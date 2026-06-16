{-# OPTIONS --without-K --guardedness #-}

-- File system operations via Haskell FFI (MAlonzo only).

module Agdelte.FFI.FileSystem where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List)
open import Data.Maybe using (Maybe)

{-# FOREIGN GHC
  import qualified Data.Text    as T
  import qualified Data.Text.IO as TIO
  import qualified Data.ByteString as BS
  import qualified Data.ByteString.Char8 as BC
  import Data.Text.Encoding (decodeUtf8With, encodeUtf8)
  import Data.Text.Encoding.Error (lenientDecode)
  import System.IO (withFile, withBinaryFile, hFlush, IOMode(WriteMode, AppendMode))
  import System.Directory (doesFileExist, createDirectoryIfMissing, renameFile, canonicalizePath, listDirectory)
  import qualified System.FilePath as FP
  import System.Posix.IO (handleToFd, closeFd, openFd, OpenMode(ReadOnly), defaultFileFlags)
  import System.Posix.Unistd (fileSynchronise)
  import Data.List (isPrefixOf, sort, foldl')
  import Data.Word (Word8, Word32)
  import Data.Bits (xor, shiftR, (.&.))
  import Control.Monad (when)
  import Control.Exception (try, SomeException)

  -- fsync the directory CONTAINING the given path, so a rename/create within
  -- it survives power loss (an fsync of a file persists its data, but not the
  -- directory entry — the rename can still be lost on crash without this).
  syncPathDirHS :: T.Text -> IO ()
  syncPathDirHS path = do
    let raw = FP.takeDirectory (T.unpack path)
        dir = if null raw then "." else raw
    r <- try (do
      fd <- openFd dir ReadOnly defaultFileFlags
      fileSynchronise fd
      closeFd fd) :: IO (Either SomeException ())
    either (const (return ())) return r

  -- Durable write: write, flush to the OS, then fsync to stable storage
  -- before returning. Without the fsync an acknowledged WAL append can be
  -- lost in the OS page cache on power loss, breaking durability.
  -- handleToFd detaches+flushes the Handle (it must not be reused after),
  -- so we close the Fd ourselves.
  durableWriteHS :: IOMode -> T.Text -> T.Text -> IO ()
  durableWriteHS mode path content =
    -- withFile guarantees the handle is closed even if hPutStr/hFlush throws
    -- (no FD leak). handleToFd detaches+closes the Handle, so withFile's final
    -- hClose is a harmless no-op; we close the raw Fd ourselves after fsync.
    withFile (T.unpack path) mode $ \h -> do
      TIO.hPutStr h content
      hFlush h
      fd <- handleToFd h
      fileSynchronise fd
      closeFd fd

  -- WAL records are framed at the BYTE level, not the character level: durability
  -- tearing happens on byte boundaries, and lenient UTF-8 decode is NOT length-
  -- preserving (a torn multi-byte char → one+ U+FFFD), so a char-length prefix
  -- can mis-frame a torn tail. Byte-length framing is exact: a torn tail always
  -- has fewer bytes than its declared length → dropped.
  --
  -- Record = `<payloadByteLen>:<crc32>:<payload-utf8>` (lengths/crc in ASCII
  -- decimal). The CRC32 over the payload distinguishes a CORRUPT committed record
  -- (full bytes present, crc mismatch → refuse to start) from a TORN TAIL (payload
  -- shorter than declared → drop). Without it, a bit-rotted length digit on a
  -- mid-stream record impersonated a torn tail and silently truncated the log (M5).

  -- pure CRC32 (poly 0xEDB88320), bit-by-bit (no table/dep); fine at recovery time.
  walCrcStep :: Word32 -> Word8 -> Word32
  walCrcStep crc byte = go (8 :: Int) (crc `xor` fromIntegral byte)
    where go 0 c = c
          go k c = go (k - 1) (if c .&. 1 /= 0 then (c `shiftR` 1) `xor` 0xEDB88320 else c `shiftR` 1)
  walCrc32 :: BS.ByteString -> Word32
  walCrc32 bs = 0xFFFFFFFF `xor` BS.foldl' walCrcStep 0xFFFFFFFF bs

  -- Durably append one CRC-framed record + fsync. On first create also fsync the
  -- parent directory, so the new file's directory entry survives power loss.
  appendWalRecordHS :: T.Text -> T.Text -> IO ()
  appendWalRecordHS path payload = do
    let pbytes = encodeUtf8 payload
        rec    = BC.pack (show (BS.length pbytes) ++ ":" ++ show (walCrc32 pbytes) ++ ":") <> pbytes
    existed <- doesFileExist (T.unpack path)
    withBinaryFile (T.unpack path) AppendMode $ \h -> do
      BS.hPut h rec
      hFlush h
      fd <- handleToFd h
      fileSynchronise fd
      closeFd fd
    when (not existed) (syncPathDirHS path)

  walIsDigit :: Word8 -> Bool
  walIsDigit w = w >= 48 && w <= 57

  -- decimal digit run → Integer (no Int overflow, L8)
  walDigitsToInteger :: BS.ByteString -> Integer
  walDigitsToInteger = BS.foldl' (\a w -> a * 10 + toInteger (w - 48)) 0

  -- Read the WAL as bytes and split into complete records at byte granularity.
  --   Just records — every COMPLETE, CRC-valid record's payload (decoded), torn tail dropped;
  --   Nothing       — corruption: bad header, an over-long digit run (>18, L8), or a
  --                   CRC mismatch on a fully-present record (M5) → caller refuses to start.
  -- Missing / unreadable file → Just [] (empty log).
  readWalRecordsHS :: T.Text -> IO (Maybe [T.Text])
  readWalRecordsHS path = do
    r <- try (BS.readFile (T.unpack path)) :: IO (Either SomeException BS.ByteString)
    pure $ case r of
      Left _   -> Just []
      Right bs -> walGo bs []
    where
      walGo bs acc
        | BS.null bs = Just (reverse acc)                          -- clean end
        | otherwise =
            case BS.elemIndex 0x3a bs of                           -- 1st ':'
              Nothing -> if BS.all walIsDigit bs then Just (reverse acc) else Nothing
              Just i  ->
                let lenD    = BS.take i bs
                    afterL  = BS.drop (i + 1) bs
                in if BS.null lenD || not (BS.all walIsDigit lenD) || BS.length lenD > 18
                   then Nothing                                    -- bad / absurd length header
                   else case BS.elemIndex 0x3a afterL of           -- 2nd ':'
                          Nothing -> if BS.all walIsDigit afterL then Just (reverse acc) else Nothing
                          Just j  ->
                            let crcD = BS.take j afterL
                                rest = BS.drop (j + 1) afterL
                                n    = fromInteger (walDigitsToInteger lenD) :: Int
                            in if BS.null crcD || not (BS.all walIsDigit crcD) || BS.length crcD > 10
                               then Nothing                        -- bad crc header
                               else if BS.length rest < n
                                    then Just (reverse acc)        -- payload incomplete → torn tail
                                    else let payload = BS.take n rest
                                             more    = BS.drop n rest
                                         in if toInteger (walCrc32 payload) == walDigitsToInteger crcD
                                            then walGo more (decodeUtf8With lenientDecode payload : acc)
                                            else Nothing            -- CRC mismatch → corruption → die
  #-}

------------------------------------------------------------------------
-- Read / Write / Append
--
-- Note: Data.Text.IO.readFile is strict (it reads and decodes the whole
-- file before returning), so `try` around it does catch read/decode errors.
-- Writes are durable (fsync) — see durableWriteHS.
------------------------------------------------------------------------

postulate
  readFileText  : String → IO String
  writeFileText : String → String → IO ⊤
  appendFileText : String → String → IO ⊤

{-# COMPILE GHC readFileText  = TIO.readFile  . T.unpack #-}
{-# COMPILE GHC writeFileText = durableWriteHS WriteMode #-}
{-# COMPILE GHC appendFileText = durableWriteHS AppendMode #-}

------------------------------------------------------------------------
-- Existence check
------------------------------------------------------------------------

postulate
  doesFileExist' : String → IO Bool

{-# COMPILE GHC doesFileExist' = doesFileExist . T.unpack #-}

------------------------------------------------------------------------
-- Directory creation
------------------------------------------------------------------------

postulate
  mkdirp : String → IO ⊤

{-# COMPILE GHC mkdirp = createDirectoryIfMissing True . T.unpack #-}

------------------------------------------------------------------------
-- Directory listing (entries only, names not paths), sorted ascending so
-- ordered conventions like NNNN_*.sql apply deterministically.
------------------------------------------------------------------------

postulate
  listDirectory : String → IO (List String)

{-# FOREIGN GHC
  listDirSortedHS :: T.Text -> IO [T.Text]
  listDirSortedHS path = do
    entries <- listDirectory (T.unpack path)
    pure (sort (map T.pack entries))
  #-}
{-# COMPILE GHC listDirectory = listDirSortedHS #-}

------------------------------------------------------------------------
-- Atomic rename
------------------------------------------------------------------------

postulate
  renameFile : String → String → IO ⊤
  -- fsync the directory containing the given file path. Call AFTER renameFile
  -- to make an atomic snapshot replace crash-durable (rename then dir-fsync).
  syncPathDir : String → IO ⊤

{-# COMPILE GHC renameFile = \src dst -> renameFile (T.unpack src) (T.unpack dst) #-}
{-# COMPILE GHC syncPathDir = syncPathDirHS #-}

------------------------------------------------------------------------
-- Safe read (returns "" if file doesn't exist)
------------------------------------------------------------------------

postulate
  readFileSafe : String → IO String
  -- Durably append one BYTE-length-framed WAL record (+ fsync, + dir fsync on
  -- create). Payload may contain any text (newlines, ':', multi-byte) — framing
  -- is by byte length, so it is unambiguous.
  appendWalRecord : String → String → IO ⊤
  -- Read the WAL as byte-framed records: just (complete record payloads, torn
  -- tail dropped) | nothing (mid-stream corruption → caller must refuse to start).
  readWalRecords : String → IO (Maybe (List String))

{-# FOREIGN GHC
  readFileSafeImpl :: T.Text -> IO T.Text
  readFileSafeImpl path = do
    result <- try (TIO.readFile (T.unpack path)) :: IO (Either SomeException T.Text)
    case result of
      Right content -> return content
      Left _        -> return T.empty
  #-}
{-# COMPILE GHC readFileSafe    = readFileSafeImpl   #-}
{-# COMPILE GHC appendWalRecord = appendWalRecordHS  #-}
{-# COMPILE GHC readWalRecords  = readWalRecordsHS   #-}

------------------------------------------------------------------------
-- Confined read / write — for paths derived from untrusted input.
--
-- The raw functions above must NEVER be given a request-derived path: they
-- do no normalization, so "../../etc/passwd" escapes any intended directory.
-- These helpers canonicalize (root </> relPath) and reject the operation if
-- the result escapes `root` (via .. or a symlink). Returns nothing/false on
-- traversal attempt or IO error.
------------------------------------------------------------------------

postulate
  -- root → relPath → contents (nothing if outside root or unreadable)
  readFileConfined  : String → String → IO (Maybe String)
  -- root → relPath → content → success?
  writeFileConfined : String → String → String → IO Bool

{-# FOREIGN GHC
  -- Resolve root </> rel, return it only if it stays within (canonical) root.
  confinedPathHS :: T.Text -> T.Text -> IO (Maybe FilePath)
  confinedPathHS root rel = do
    r <- try (do
      rootC <- canonicalizePath (T.unpack root)
      cand  <- canonicalizePath (T.unpack root FP.</> T.unpack rel)
      pure (rootC, cand)) :: IO (Either SomeException (FilePath, FilePath))
    case r of
      Left _ -> pure Nothing
      Right (rootC, cand)
        | (rootC ++ "/") `isPrefixOf` (cand ++ "/") -> pure (Just cand)
        | otherwise                                  -> pure Nothing

  readFileConfinedHS :: T.Text -> T.Text -> IO (Maybe T.Text)
  readFileConfinedHS root rel = do
    mp <- confinedPathHS root rel
    case mp of
      Nothing -> pure Nothing
      Just p  -> do
        r <- try (TIO.readFile p) :: IO (Either SomeException T.Text)
        case r of
          Right c -> pure (Just c)
          Left _  -> pure Nothing

  writeFileConfinedHS :: T.Text -> T.Text -> T.Text -> IO Bool
  writeFileConfinedHS root rel content = do
    mp <- confinedPathHS root rel
    case mp of
      Nothing -> pure False
      Just p  -> do
        r <- try (durableWriteHS WriteMode (T.pack p) content)
               :: IO (Either SomeException ())
        case r of
          Right _ -> pure True
          Left _  -> pure False
  #-}
{-# COMPILE GHC readFileConfined  = readFileConfinedHS  #-}
{-# COMPILE GHC writeFileConfined = writeFileConfinedHS #-}
