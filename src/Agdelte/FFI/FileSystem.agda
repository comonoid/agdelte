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
  import System.IO (withFile, hFlush, IOMode(WriteMode, AppendMode))
  import System.Directory (doesFileExist, createDirectoryIfMissing, renameFile, canonicalizePath, listDirectory)
  import qualified System.FilePath as FP
  import System.Posix.IO (handleToFd, closeFd, openFd, OpenMode(ReadOnly), defaultFileFlags)
  import System.Posix.Unistd (fileSynchronise)
  import Data.List (isPrefixOf, sort)
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

{-# FOREIGN GHC
  readFileSafeImpl :: T.Text -> IO T.Text
  readFileSafeImpl path = do
    result <- try (TIO.readFile (T.unpack path)) :: IO (Either SomeException T.Text)
    case result of
      Right content -> return content
      Left _        -> return T.empty
  #-}
{-# COMPILE GHC readFileSafe = readFileSafeImpl #-}

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
