{-# OPTIONS --without-K --guardedness #-}

-- File system operations via Haskell FFI (MAlonzo only).

module Agdelte.FFI.FileSystem where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)

{-# FOREIGN GHC
  import qualified Data.Text    as T
  import qualified Data.Text.IO as TIO
  import System.Directory (doesFileExist, createDirectoryIfMissing, renameFile)
  import Control.Exception (try, SomeException)
  #-}

------------------------------------------------------------------------
-- Read / Write / Append
------------------------------------------------------------------------

postulate
  readFileText  : String → IO String
  writeFileText : String → String → IO ⊤
  appendFileText : String → String → IO ⊤

{-# COMPILE GHC readFileText  = TIO.readFile  . T.unpack #-}
{-# COMPILE GHC writeFileText = \p c -> TIO.writeFile  (T.unpack p) c #-}
{-# COMPILE GHC appendFileText = \p c -> TIO.appendFile (T.unpack p) c #-}

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
-- Atomic rename
------------------------------------------------------------------------

postulate
  renameFile : String → String → IO ⊤

{-# COMPILE GHC renameFile = \src dst -> renameFile (T.unpack src) (T.unpack dst) #-}

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
