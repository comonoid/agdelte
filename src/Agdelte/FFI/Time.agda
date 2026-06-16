{-# OPTIONS --without-K --guardedness #-}

-- Time utilities (GHC backend).

module Agdelte.FFI.Time where

open import Agda.Builtin.IO using (IO)
open import Data.Nat using (ℕ)

-- | Get current unix timestamp in seconds.
postulate
  getCurrentTime : IO ℕ

-- NB: the body is inlined into the COMPILE pragma (not a FOREIGN def) so the
-- FOREIGN block is import-only — a trailing def in a FOREIGN block strands
-- MAlonzo's auto `import Data.Text` after it → GHC parse error.
{-# FOREIGN GHC import qualified Data.Time.Clock.POSIX as POSIX #-}
{-# COMPILE GHC getCurrentTime = (fmap round POSIX.getPOSIXTime :: IO Integer) #-}
