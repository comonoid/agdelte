{-# OPTIONS --without-K --guardedness #-}

-- Time utilities (GHC backend).

module Agdelte.FFI.Time where

open import Agda.Builtin.IO using (IO)
open import Data.Nat using (ℕ)

-- | Get current unix timestamp in seconds.
postulate
  getCurrentTime : IO ℕ

{-# FOREIGN GHC
  import Data.Time.Clock.POSIX (getPOSIXTime)

  getCurrentTimeHS :: IO Integer
  getCurrentTimeHS = round <$> getPOSIXTime
  #-}
{-# COMPILE GHC getCurrentTime = getCurrentTimeHS #-}
