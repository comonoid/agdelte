{-# OPTIONS --without-K --guardedness #-}

-- AnimationFrame: animation events (60fps)
-- Re-exports Event constructors for convenience

module Agdelte.Primitive.AnimationFrame where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Agdelte.Core.Event public using (animationFrame; animationFrameWithTime)

------------------------------------------------------------------------
-- Animation utilities
------------------------------------------------------------------------

-- Frames per second (approximately)
fps : ℕ
fps = 60

-- Interval between frames in ms
frameInterval : ℕ
frameInterval = 16
