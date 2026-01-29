{-# OPTIONS --without-K --guardedness #-}

-- AnimationFrame: animation events (60fps)

module Agdelte.Primitive.AnimationFrame where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Animation Frame Event
------------------------------------------------------------------------

postulate
  -- Event on every frame
  animationFrame : ∀ {A : Set} → A → Event A

  -- Event with timestamp (time in ms)
  animationFrameWithTime : ∀ {A : Set} → (Float → A) → Event A

{-# COMPILE JS animationFrame = _ => msg => ({
  type: 'animationFrame',
  config: { msg },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS animationFrameWithTime = _ => handler => ({
  type: 'animationFrame',
  config: { msg: handler },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Animation utilities
------------------------------------------------------------------------

-- Frames per second (approximately)
fps : ℕ
fps = 60

-- Interval between frames in ms
frameInterval : ℕ
frameInterval = 16
