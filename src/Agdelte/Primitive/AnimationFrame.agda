{-# OPTIONS --without-K --guardedness #-}

-- AnimationFrame: события анимации (60fps)

module Agdelte.Primitive.AnimationFrame where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Animation Frame Event
------------------------------------------------------------------------

postulate
  -- Событие на каждый кадр
  animationFrame : ∀ {A : Set} → A → Event A

  -- Событие с timestamp (время в ms)
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
-- Утилиты для анимации
------------------------------------------------------------------------

-- Количество кадров в секунду (приблизительно)
fps : ℕ
fps = 60

-- Интервал между кадрами в ms
frameInterval : ℕ
frameInterval = 16
