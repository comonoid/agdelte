{-# OPTIONS --without-K --guardedness #-}

-- Interval: периодические события

module Agdelte.Primitive.Interval where

open import Data.Nat using (ℕ)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Interval Event
------------------------------------------------------------------------

postulate
  -- Событие каждые n миллисекунд
  interval : ∀ {A : Set} → ℕ → A → Event A

  -- Однократное событие через n миллисекунд
  timeout : ∀ {A : Set} → ℕ → A → Event A

{-# COMPILE JS interval = _ => ms => msg => ({
  type: 'interval',
  config: { ms, msg },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS timeout = _ => ms => msg => ({
  type: 'timeout',
  config: { ms, msg },
  now: [],
  get next() { return { now: [], get next() { return this; } }; }
}) #-}

------------------------------------------------------------------------
-- Удобные обёртки
------------------------------------------------------------------------

-- Каждую секунду
everySecond : ∀ {A : Set} → A → Event A
everySecond = interval 1000

-- Каждую минуту
everyMinute : ∀ {A : Set} → A → Event A
everyMinute = interval 60000

-- Каждые n секунд
everyNSeconds : ∀ {A : Set} → ℕ → A → Event A
everyNSeconds n = interval (n * 1000)
  where open import Data.Nat using (_*_)
