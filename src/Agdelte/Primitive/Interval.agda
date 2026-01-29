{-# OPTIONS --without-K --guardedness #-}

-- Interval: periodic events

module Agdelte.Primitive.Interval where

open import Data.Nat using (ℕ)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Interval Event
------------------------------------------------------------------------

postulate
  -- Event every n milliseconds
  interval : ∀ {A : Set} → ℕ → A → Event A

  -- Single event after n milliseconds
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
-- Convenient wrappers
------------------------------------------------------------------------

-- Every second
everySecond : ∀ {A : Set} → A → Event A
everySecond = interval 1000

-- Every minute
everyMinute : ∀ {A : Set} → A → Event A
everyMinute = interval 60000

-- Every n seconds
everyNSeconds : ∀ {A : Set} → ℕ → A → Event A
everyNSeconds n = interval (n * 1000)
  where open import Data.Nat using (_*_)
