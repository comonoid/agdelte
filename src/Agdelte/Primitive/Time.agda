{-# OPTIONS --without-K --guardedness #-}

-- Time: time events

module Agdelte.Primitive.Time where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.String using (String)
open import Agdelte.Core.Event
open import Agdelte.Core.Signal

------------------------------------------------------------------------
-- Time Types
------------------------------------------------------------------------

-- Time in milliseconds (since Unix epoch)
Time : Set
Time = ℕ

-- Timestamp (high precision)
Timestamp : Set
Timestamp = Float

------------------------------------------------------------------------
-- Time Events
------------------------------------------------------------------------

postulate
  -- Current time (once on subscription)
  currentTime : ∀ {A : Set} → (Time → A) → Event A

  -- Periodic time
  every : ∀ {A : Set} → ℕ → (Time → A) → Event A

  -- High precision time (performance.now)
  performanceNow : ∀ {A : Set} → (Timestamp → A) → Event A

{-# COMPILE JS currentTime = _ => handler => ({
  type: 'immediate',
  config: { handler: () => handler(Date.now()) },
  now: [handler(Date.now())],
  get next() { return { now: [], get next() { return this; } }; }
}) #-}

{-# COMPILE JS every = _ => ms => handler => ({
  type: 'interval',
  config: { ms, msg: null },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS performanceNow = _ => handler => ({
  type: 'immediate',
  config: { handler: () => handler(performance.now()) },
  now: [handler(performance.now())],
  get next() { return { now: [], get next() { return this; } }; }
}) #-}

------------------------------------------------------------------------
-- Convenient wrappers
------------------------------------------------------------------------

-- Current time as signal (updates every second)
timePerSecond : ∀ {A : Set} → (Time → A) → Event A
timePerSecond = every 1000

-- Every tick (16ms ≈ 60fps)
everyTick : ∀ {A : Set} → (Time → A) → Event A
everyTick = every 16

-- Every n milliseconds
everyMs : ∀ {A : Set} → ℕ → (Time → A) → Event A
everyMs = every

------------------------------------------------------------------------
-- Time formatting (via FFI)
------------------------------------------------------------------------

postulate
  -- Format time to string
  formatTime : Time → String

  -- Parse time from string
  parseTime : String → Time

{-# COMPILE JS formatTime = t => new Date(t).toISOString() #-}
{-# COMPILE JS parseTime = s => Date.parse(s) #-}

------------------------------------------------------------------------
-- Timers
------------------------------------------------------------------------

-- Delayed execution
postulate
  timeout : ∀ {A : Set} → ℕ → A → Event A

{-# COMPILE JS timeout = _ => ms => msg => ({
  type: 'timeout',
  config: { ms, msg },
  now: [],
  get next() {
    return { now: [], get next() { return this; } };
  }
}) #-}

-- Debounce: event after pause
postulate
  debounce : ∀ {A : Set} → ℕ → Event A → Event A

-- Throttle: no more often than once per n ms
postulate
  throttle : ∀ {A : Set} → ℕ → Event A → Event A

{-# COMPILE JS debounce = _ => ms => event => ({
  ...event,
  debounce: ms
}) #-}

{-# COMPILE JS throttle = _ => ms => event => ({
  ...event,
  throttle: ms
}) #-}
