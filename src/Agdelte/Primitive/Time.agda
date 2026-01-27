{-# OPTIONS --without-K --guardedness #-}

-- Time: события времени

module Agdelte.Primitive.Time where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.String using (String)
open import Agdelte.Core.Event
open import Agdelte.Core.Signal

------------------------------------------------------------------------
-- Time Types
------------------------------------------------------------------------

-- Время в миллисекундах (с эпохи Unix)
Time : Set
Time = ℕ

-- Timestamp (высокоточный)
Timestamp : Set
Timestamp = Float

------------------------------------------------------------------------
-- Time Events
------------------------------------------------------------------------

postulate
  -- Текущее время (один раз при подписке)
  currentTime : ∀ {A : Set} → (Time → A) → Event A

  -- Периодическое время
  every : ∀ {A : Set} → ℕ → (Time → A) → Event A

  -- Высокоточное время (performance.now)
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
-- Удобные обёртки
------------------------------------------------------------------------

-- Текущее время как сигнал (обновляется каждую секунду)
timePerSecond : ∀ {A : Set} → (Time → A) → Event A
timePerSecond = every 1000

-- Каждый тик (16ms ≈ 60fps)
everyTick : ∀ {A : Set} → (Time → A) → Event A
everyTick = every 16

-- Каждые n миллисекунд
everyMs : ∀ {A : Set} → ℕ → (Time → A) → Event A
everyMs = every

------------------------------------------------------------------------
-- Форматирование времени (через FFI)
------------------------------------------------------------------------

postulate
  -- Форматирование времени в строку
  formatTime : Time → String

  -- Парсинг времени из строки
  parseTime : String → Time

{-# COMPILE JS formatTime = t => new Date(t).toISOString() #-}
{-# COMPILE JS parseTime = s => Date.parse(s) #-}

------------------------------------------------------------------------
-- Таймеры
------------------------------------------------------------------------

-- Задержка выполнения
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

-- Debounce: событие после паузы
postulate
  debounce : ∀ {A : Set} → ℕ → Event A → Event A

-- Throttle: не чаще чем раз в n ms
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
