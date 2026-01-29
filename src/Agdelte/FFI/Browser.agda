{-# OPTIONS --without-K #-}

-- Browser FFI: JS-only postulates for DOM, Workers, Fetch, WebSocket
-- This module uses {-# COMPILE JS #-} pragmas -- only for browser builds
--
-- Note: In current Agdelte, the JS runtime (runtime/events.js, runtime/dom.js)
-- interprets Event/Cmd/Node ASTs directly via Scott encoding. These postulates
-- document the browser-specific primitives available to the runtime.
--
-- For actual browser apps, use Event/Cmd constructors (src/Agdelte/Core/Event.agda,
-- src/Agdelte/Core/Cmd.agda) which compile to Scott-encoded ASTs interpreted
-- by the runtime. Direct FFI calls are for advanced use only.

module Agdelte.FFI.Browser where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)

------------------------------------------------------------------------
-- DOM primitives (for direct FFI use, not normally needed)
------------------------------------------------------------------------

-- Opaque DOM element handle
postulate
  Element : Set

-- Query selector
postulate
  querySelector : String → Element
  -- {-# COMPILE JS querySelector = function(sel) { return document.querySelector(sel); } #-}

------------------------------------------------------------------------
-- Console
------------------------------------------------------------------------

postulate
  consoleLog   : String → Element  -- returns dummy, used for side effect
  consoleWarn  : String → Element
  consoleError : String → Element

------------------------------------------------------------------------
-- Timing (low-level, prefer Event.interval/timeout)
------------------------------------------------------------------------

-- Opaque timer handle
postulate
  TimerHandle : Set

postulate
  setTimeout    : ℕ → Element → TimerHandle
  clearTimeout  : TimerHandle → Element
  setInterval   : ℕ → Element → TimerHandle
  clearInterval : TimerHandle → Element

------------------------------------------------------------------------
-- Storage (low-level, prefer Cmd.getItem/setItem)
------------------------------------------------------------------------

postulate
  localStorageGet    : String → Maybe String
  localStorageSet    : String → String → Element
  localStorageRemove : String → Element

------------------------------------------------------------------------
-- Clipboard (low-level, prefer Cmd.writeClipboard/readClipboard)
------------------------------------------------------------------------

postulate
  clipboardWrite : String → Element
  -- clipboardRead is async, handled by Cmd

------------------------------------------------------------------------
-- URL / History (low-level, prefer Cmd.pushUrl/replaceUrl)
------------------------------------------------------------------------

postulate
  getPathname : Element  -- returns dummy; runtime reads window.location.pathname
  pushState   : String → Element
  replaceState : String → Element

------------------------------------------------------------------------
-- SharedArrayBuffer (requires COOP/COEP headers)
------------------------------------------------------------------------

-- Opaque shared buffer handle
-- At JS level this is a SharedArrayBuffer object
postulate
  SharedBuffer : Set

-- Note: SharedBuffer allocation and worker access are handled by
-- Event constructors (allocShared, workerShared) in Event.agda.
-- The runtime creates SharedArrayBuffer instances and passes them
-- to workers via postMessage with transfer.
