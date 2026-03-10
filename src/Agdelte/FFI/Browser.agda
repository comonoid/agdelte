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
--
-- Purity note: these postulates are declared as pure functions (e.g.
-- consoleLog : String → ⊤) even though they perform side effects.
-- Agda's type system permits the compiler to CSE, reorder, or eliminate
-- pure calls, but the JS backend currently does not optimise, so this is
-- safe in practice. The primary API (Event/Cmd AST) is already pure and
-- safe; these exist only as low-level escape hatches.

module Agdelte.FFI.Browser where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)
open import Agda.Builtin.Unit using (⊤)

------------------------------------------------------------------------
-- DOM primitives (for direct FFI use, not normally needed)
------------------------------------------------------------------------

-- Opaque DOM element handle
postulate
  Element : Set

{-# COMPILE JS Element = function(x) { return x; } #-}

-- Query selector
postulate
  querySelector : String → Maybe Element

-- FFI-FRAGILE: just (Maybe), nothing (Maybe)
{-# COMPILE JS querySelector = function(sel) {
  const el = document.querySelector(sel);
  return el ? (cases) => cases.just(el) : (cases) => cases.nothing();
} #-}

------------------------------------------------------------------------
-- Console
------------------------------------------------------------------------

postulate
  consoleLog   : String → ⊤
  consoleWarn  : String → ⊤
  consoleError : String → ⊤

{-# COMPILE JS consoleLog = function(s) { console.log(s); return null; } #-}
{-# COMPILE JS consoleWarn = function(s) { console.warn(s); return null; } #-}
{-# COMPILE JS consoleError = function(s) { console.error(s); return null; } #-}

------------------------------------------------------------------------
-- Timing (low-level, prefer Event.interval/timeout)
------------------------------------------------------------------------

-- Opaque timer handle
postulate
  TimerHandle : Set

{-# COMPILE JS TimerHandle = function(x) { return x; } #-}

postulate
  setTimeout    : ℕ → (⊤ → ⊤) → TimerHandle
  clearTimeout  : TimerHandle → ⊤
  setInterval   : ℕ → (⊤ → ⊤) → TimerHandle
  clearInterval : TimerHandle → ⊤

{-# COMPILE JS setTimeout = function(ms) { return function(cb) {
  return window.setTimeout(cb, Number(ms));
}; } #-}
{-# COMPILE JS clearTimeout = function(h) {
  window.clearTimeout(h); return null;
} #-}
{-# COMPILE JS setInterval = function(ms) { return function(cb) {
  return window.setInterval(cb, Number(ms));
}; } #-}
{-# COMPILE JS clearInterval = function(h) {
  window.clearInterval(h); return null;
} #-}

------------------------------------------------------------------------
-- Storage (low-level, prefer Cmd.getItem/setItem)
------------------------------------------------------------------------

postulate
  localStorageGet    : String → Maybe String
  localStorageSet    : String → String → ⊤
  localStorageRemove : String → ⊤

-- FFI-FRAGILE: just (Maybe), nothing (Maybe)
{-# COMPILE JS localStorageGet = function(key) {
  try {
    const val = localStorage.getItem(key);
    return val !== null ? (cases) => cases.just(val) : (cases) => cases.nothing();
  } catch(e) { return (cases) => cases.nothing(); }
} #-}
{-# COMPILE JS localStorageSet = function(key) { return function(val) {
  try { localStorage.setItem(key, val); } catch(e) {}
  return null;
}; } #-}
{-# COMPILE JS localStorageRemove = function(key) {
  try { localStorage.removeItem(key); } catch(e) {}
  return null;
} #-}

------------------------------------------------------------------------
-- Clipboard (low-level, prefer Cmd.writeClipboard/readClipboard)
------------------------------------------------------------------------

postulate
  clipboardWrite : String → ⊤
  -- clipboardRead is async, handled by Cmd

{-# COMPILE JS clipboardWrite = function(text) {
  navigator.clipboard.writeText(text).catch(() => {});
  return null;
} #-}

------------------------------------------------------------------------
-- URL / History (low-level, prefer Cmd.pushUrl/replaceUrl)
------------------------------------------------------------------------

postulate
  pushState    : String → ⊤
  replaceState : String → ⊤

{-# COMPILE JS pushState = function(url) {
  window.history.pushState(null, '', url); return null;
} #-}
{-# COMPILE JS replaceState = function(url) {
  window.history.replaceState(null, '', url); return null;
} #-}

------------------------------------------------------------------------
-- SharedArrayBuffer (requires COOP/COEP headers)
------------------------------------------------------------------------

-- Re-exported from FFI.Shared for convenience
open import Agdelte.FFI.Shared using (SharedBuffer) public

-- Note: SharedBuffer allocation and worker access are handled by
-- Event constructors (allocShared, workerShared) in Event.agda.
-- The runtime creates SharedArrayBuffer instances and passes them
-- to workers via postMessage with transfer.
