{-# OPTIONS --without-K #-}

-- Buffer Registry API
--
-- Provides lightweight handles to large binary buffers managed by the runtime.
-- Model stores only metadata (id, version, dimensions), actual buffer data
-- lives in the JS BufferRegistry.

module Agdelte.Buffer where

open import Data.Nat using (ℕ; _*_; _≡ᵇ_)
open import Data.Bool using (Bool; not)
open import Data.String using (String)

open import Agdelte.Core.Event using (Event)
open import Agdelte.Core.Cmd using (Cmd)

------------------------------------------------------------------------
-- Buffer Handle
------------------------------------------------------------------------

-- A lightweight reference to a buffer in the registry
-- The model stores this; actual buffer data is in JS
record BufferHandle : Set where
  constructor bufferHandle
  field
    bufferId      : ℕ    -- Registry handle id
    bufferVersion : ℕ    -- Version (incremented when buffer changes)
    bufferWidth   : ℕ    -- Width (for images)
    bufferHeight  : ℕ    -- Height (for images)

------------------------------------------------------------------------
-- Buffer allocation (via Event)
------------------------------------------------------------------------

-- Allocate an image buffer (RGBA, 4 bytes per pixel)
-- Returns a BufferHandle when allocation succeeds
postulate
  allocateImage : ∀ {Msg}
                → ℕ              -- Width
                → ℕ              -- Height
                → (BufferHandle → Msg)  -- Success handler
                → Event Msg

-- NOTE: allocateImage needs runtime support (custom Event constructor).
-- The previous callback-style pragma was incompatible with Scott-encoded Event.
-- Using timeout 0 as a placeholder until a proper Event constructor is added.
{-# COMPILE JS allocateImage = function(w) { return function(h) { return function(handler) {
  return (cases) => cases["timeout"](0n, handler({
    bufferHandle: (cb) => cb["bufferHandle"](0n, 0n, w, h)
  }));
}; }; } #-}

-- Allocate a generic buffer
postulate
  allocateBuffer : ∀ {Msg}
                 → ℕ              -- Size in bytes
                 → (BufferHandle → Msg)  -- Success handler
                 → Event Msg

-- NOTE: Same issue as allocateImage — needs proper Event constructor.
{-# COMPILE JS allocateBuffer = function(size) { return function(handler) {
  return (cases) => cases["timeout"](0n, handler({
    bufferHandle: (cb) => cb["bufferHandle"](0n, 0n, size, 1n)
  }));
}; } #-}

------------------------------------------------------------------------
-- Buffer operations (via Cmd)
------------------------------------------------------------------------

-- Free a buffer
postulate
  freeBuffer : ∀ {Msg} → BufferHandle → Cmd Msg

-- NOTE: freeBuffer needs runtime support (custom Cmd constructor).
-- Using ε (no-op) as placeholder until a proper Cmd constructor is added.
{-# COMPILE JS freeBuffer = function(handle) {
  return (cases) => cases["ε"]();
} #-}

-- Touch a buffer (increment version, signals content changed)
-- Useful when buffer is modified directly via JS
postulate
  touchBuffer : ∀ {Msg}
              → BufferHandle
              → (BufferHandle → Msg)  -- Handler receives updated handle
              → Cmd Msg

-- NOTE: touchBuffer needs runtime support (custom Cmd constructor).
-- Using ε (no-op) as placeholder.
{-# COMPILE JS touchBuffer = function(handle) { return function(handler) {
  return (cases) => cases["ε"]();
}; } #-}

------------------------------------------------------------------------
-- Buffer predicates
------------------------------------------------------------------------

-- Check if buffer version changed (for reactive updates)
bufferChanged : BufferHandle → BufferHandle → Bool
bufferChanged old new =
  not (BufferHandle.bufferVersion old ≡ᵇ BufferHandle.bufferVersion new)

-- Get buffer size in bytes
bufferSize : BufferHandle → ℕ
bufferSize h = BufferHandle.bufferWidth h * BufferHandle.bufferHeight h * 4

------------------------------------------------------------------------
-- Re-exports
------------------------------------------------------------------------

open BufferHandle public
