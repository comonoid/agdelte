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

{-# COMPILE JS allocateImage = w => h => handler => (cb) => cb.allocImage(w, h, handler) #-}

-- Allocate a generic buffer
postulate
  allocateBuffer : ∀ {Msg}
                 → ℕ              -- Size in bytes
                 → (BufferHandle → Msg)  -- Success handler
                 → Event Msg

{-# COMPILE JS allocateBuffer = size => handler => (cb) => cb.allocBuffer(size, handler) #-}

------------------------------------------------------------------------
-- Buffer operations (via Cmd)
------------------------------------------------------------------------

-- Free a buffer
postulate
  freeBuffer : ∀ {Msg} → BufferHandle → Cmd Msg

{-# COMPILE JS freeBuffer = handle => (cb) => cb.freeBuffer(handle) #-}

-- Touch a buffer (increment version, signals content changed)
-- Useful when buffer is modified directly via JS
postulate
  touchBuffer : ∀ {Msg}
              → BufferHandle
              → (BufferHandle → Msg)  -- Handler receives updated handle
              → Cmd Msg

{-# COMPILE JS touchBuffer = handle => handler => (cb) => cb.touchBuffer(handle, handler) #-}

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
