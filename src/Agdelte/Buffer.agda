{-# OPTIONS --without-K #-}

-- Buffer Registry API
--
-- Provides lightweight handles to large binary buffers managed by the runtime.
-- Model stores only metadata (id, version, dimensions), actual buffer data
-- lives in the JS BufferRegistry.

module Agdelte.Buffer where

open import Data.Nat using (ℕ; _*_; _≡ᵇ_)
open import Data.Bool using (Bool; not; _∧_)
open import Data.String using (String)

open import Agdelte.Core.Event using (Event; allocImage; allocBuffer)
open import Agdelte.Core.Cmd using (Cmd; freeBuffer; touchBuffer)

------------------------------------------------------------------------
-- Re-export BufferHandle from Event
------------------------------------------------------------------------

open import Agdelte.Core.Event using (BufferHandle; bufferHandle;
  bufferId; bufferVersion; bufferWidth; bufferHeight) public

------------------------------------------------------------------------
-- Buffer allocation (via Event)
------------------------------------------------------------------------

-- Allocate an image buffer (RGBA, 4 bytes per pixel)
-- Returns a BufferHandle when allocation succeeds
allocateImage : ∀ {Msg}
              → ℕ              -- Width
              → ℕ              -- Height
              → (BufferHandle → Msg)  -- Success handler
              → Event Msg
allocateImage = allocImage

-- Allocate a generic buffer
allocateBuffer : ∀ {Msg}
               → ℕ              -- Size in bytes
               → (BufferHandle → Msg)  -- Success handler
               → Event Msg
allocateBuffer = allocBuffer

------------------------------------------------------------------------
-- Buffer operations (via Cmd)
------------------------------------------------------------------------

-- Free a buffer
freeBufferCmd : ∀ {Msg} → BufferHandle → Cmd Msg
freeBufferCmd = freeBuffer

-- Touch a buffer (increment version, signals content changed)
-- Useful when buffer is modified directly via JS
touchBufferCmd : ∀ {Msg}
              → BufferHandle
              → (BufferHandle → Msg)  -- Handler receives updated handle
              → Cmd Msg
touchBufferCmd = touchBuffer

------------------------------------------------------------------------
-- Buffer predicates
------------------------------------------------------------------------

-- Check if buffer content changed (for reactive updates)
-- Compares both buffer ID (same buffer) and version strictly increased
bufferChanged : BufferHandle → BufferHandle → Bool
bufferChanged old new =
  (bufferId old ≡ᵇ bufferId new) ∧ (bufferVersion old <ᵇ bufferVersion new)
  where open import Data.Nat using (_<ᵇ_)

-- Get image buffer size in bytes (RGBA, 4 bytes per pixel)
imageBufferSize : BufferHandle → ℕ
imageBufferSize h = bufferWidth h * bufferHeight h * 4

-- Get generic buffer size in bytes
-- For allocateBuffer(n), runtime sets width=n, height=1
bufferSize : BufferHandle → ℕ
bufferSize h = bufferWidth h * bufferHeight h

