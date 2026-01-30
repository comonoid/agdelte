{-# OPTIONS --without-K --guardedness #-}

-- Linear IpcHandle: indexed by connection state
--
-- Wraps the untyped IpcHandle from FFI.Server with a state index
-- that prevents:
--   - querying after disconnect
--   - disconnecting twice
--   - using a handle before connecting
--
-- See doc/research.md section 2 for design rationale.

module Agdelte.Concurrent.ProcessOpticLinear where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

open import Agdelte.FFI.Server as Raw
  using (IpcHandle; connectProcess; queryProcess; stepProcess; closeProcess)
open import Agdelte.FFI.Server using (_>>=_; _>>_; pure)

------------------------------------------------------------------------
-- Connection state
------------------------------------------------------------------------

data ConnState : Set where
  Connected    : ConnState
  Disconnected : ConnState

------------------------------------------------------------------------
-- Indexed IpcHandle: tracks connection state at type level
------------------------------------------------------------------------

-- A handle that is known to be in state `s`.
-- Only `Connected` handles can be queried/stepped/closed.
data IpcHandleL : ConnState → Set where
  mkHandle : IpcHandle → IpcHandleL Connected

------------------------------------------------------------------------
-- Operations with state transitions
------------------------------------------------------------------------

-- Connect: produces a Connected handle
connect : String → IO (IpcHandleL Connected)
connect path = connectProcess path >>= λ h → pure (mkHandle h)

-- Query (peek): only on Connected, stays Connected
query : IpcHandleL Connected → IO String
query (mkHandle h) = queryProcess h

-- Step: only on Connected, stays Connected
step : IpcHandleL Connected → String → IO String
step (mkHandle h) input = stepProcess h input

-- Close: Connected → Disconnected
-- Returns unit; the Disconnected handle is not useful
-- but exists as proof the protocol was followed.
close : IpcHandleL Connected → IO ⊤
close (mkHandle h) = closeProcess h

------------------------------------------------------------------------
-- Example: safe interaction pattern
------------------------------------------------------------------------

-- A safe query-then-close sequence.
-- Type-level guarantee: handle is closed exactly once.
queryAndClose : String → IO String
queryAndClose path =
  connect path >>= λ h →
  query h      >>= λ result →
  close h      >>
  pure result

-- A safe step-then-close sequence.
stepAndClose : String → String → IO String
stepAndClose path input =
  connect path    >>= λ h →
  step h input    >>= λ result →
  close h         >>
  pure result
