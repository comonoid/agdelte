{-# OPTIONS --without-K --guardedness #-}

-- Big Lens — Network-Wide Optic
--
-- Extends the Optic abstraction to span:
--   LocalOptic   — pure peek/over (Optic.agda)
--   AgentOptic   — HTTP GET/POST to server agents
--   ClientOptic  — WebSocket peek/over to browser clients
--   ProcessOptic — Unix socket (ProcessOptic.agda)
--
-- Key idea: IOOptic is the effectful counterpart of Optic.
-- Same peek/over interface, but in IO and string-serialized.
--
-- Transport is encoded in the interpretation, not in the lens itself.

module Agdelte.Reactive.BigLens where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.FFI.Server using (_>>=_; _>>_; pure; bracket)

------------------------------------------------------------------------
-- IOOptic: effectful optic over a transport
------------------------------------------------------------------------

-- Unlike pure Optic (peek : S → Maybe A, over : (A → A) → S → S),
-- IOOptic works over a transport: state lives remotely, we can't send
-- functions over the wire. So:
--   ioPeek : IO (Maybe String)    — read remote state (serialized)
--   ioOver : String → IO String   — send input, get result back
--
-- This matches the Agent protocol: observe (peek) + step (over).

record IOOptic : Set where
  constructor mkIOOptic
  field
    ioPeek : IO (Maybe String)
    ioOver : String → IO (Maybe String)

open IOOptic public

------------------------------------------------------------------------
-- AgentOptic: HTTP-backed IOOptic to a server agent
------------------------------------------------------------------------

-- Construct IOOptic from agent HTTP endpoint.
-- peek = GET /agent-path/state
-- over = POST /agent-path/step with input as body

open import Agdelte.FFI.Server using
  ( IpcHandle
  ; connectProcess; queryProcess; stepProcess; closeProcess
  ; tryCatch
  )

-- AgentOptic via Unix socket (local process, same machine).
-- Uses the ProcessOptic IPC protocol.
-- Connection errors are caught: both peekIO and overIO return nothing.
-- NOTE: Creates a new socket connection per operation (connect/use/close).
-- Suitable for low-frequency inspection. For high-frequency polling,
-- consider a persistent-connection variant to avoid socket churn.
processAgentOptic : String → IOOptic
processAgentOptic socketPath = mkIOOptic peekIO overIO
  where
    peekIO : IO (Maybe String)
    peekIO =
      tryCatch (bracket (connectProcess socketPath)
                        closeProcess
                        queryProcess)

    overIO : String → IO (Maybe String)
    overIO input =
      tryCatch (bracket (connectProcess socketPath)
                        closeProcess
                        (λ h → stepProcess h input))

-- Persistent-connection variant: reuses an existing IPC handle.
-- Caller manages connect/close lifecycle (e.g. via bracket).
-- Suitable for high-frequency polling (no per-operation socket churn).
handleAgentOptic : IpcHandle → IOOptic
handleAgentOptic h = mkIOOptic
  (tryCatch (queryProcess h))
  (λ input → tryCatch (stepProcess h input))

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | IOOptic that always returns a fixed value (for testing)
constIOOptic : String → IOOptic
constIOOptic s = mkIOOptic (pure (just s)) (λ _ → pure (just s))

-- | IOOptic from a local IORef (for testing — local mutable state).
-- ioOver treats input as the new state verbatim (no agent transformation).
-- For testing agents that transform input, use processAgentOptic.
open import Agdelte.FFI.Server using (IORef; readIORef; writeIORef)

refOptic : IORef String → IOOptic
refOptic ref = mkIOOptic
  (readIORef ref >>= λ s → pure (just s))
  (λ input → writeIORef ref input >> pure (just input))
