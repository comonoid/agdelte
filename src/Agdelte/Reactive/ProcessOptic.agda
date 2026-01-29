{-# OPTIONS --without-K --guardedness #-}

-- ProcessOptic: access agent state in another OS process via Unix socket
--
-- Same peek/over conceptual interface as local Optic, but over IPC.
-- Server-side only (Haskell backend via MAlonzo).
--
-- Architecture:
--   Process A (server): serveProcessOptic path observe step
--   Process B (client): connectProcessOptic path >>= queryProcessOptic
--
-- Protocol (over Unix domain socket):
--   "peek"        → current observation (String)
--   "step:INPUT"  → step with INPUT, return new observation
--
-- Uses FFI/Server.agda for IO + IPC operations.
-- Uses FFI/Shared.agda Serialize for type-safe encoding/decoding.

module Agdelte.Reactive.ProcessOptic where

open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)

open import Agdelte.FFI.Server using
  ( _>>=_; _>>_; pure
  ; IpcHandle
  ; serveAgentProcess; connectProcess
  ; queryProcess; stepProcess; closeProcess
  )
open import Agdelte.FFI.Shared using (Serialize; encode; decode; TransportResult; success; failure)

private
  variable
    A : Set

------------------------------------------------------------------------
-- ProcessOptic: typed remote access over Unix socket
------------------------------------------------------------------------

-- | A ProcessOptic connects to an agent in another process.
-- The socketPath identifies the Unix domain socket.
-- Serialize instance provides type-safe encoding/decoding.
record ProcessOptic (A : Set) : Set where
  constructor mkProcessOptic
  field
    socketPath : String
    {{serial}}  : Serialize A

open ProcessOptic public

------------------------------------------------------------------------
-- Server side: expose agent over Unix socket
------------------------------------------------------------------------

-- | Serve an agent's state over a Unix socket.
-- Other processes can connect using connectProcessOptic.
--
-- Example:
--   serveProcessOptic "/tmp/counter.sock" observe step
--   where observe = readIORef ref >>= λ s → pure (encode s)
--         step input = ... modify ref ... >>= λ s → pure (encode s)
serveProcessOptic : ProcessOptic A
                  → IO String             -- observe: read current state
                  → (String → IO String)  -- step: apply input, return new state
                  → IO ⊤
serveProcessOptic po = serveAgentProcess (socketPath po)

------------------------------------------------------------------------
-- Client side: connect and perform optic operations
------------------------------------------------------------------------

-- | Connect to a remote agent's ProcessOptic.
-- Returns IPC handle for subsequent operations.
connectProcessOptic : ProcessOptic A → IO IpcHandle
connectProcessOptic po = connectProcess (socketPath po)

-- | Peek: read remote agent state (decode from String)
peekProcess : {{_ : Serialize A}} → IpcHandle → IO (TransportResult A)
peekProcess handle =
  queryProcess handle >>= λ raw →
  pure (decodeResult raw)
  where
    decodeResult : String → TransportResult _
    decodeResult raw with decode raw
    ... | just a  = success a
    ... | nothing = failure "decode failed"

-- | Step: modify remote agent state
stepProcessOptic : IpcHandle → String → IO (TransportResult String)
stepProcessOptic handle input =
  stepProcess handle input >>= λ raw →
  pure (success raw)

-- | Close the connection
disconnectProcess : IpcHandle → IO ⊤
disconnectProcess = closeProcess

------------------------------------------------------------------------
-- Convenience: one-shot query/step (connect, operate, close)
------------------------------------------------------------------------

-- | One-shot peek: connect, read state, close
peekOnce : ProcessOptic A → IO (TransportResult A)
peekOnce po =
  connectProcessOptic po >>= λ handle →
  peekProcess handle     >>= λ result →
  closeProcess handle    >>
  pure result

-- | One-shot step: connect, step, close
stepOnce : ProcessOptic A → String → IO (TransportResult String)
stepOnce po input =
  connectProcessOptic po >>= λ handle →
  stepProcessOptic handle input >>= λ result →
  closeProcess handle           >>
  pure result
