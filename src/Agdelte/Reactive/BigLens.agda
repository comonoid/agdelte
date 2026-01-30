{-# OPTIONS --without-K --guardedness #-}

-- Phase 8: Big Lens — Network-Wide Optic
--
-- Extends the Optic abstraction to span:
--   LocalOptic   — pure peek/over (Phase 6, already in Optic.agda)
--   AgentOptic   — HTTP GET/POST to server agents
--   ClientOptic  — WebSocket peek/over to browser clients
--   ProcessOptic — Unix socket (Phase 7, already in ProcessOptic.agda)
--
-- Key idea: IOOptic is the effectful counterpart of Optic.
-- Same peek/over interface, but in IO and string-serialized.
--
-- Transport is encoded in the interpretation, not in the lens itself.
-- Composition chains effectful segments via _∘IO_.

module Agdelte.Reactive.BigLens where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.FFI.Server using (_>>=_; _>>_; pure; _++s_)

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
    ioOver : String → IO String

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
  )

-- AgentOptic via Unix socket (local process, same machine).
-- Uses the ProcessOptic IPC protocol.
processAgentOptic : String → IOOptic
processAgentOptic socketPath = mkIOOptic peekIO overIO
  where
    peekIO : IO (Maybe String)
    peekIO =
      connectProcess socketPath >>= λ h →
      queryProcess h            >>= λ result →
      closeProcess h            >>
      pure (just result)

    overIO : String → IO String
    overIO input =
      connectProcess socketPath >>= λ h →
      stepProcess h input       >>= λ result →
      closeProcess h            >>
      pure result

------------------------------------------------------------------------
-- ClientOptic: WebSocket-backed IOOptic to a browser client
------------------------------------------------------------------------

-- For Phase 8B: the server sends WS messages to a specific client.
-- Protocol:
--   peek → send {"peek":"model"} → client responds with serialized model
--   over → send {"over":"MsgPayload"} → client dispatches, responds with new state
--
-- This requires:
--   1. Server knows client IDs (assigned on WS connect)
--   2. Server can send targeted WS messages (not just broadcast)
--   3. Client handles incoming peek/over requests
--
-- For now, we define the Agda-side type. The WS transport FFI will be
-- added in 8B when we extend AgentServer.hs.

-- Placeholder: will be backed by WS FFI in 8B
postulate
  wsPeekClient : String → IO (Maybe String)   -- clientId → peek
  wsOverClient : String → String → IO String   -- clientId → input → result

clientOptic : String → IOOptic
clientOptic clientId = mkIOOptic (wsPeekClient clientId) (wsOverClient clientId)

------------------------------------------------------------------------
-- IOOptic composition
------------------------------------------------------------------------

-- Composition of IOOptic is sequential: first peek outer, use result
-- to drive inner. Since IOOptic operates on serialized strings,
-- composition passes the serialized result through.
--
-- Unlike pure Optic where we compose peek (a >>= b) and over (a ∘ b),
-- IOOptic composition must account for the fact that "over" can't
-- compose transparently — each segment has its own input format.
--
-- The meaningful composition is:
--   peek: outer.peek >>= (feed to inner as context)
--   over: direct — each IOOptic's over is self-contained
--
-- For true Big Lens composition (e.g. peek into agent, then into field),
-- we compose IOOptic with pure Optic:

-- | Compose two IOOptics sequentially.
-- peek: outer peek, then if available, inner peek.
-- over: send input directly to outer (each level has its own step protocol).
_∘IO_ : IOOptic → IOOptic → IOOptic
outer ∘IO inner = mkIOOptic
  (ioPeek outer >>= helper)
  (ioOver outer)
  where
    helper : Maybe String → IO (Maybe String)
    helper nothing  = pure nothing
    helper (just _) = ioPeek inner

infixr 9 _∘IO_

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | IOOptic that always returns a fixed value (for testing)
constIOOptic : String → IOOptic
constIOOptic s = mkIOOptic (pure (just s)) (λ _ → pure s)

-- | IOOptic from a local IORef (for testing — local mutable state)
open import Agdelte.FFI.Server using (IORef; readIORef; writeIORef)

refOptic : IORef String → IOOptic
refOptic ref = mkIOOptic
  (readIORef ref >>= λ s → pure (just s))
  (λ input → writeIORef ref input >> pure input)
