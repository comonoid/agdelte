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
-- Composition chains effectful segments via _∘IO_.

module Agdelte.Reactive.BigLens where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.FFI.Server using (_>>=_; _>>_; pure)

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
  ; tryCatch
  )

-- AgentOptic via Unix socket (local process, same machine).
-- Uses the ProcessOptic IPC protocol.
-- Connection errors are caught: peekIO returns nothing, overIO logs
-- the error and returns "".
processAgentOptic : String → IOOptic
processAgentOptic socketPath = mkIOOptic peekIO overIO
  where
    peekIO : IO (Maybe String)
    peekIO =
      tryCatch (connectProcess socketPath >>= λ h →
                queryProcess h            >>= λ result →
                closeProcess h            >>
                pure result) >>= λ where
        (just result) → pure (just result)
        nothing       → pure nothing

    overIO : String → IO String
    overIO input =
      tryCatch (connectProcess socketPath >>= λ h →
                stepProcess h input       >>= λ result →
                closeProcess h            >>
                pure result) >>= λ where
        (just result) → pure result
        nothing       → pure ""

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
-- peek: outer first → if available, inner peek (outer value discarded because
--   IOOptic works on serialized strings — "nested peek" is just sequential peek).
-- over: inner first → feed result to outer (pipeline order).
-- This asymmetry (peek outer→inner, over inner→outer) is intentional.
_∘IO_ : IOOptic → IOOptic → IOOptic
outer ∘IO inner = mkIOOptic
  (ioPeek outer >>= helper)
  (λ input → ioOver inner input >>= ioOver outer)
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
