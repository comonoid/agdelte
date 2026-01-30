{-# OPTIONS --without-K --guardedness #-}

-- Session types as sugar over polynomial lenses
--
-- A Session describes a communication protocol.
-- SessionI/SessionO compile it to Agent input/output types.
-- Smart constructors hide inj₁/inj₂ tagging.
--
-- Architecture:
--   Session (protocol description)
--     ↓ SessionI, SessionO (compile to types)
--   Agent S (SessionI s) (SessionO s)
--     ↓ through + selectLeft/selectRight (from Wiring.agda)
--   Concrete typed interaction
--
-- See doc/research.md §1 for design rationale.

module Agdelte.Concurrent.Session where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id; const)
open import Agda.Builtin.String using (String)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring

------------------------------------------------------------------------
-- Session: protocol description
------------------------------------------------------------------------

-- A Session describes a communication protocol from the implementor's
-- perspective (the agent/server side).
--
-- send A s   = produce a value of type A, then continue with s
-- recv A s   = consume a value of type A, then continue with s
-- offer s₁ s₂ = client picks which branch (external choice, &)
-- choose s₁ s₂ = system picks which branch (internal choice, ⊕)
-- done       = protocol complete

{-# NO_UNIVERSE_CHECK #-}
data Session : Set₁ where
  send   : (A : Set) → Session → Session
  recv   : (A : Set) → Session → Session
  offer  : Session → Session → Session
  choose : Session → Session → Session
  done   : Session

------------------------------------------------------------------------
-- Duality: the other side's view
------------------------------------------------------------------------

-- If the server implements Session s, the client sees dual s.
-- send ↔ recv, offer ↔ choose.

dual : Session → Session
dual (send A s)     = recv A (dual s)
dual (recv A s)     = send A (dual s)
dual (offer s₁ s₂)  = choose (dual s₁) (dual s₂)
dual (choose s₁ s₂) = offer (dual s₁) (dual s₂)
dual done            = done

-- dual is an involution: dual (dual s) ≡ s
-- (proof deferred to Phase 10)

------------------------------------------------------------------------
-- Interpretation: Session → Agent interface types
------------------------------------------------------------------------

-- Compute the input type needed for a session.
-- recv A accumulates into a product; offer/choose use sums.
SessionI : Session → Set
SessionI (send A s)     = SessionI s
SessionI (recv A s)     = A × SessionI s
SessionI (offer s₁ s₂)  = SessionI s₁ ⊎ SessionI s₂
SessionI (choose s₁ s₂) = SessionI s₁ ⊎ SessionI s₂
SessionI done            = ⊤

-- Compute the output type produced by a session.
-- send A accumulates into a product; offer uses product (&), choose uses sum (⊕).
SessionO : Session → Set
SessionO (send A s)     = A × SessionO s
SessionO (recv A s)     = SessionO s
SessionO (offer s₁ s₂)  = SessionO s₁ × SessionO s₂
SessionO (choose s₁ s₂) = SessionO s₁ ⊎ SessionO s₂
SessionO done            = ⊤

------------------------------------------------------------------------
-- SessionAgent: Agent that implements a protocol
------------------------------------------------------------------------

-- An agent implementing session s has:
--   Input  = SessionI s  (what it receives)
--   Output = SessionO s  (what it produces)
SessionAgent : Session → Set → Set
SessionAgent s S = Agent S (SessionI s) (SessionO s)

------------------------------------------------------------------------
-- Example protocols
------------------------------------------------------------------------

-- ProcessOptic protocol (from server's perspective):
-- Server offers two services: peek (send state) or step (recv input, send new state)
--
-- offer
--   (recv ⊤ (send String done))        -- peek: receive unit, send state
--   (recv String (send String done))    -- step: receive input, send new state
--
-- SessionI = (⊤ × ⊤) ⊎ (String × ⊤) ≈ ⊤ ⊎ String
-- SessionO = (String × ⊤) × (String × ⊤) ≈ String × String

PeekProtocol : Session
PeekProtocol = recv ⊤ (send String done)

StepProtocol : Session
StepProtocol = recv String (send String done)

ProcessProtocol : Session
ProcessProtocol = offer PeekProtocol StepProtocol

-- Worker protocol (from worker's perspective):
-- recv input, send result
WorkerProtocol : Session
WorkerProtocol = recv String (send String done)

-- Request-response (generic):
ReqResp : Set → Set → Session
ReqResp Req Resp = recv Req (send Resp done)

------------------------------------------------------------------------
-- Smart constructors: build session I/O values without manual tagging
------------------------------------------------------------------------

-- For a simple recv A (send B done) session:
-- Input  = A × ⊤ ≈ A
-- Output = B × ⊤ ≈ B

-- Pack input for ReqResp
reqInput : ∀ {Req Resp : Set} → Req → SessionI (ReqResp Req Resp)
reqInput req = req , tt

-- Unpack output from ReqResp
respOutput : ∀ {Req Resp : Set} → SessionO (ReqResp Req Resp) → Resp
respOutput (resp , tt) = resp

-- For offer s₁ s₂: select left or right branch input
offerLeft : ∀ {s₁ s₂ : Session} → SessionI s₁ → SessionI (offer s₁ s₂)
offerLeft = inj₁

offerRight : ∀ {s₁ s₂ : Session} → SessionI s₂ → SessionI (offer s₁ s₂)
offerRight = inj₂

-- For offer s₁ s₂: extract left or right branch output
offerOutLeft : ∀ {s₁ s₂ : Session} → SessionO (offer s₁ s₂) → SessionO s₁
offerOutLeft = proj₁

offerOutRight : ∀ {s₁ s₂ : Session} → SessionO (offer s₁ s₂) → SessionO s₂
offerOutRight = proj₂

-- For ProcessProtocol specifically:
-- Peek: send ⊤, get first component of output
peekInput : SessionI ProcessProtocol
peekInput = offerLeft {PeekProtocol} {StepProtocol} (tt , tt)

-- Step: send String, get second component of output
stepInput : String → SessionI ProcessProtocol
stepInput input = offerRight {PeekProtocol} {StepProtocol} (input , tt)

-- Extract peek result
peekResult : SessionO ProcessProtocol → String
peekResult (peek , _) = proj₁ peek

-- Extract step result
stepResult : SessionO ProcessProtocol → String
stepResult (_ , step) = proj₁ step

------------------------------------------------------------------------
-- AgentLens selectors for session branches
------------------------------------------------------------------------

-- These reuse selectLeft/selectRight from Wiring.agda.
-- For an agent implementing (offer s₁ s₂):
--   through selectLeft agent  : interacts only via s₁
--   through selectRight agent : interacts only via s₂

-- Convenience: typed peek lens for ProcessProtocol
-- Changes interface from (⊤ ⊎ String) → (String × String)
--                     to  ⊤            → String
peekLens : AgentLens (SessionI ProcessProtocol) (SessionO ProcessProtocol)
                     (SessionI PeekProtocol) (SessionO PeekProtocol)
peekLens = selectLeft

-- Typed step lens for ProcessProtocol
stepLens : AgentLens (SessionI ProcessProtocol) (SessionO ProcessProtocol)
                     (SessionI StepProtocol) (SessionO StepProtocol)
stepLens = selectRight

------------------------------------------------------------------------
-- Constructing session agents from functions
------------------------------------------------------------------------

-- Build an agent for a simple request-response protocol
mkReqResp : ∀ {Req Resp S : Set} → S → (S → Resp) → (S → Req → S) → SessionAgent (ReqResp Req Resp) S
mkReqResp s₀ obs stp = record
  { state   = s₀
  ; observe = λ s → obs s , tt
  ; step    = λ s (req , tt) → stp s req
  }

-- Build an agent for offer protocol from two sub-agents
mkOffer : ∀ {s₁ s₂ : Session} {S₁ S₂ : Set}
        → SessionAgent s₁ S₁ → SessionAgent s₂ S₂
        → SessionAgent (offer s₁ s₂) (S₁ × S₂)
mkOffer a b = a & b
