{-# OPTIONS --without-K --guardedness #-}

-- Research §3: ! (Bang) — Shareable Agents
--
-- In linear logic, !A means "unlimited copies of A".
-- For agents: an agent that can serve multiple clients simultaneously.
--
-- Formalizes the pattern already used by:
--   - ProcessOptic: multiple processes connect to one agent via Unix socket
--   - RemoteOptic: multiple browsers connect to one agent via HTTP
--   - AgentServer.hs: one agent, many WS subscribers
--
-- SharedAgent is the type-level witness that an agent is shareable.
-- LinearAgent is the type-level witness for one-shot interaction.

module Agdelte.Concurrent.SharedAgent where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Function using (id; const)

open import Agdelte.Concurrent.Agent

------------------------------------------------------------------------
-- SharedAgent: existentially quantified, marked shareable
------------------------------------------------------------------------

-- A SharedAgent hides its state type (like SomeAgent from Wiring.agda)
-- and is explicitly marked as serving multiple clients.
record SharedAgent (I O : Set) : Set₁ where
  constructor mkShared
  field
    {S}   : Set
    agent : Agent S I O

open SharedAgent public

------------------------------------------------------------------------
-- LinearAgent: one-shot interaction, consumed after use
------------------------------------------------------------------------

-- A LinearAgent can be used exactly once. After stepping, it's consumed.
-- This models one-shot workers, single-use channels, etc.
--
-- WARNING: The "linear" invariant is enforced BY CONVENTION ONLY.
-- LinearAgent is structurally identical to SharedAgent — Agda lacks
-- linear types, so nothing prevents calling useLinear multiple times
-- on the same value. The restricted API (useLinear returns O, not
-- LinearAgent × O) discourages reuse, but does not prevent it.
-- TODO: Revisit when/if Agda gets linearity support.
record LinearAgent (I O : Set) : Set₁ where
  constructor mkLinear
  field
    {S}   : Set
    agent : Agent S I O

open LinearAgent public

------------------------------------------------------------------------
-- Constructors
------------------------------------------------------------------------

-- Mark an agent as shareable
share : ∀ {S I O} → Agent S I O → SharedAgent I O
share a = mkShared a

-- Mark an agent as linear (one-shot)
asLinear : ∀ {S I O} → Agent S I O → LinearAgent I O
asLinear a = mkLinear a

open import Agdelte.Concurrent.Wiring using (SomeAgent; someAgent)

-- Forget multiplicity: extract the underlying SomeAgent
forgetShared : ∀ {I O} → SharedAgent I O → SomeAgent I O
forgetShared (mkShared a) = someAgent a

forgetLinear : ∀ {I O} → LinearAgent I O → SomeAgent I O
forgetLinear (mkLinear a) = someAgent a

------------------------------------------------------------------------
-- SharedAgent operations: multiple clients share state
------------------------------------------------------------------------

-- Observe shared agent (non-destructive, any client can peek)
peekShared : ∀ {I O} → SharedAgent I O → O
peekShared sa = observe (agent sa) (state (agent sa))

-- Step shared agent — pure function returning a new SharedAgent value.
-- NOTE: "shared" refers to the type-level CAPABILITY of serving multiple
-- clients, not runtime concurrency. Two concurrent callers stepping the
-- same SharedAgent get independent copies. For actual concurrent sharing,
-- wrap with MVar at the IO level (see wireAgent in FFI/Server.agda).
stepShared : ∀ {I O} → SharedAgent I O → I → SharedAgent I O × O
stepShared sa i =
  let result = stepAgent (agent sa) i
  in mkShared (proj₁ result) , proj₂ result

------------------------------------------------------------------------
-- LinearAgent operations: consumed after single use
------------------------------------------------------------------------

-- Use linear agent exactly once: step and get result.
-- Returns output only — the agent is "consumed" (not returned).
useLinear : ∀ {I O} → LinearAgent I O → I → O
useLinear la i = proj₂ (stepAgent (LinearAgent.agent la) i)

-- CPS-style linear use: the callback receives a step function (I → O),
-- not the agent itself, so the LinearAgent handle cannot be aliased.
-- NOTE: the step function itself is a first-class value and CAN be called
-- multiple times — CPS hides the agent, but does not enforce single-use.
-- True linearity would require linear types (not available in Agda).
withLinear : ∀ {I O A : Set} → LinearAgent I O → ((I → O) → A) → A
withLinear la f = f (useLinear la)

------------------------------------------------------------------------
-- Composition: SharedAgent combinators
------------------------------------------------------------------------

-- Parallel shared agents
_***shared_ : ∀ {I₁ O₁ I₂ O₂} →
              SharedAgent I₁ O₁ → SharedAgent I₂ O₂ →
              SharedAgent (I₁ × I₂) (O₁ × O₂)
mkShared a ***shared mkShared b = mkShared (a *** b)
  where open import Agdelte.Concurrent.Wiring using (_***_)

-- Fan-out shared agent: same input to both
fanoutShared : ∀ {I O₁ O₂} →
               SharedAgent I O₁ → SharedAgent I O₂ →
               SharedAgent I (O₁ × O₂)
fanoutShared (mkShared a) (mkShared b) = mkShared (fanout a b)
  where open import Agdelte.Concurrent.Wiring using (fanout)

-- Pipeline shared agents
_>>>shared_ : ∀ {I M O} →
              SharedAgent I M → SharedAgent M O →
              SharedAgent I O
mkShared a >>>shared mkShared b = mkShared (a >>> b)
  where open import Agdelte.Concurrent.Wiring using (_>>>_)

------------------------------------------------------------------------
-- Registry: named collection of shared agents
------------------------------------------------------------------------

-- A named shared agent (for server registration)
record NamedAgent : Set₁ where
  constructor mkNamed
  field
    agentName : String
    agentPath : String
    {I O}     : Set
    shared    : SharedAgent I O

open NamedAgent public

-- A registry is a list of named shared agents
Registry : Set₁
Registry = List NamedAgent

open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (primStringEquality)

-- Lookup by name (linear scan)
lookupAgent : String → Registry → Maybe NamedAgent
lookupAgent _ [] = nothing
lookupAgent n (na ∷ rest) with primStringEquality n (agentName na)
... | true  = just na
... | false = lookupAgent n rest
