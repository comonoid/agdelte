{-# OPTIONS --without-K --guardedness #-}

-- Wiring Diagrams — declarative agent-client topology
--
-- A Diagram describes which agents exist and how they connect:
--   - Agent outputs can broadcast to all WS clients
--   - Agent outputs can feed into other agents' inputs
--   - Client inputs route to specific agents
--
-- The server runtime interprets the Diagram to set up routing.
-- This replaces the ad-hoc wireAgent + runAgentServer2 pattern
-- from MultiAgent.agda with a structured, composable description.
--
-- Corresponds to polynomial composition:
--   Diagram ≅ Wiring diagram in the Poly category
--   Each Slot is a polynomial p(y) = O × y^I
--   Connections are lenses between polynomials

module Agdelte.Reactive.Diagram where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; any)
open import Data.Product using (_×_; _,_)

open import Agdelte.Concurrent.Agent using (Agent; state; observe; step)

------------------------------------------------------------------------
-- Connection: where agent output goes
------------------------------------------------------------------------

-- A Connection describes one routing rule in the network.
-- On each agent step, the runtime checks all connections and routes output.
data Connection : Set where
  -- Agent output broadcasts to all connected WS clients
  -- Example: counter state change → all browsers see new count
  broadcast   : String → Connection

  -- Agent output feeds into another agent's input
  -- Example: sensor agent output → controller agent input
  agentPipe   : String → String → Connection  -- source → target

  -- Client input (from browser WS) routes to an agent
  -- Example: button click in browser → counter agent step
  clientRoute : String → Connection            -- target agent name

------------------------------------------------------------------------
-- Slot: a named agent in the diagram
------------------------------------------------------------------------

-- A Slot is one node in the wiring diagram.
-- It has a name, an HTTP path, and a pure Agent definition.
-- The runtime bridges it to the mutable server via wireAgent.
record Slot : Set₁ where
  constructor mkSlot
  field
    name  : String                    -- display name ("counter")
    path  : String                    -- HTTP path ("/counter")
    {S}   : Set                       -- hidden state type
    agent : Agent S String String     -- pure coalgebra

open Slot public

------------------------------------------------------------------------
-- Diagram: complete network topology
------------------------------------------------------------------------

-- A Diagram is a list of agent slots plus a list of connections.
-- The runtime interprets this to:
--   1. Wire each slot's Agent to the HTTP server
--   2. Set up connection routing on each step
--   3. Register client routes for incoming WS messages
-- DiagramSpec: topology without deployment details (port).
-- This is the composable unit — combinators work on DiagramSpec.
record DiagramSpec : Set₁ where
  constructor mkDiagramSpec
  field
    slots       : List Slot
    connections : List Connection

open DiagramSpec public

-- Diagram: topology + deployment config (port).
-- Created from DiagramSpec at deployment time.
record Diagram : Set₁ where
  constructor mkDiagram
  field
    spec : DiagramSpec
    port : Nat

-- spec is hidden to avoid clash with DiagramSpec fields; use Diagram.spec d
open Diagram public hiding (spec)

------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------

-- Single agent, broadcast to all clients (most common pattern)
singleAgent : String → String → ∀ {S} → Agent S String String → DiagramSpec
singleAgent n p a = mkDiagramSpec
  (mkSlot n p a ∷ [])
  (broadcast n ∷ clientRoute n ∷ [])

-- Two independent agents, both broadcast, clients route to either
dualAgent : String → String → ∀ {S₁} → Agent S₁ String String →
            String → String → ∀ {S₂} → Agent S₂ String String →
            DiagramSpec
dualAgent n₁ p₁ a₁ n₂ p₂ a₂ = mkDiagramSpec
  (mkSlot n₁ p₁ a₁ ∷ mkSlot n₂ p₂ a₂ ∷ [])
  (broadcast n₁ ∷ broadcast n₂ ∷ clientRoute n₁ ∷ clientRoute n₂ ∷ [])

-- Pipeline: output of first agent feeds input of second.
-- Only the first agent has a clientRoute (WS clients send to n₁).
-- The second agent receives input exclusively via the pipe from n₁.
-- Both agents are accessible via HTTP through their respective paths.
pipeline : String → String → ∀ {S₁} → Agent S₁ String String →
           String → String → ∀ {S₂} → Agent S₂ String String →
           DiagramSpec
pipeline n₁ p₁ a₁ n₂ p₂ a₂ = mkDiagramSpec
  (mkSlot n₁ p₁ a₁ ∷ mkSlot n₂ p₂ a₂ ∷ [])
  (agentPipe n₁ n₂ ∷ broadcast n₂ ∷ clientRoute n₁ ∷ [])

-- Deploy a DiagramSpec on a specific port
deploy : DiagramSpec → Nat → Diagram
deploy ds pt = mkDiagram ds pt

------------------------------------------------------------------------
-- DiagramSpec combinators
------------------------------------------------------------------------

-- Check if a slot name exists in a diagram spec (for connection validation)
open import Agda.Builtin.String using (primStringEquality)

hasSlot : String → DiagramSpec → Bool
hasSlot n d = anyBool (λ s → primStringEquality n (name s)) (slots d)
  where
    anyBool : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
    anyBool _ [] = false
    anyBool p (x ∷ xs) = if p x then true else anyBool p xs

-- Bool-based filter (Data.List.filter requires Dec in stdlib v2.x)
boolFilter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolFilter _ []       = []
boolFilter p (x ∷ xs) with p x
... | true  = x ∷ boolFilter p xs
... | false = boolFilter p xs

-- Merge two diagram specs (union of slots and connections).
-- Slots from d₂ whose names already exist in d₁ are SILENTLY dropped
-- to prevent duplicate slot names causing ambiguous routing.
-- WARNING: a typo giving two slots the same name will cause one to be
-- silently discarded with no error. Consider validating names at use site.
-- Connections from d₂ that reference dropped slots are also removed,
-- since they would silently target d₁'s agent instead of d₂'s.
_⊕D_ : DiagramSpec → DiagramSpec → DiagramSpec
d₁ ⊕D d₂ = mkDiagramSpec
  (slots d₁ ++ uniqueSlots)
  (connections d₁ ++ validConns)
  where
    open Data.List using (_++_)
    uniqueSlots = boolFilter (λ s → not (hasSlot (name s) d₁)) (slots d₂)
    -- A slot from d₂ was "dropped" if d₁ already has that name
    wasDropped : String → Bool
    wasDropped n = hasSlot n d₁
    -- A connection from d₂ is invalid if it references a dropped slot
    connRefsDropped : Connection → Bool
    connRefsDropped (broadcast n)     = wasDropped n
    connRefsDropped (agentPipe s t)   = wasDropped s ∨ wasDropped t
    connRefsDropped (clientRoute n)   = wasDropped n
    validConns = boolFilter (λ c → not (connRefsDropped c)) (connections d₂)
    open import Data.Bool using (_∨_)

-- Add a connection to a diagram spec
wireSpec : Connection → DiagramSpec → DiagramSpec
wireSpec c d = mkDiagramSpec (slots d) (c ∷ connections d)

-- Add a connection to a deployed diagram
wire : Connection → Diagram → Diagram
wire c d = mkDiagram (wireSpec c (Diagram.spec d)) (port d)

------------------------------------------------------------------------
-- IO: interpret diagram into running server
------------------------------------------------------------------------

-- The actual interpretation happens in Haskell (AgentServer.hs).
-- This postulate bridges the Agda Diagram type to the Haskell runtime.
-- The Haskell side:
--   1. Calls wireAgent for each Slot
--   2. Sets up connection routing in the httpHandler
--   3. Runs the server on the specified port

open import Agdelte.FFI.Server using
  ( _>>=_; _>>_; pure; putStrLn
  ; AgentDef; runAgentServerNWithConns
  ; ConnectionDef; mkBroadcastDef; mkAgentPipeDef; mkClientRouteDef
  ; wireAgent
  )

-- Wire a Slot to AgentDef using shared wireAgent
wireSlot : Slot → IO AgentDef
wireSlot s = wireAgent (name s) (path s) (agent s)

-- Wire all slots sequentially (IO mapM)
wireSlots : List Slot → IO (List AgentDef)
wireSlots []       = pure []
wireSlots (s ∷ ss) =
  wireSlot s >>= λ d →
  wireSlots ss >>= λ ds →
  pure (d ∷ ds)

-- Compile Connection to FFI ConnectionDef
compileConnection : Connection → ConnectionDef
compileConnection (broadcast n)     = mkBroadcastDef n
compileConnection (agentPipe s t)   = mkAgentPipeDef s t
compileConnection (clientRoute n)   = mkClientRouteDef n

compileConnections : List Connection → List ConnectionDef
compileConnections []       = []
compileConnections (c ∷ cs) = compileConnection c ∷ compileConnections cs

-- Detect duplicate slot names and print warnings
private
  warnDuplicates : List Slot → IO ⊤
  warnDuplicates []       = pure tt
    where open import Agda.Builtin.Unit using (tt)
  warnDuplicates (s ∷ ss) =
    (if hasDup (name s) ss
     then putStrLn ("WARNING: duplicate slot name \"" ++ name s ++ "\" — later definition will be shadowed")
     else pure tt) >>
      warnDuplicates ss
    where
      open import Data.String using (_++_)
      open import Data.Bool using (if_then_else_)
      open import Agda.Builtin.Unit using (tt)
      hasDup : String → List Slot → Bool
      hasDup _ []       = false
      hasDup n (x ∷ xs) with primStringEquality n (name x)
      ... | true  = true
      ... | false = hasDup n xs

-- Run a diagram with any number of agents and connections
runDiagram : Diagram → IO ⊤
runDiagram d =
  putStrLn "Starting Diagram Server..." >>
  warnDuplicates (slots (Diagram.spec d)) >>
  wireSlots (slots (Diagram.spec d)) >>= λ defs →
  runAgentServerNWithConns (port d) defs
    (compileConnections (connections (Diagram.spec d)))

-- Run a DiagramSpec directly on a given port
runDiagramSpec : Nat → DiagramSpec → IO ⊤
runDiagramSpec pt ds = runDiagram (deploy ds pt)

