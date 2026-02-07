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
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Concurrent.Agent using (Agent; state; observe; step; stepAgent)

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
record Diagram : Set₁ where
  constructor mkDiagram
  field
    slots       : List Slot
    connections : List Connection
    port        : Nat

open Diagram public

------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------

-- Single agent, broadcast to all clients (most common pattern)
singleAgent : String → String → ∀ {S} → Agent S String String → Nat → Diagram
singleAgent n p a pt = mkDiagram
  (mkSlot n p a ∷ [])
  (broadcast n ∷ clientRoute n ∷ [])
  pt

-- Two independent agents, both broadcast, clients route to either
dualAgent : String → String → ∀ {S₁} → Agent S₁ String String →
            String → String → ∀ {S₂} → Agent S₂ String String →
            Nat → Diagram
dualAgent n₁ p₁ a₁ n₂ p₂ a₂ pt = mkDiagram
  (mkSlot n₁ p₁ a₁ ∷ mkSlot n₂ p₂ a₂ ∷ [])
  (broadcast n₁ ∷ broadcast n₂ ∷ clientRoute n₁ ∷ clientRoute n₂ ∷ [])
  pt

-- Pipeline: output of first agent feeds input of second
pipeline : String → String → ∀ {S₁} → Agent S₁ String String →
           String → String → ∀ {S₂} → Agent S₂ String String →
           Nat → Diagram
pipeline n₁ p₁ a₁ n₂ p₂ a₂ pt = mkDiagram
  (mkSlot n₁ p₁ a₁ ∷ mkSlot n₂ p₂ a₂ ∷ [])
  (agentPipe n₁ n₂ ∷ broadcast n₂ ∷ clientRoute n₁ ∷ [])
  pt

------------------------------------------------------------------------
-- Diagram combinators
------------------------------------------------------------------------

-- Merge two diagrams (union of slots and connections)
_⊕D_ : Diagram → Diagram → Nat → Diagram
(d₁ ⊕D d₂) pt = mkDiagram
  (slots d₁ ++ slots d₂)
  (connections d₁ ++ connections d₂)
  pt
  where open Data.List using (_++_)

-- Add a connection to a diagram
wire : Connection → Diagram → Diagram
wire c d = mkDiagram (slots d) (c ∷ connections d) (port d)

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
  ; AgentDef; mkAgentDef; runAgentServer1; runAgentServer2
  ; IORef; newIORef; readIORef; writeIORef
  )
-- Wire a single slot to an AgentDef (bridge pure Agent to mutable server)
wireSlot : Slot → IO AgentDef
wireSlot s =
  let a = agent s in
  newIORef (observe a (state a)) >>= λ stateRef →
  newIORef a                     >>= λ agentRef →
  let observeIO : IO String
      observeIO = readIORef agentRef >>= λ ag →
                  pure (observe ag (state ag))

      stepIO : String → IO String
      stepIO input = readIORef agentRef >>= λ ag →
                     let result = stepAgent ag input in
                     let ag'    = proj₁ result in
                     let out    = proj₂ result in
                     writeIORef agentRef ag' >>
                     writeIORef stateRef out >>
                     pure out
  in
  pure (mkAgentDef (name s) (path s) stateRef observeIO stepIO)

-- Run a diagram with 1 agent
runDiagram1 : Diagram → IO ⊤
runDiagram1 d with slots d
... | s ∷ [] =
  putStrLn "Starting Diagram Server..." >>
  wireSlot s >>= λ def →
  runAgentServer1 (port d) def
... | _ = putStrLn "Error: runDiagram1 expects exactly 1 slot"

-- Run a diagram with 2 agents
runDiagram2 : Diagram → IO ⊤
runDiagram2 d with slots d
... | s₁ ∷ s₂ ∷ [] =
  putStrLn "Starting Diagram Server..." >>
  wireSlot s₁ >>= λ def₁ →
  wireSlot s₂ >>= λ def₂ →
  runAgentServer2 (port d) def₁ def₂
... | _ = putStrLn "Error: runDiagram2 expects exactly 2 slots"
