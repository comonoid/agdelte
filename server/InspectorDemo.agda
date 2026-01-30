{-# OPTIONS --without-K --guardedness #-}

-- Inspector / Diagram Demo
--
-- Demonstrates:
--   1. Define simple String→String agents (counter, echo, bang)
--   2. Build Diagrams with singleAgent, dualAgent, pipeline
--   3. Use wireSlot to bridge pure Agent to mutable IO
--   4. Use inspectDiagram to peek all agents and print states
--   5. Use sendAndPrint to send a command via IOOptic
--   6. Demonstrate _⊕D_ — merge two diagrams
--   7. Use refOptic for local IORef-based IOOptic
--
-- Compiles to Haskell (MAlonzo): agda --compile server/InspectorDemo.agda
-- Run: _build/InspectorDemo

module InspectorDemo where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Concurrent.Agent
open import Agdelte.Reactive.Diagram
open import Agdelte.Reactive.Inspector
open import Agdelte.Reactive.BigLens using (IOOptic; refOptic; constIOOptic; ioPeek; ioOver)
open import Agdelte.FFI.Server

------------------------------------------------------------------------
-- Demo Agents
------------------------------------------------------------------------

-- Counter: increments on each step
counterAgent : Agent Nat String String
counterAgent = mkAgent 0 show (λ n _ → suc n)

-- Echo: returns input as output
echoAgent : Agent String String String
echoAgent = mkAgent "<empty>" (λ s → s) (λ _ i → i)

-- Bang: appends "!" to input
bangAgent : Agent String String String
bangAgent = mkAgent "" (λ s → s) (λ _ i → i ++s "!")

------------------------------------------------------------------------
-- Diagrams
------------------------------------------------------------------------

-- 1. Single-agent
counterDiagram : Diagram
counterDiagram = singleAgent "counter" "/counter" counterAgent 3001

-- 2. Dual-agent
dualDiagram : Diagram
dualDiagram = dualAgent
  "counter" "/counter" counterAgent
  "echo"    "/echo"    echoAgent
  3002

-- 3. Pipeline: echo output feeds into bang
pipelineDiagram : Diagram
pipelineDiagram = pipeline
  "echo" "/echo" echoAgent
  "bang" "/bang" bangAgent
  3003

-- 4. Merged: counter ⊕ pipeline
mergedDiagram : Diagram
mergedDiagram = (counterDiagram ⊕D pipelineDiagram) 3004

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

printMaybe : String → Maybe String → IO ⊤
printMaybe label (just v) = putStrLn (label ++s " → " ++s v)
printMaybe label nothing  = putStrLn (label ++s " → <unavailable>")

------------------------------------------------------------------------
-- Demo runner
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  putStrLn "╔══════════════════════════════════════╗" >>
  putStrLn "║     Inspector / Diagram Demo         ║" >>
  putStrLn "╚══════════════════════════════════════╝" >>
  putStrLn "" >>

  -- 1. Inspect single-agent diagram (initial state)
  putStrLn "═══ 1. Single-agent Diagram (counter) ═══" >>
  inspectDiagram counterDiagram >>
  putStrLn "" >>

  -- 2. Inspect dual-agent diagram
  putStrLn "═══ 2. Dual-agent Diagram (counter + echo) ═══" >>
  inspectDiagram dualDiagram >>
  putStrLn "" >>

  -- 3. Inspect pipeline diagram
  putStrLn "═══ 3. Pipeline Diagram (echo >>> bang) ═══" >>
  inspectDiagram pipelineDiagram >>
  putStrLn "" >>

  -- 4. Inspect merged diagram
  putStrLn "═══ 4. Merged Diagram (counter ⊕ pipeline) ═══" >>
  inspectDiagram mergedDiagram >>
  putStrLn "" >>

  -- 5. wireSlot + refOptic: bridge Agent to mutable IO
  putStrLn "═══ 5. wireSlot + refOptic ═══" >>
  wireSlot (mkSlot "counter" "/counter" counterAgent) >>= λ _ →
  putStrLn "  Wired counter agent to AgentDef ✓" >>
  newIORef "initial-value" >>= λ ref →
  putStrLn "  Created refOptic from IORef" >>
  ioPeek (refOptic ref) >>= λ peeked →
  printMaybe "  refOptic.peek" peeked >>
  ioOver (refOptic ref) "updated-value" >>= λ overResult →
  putStrLn ("  refOptic.over(\"updated-value\") → " ++s overResult) >>
  ioPeek (refOptic ref) >>= λ peeked2 →
  printMaybe "  refOptic.peek (after over)" peeked2 >>
  putStrLn "" >>

  -- 6. sendAndPrint with constIOOptic
  putStrLn "═══ 6. sendAndPrint (constIOOptic) ═══" >>
  sendAndPrint "test-agent" (constIOOptic "test-state") "some-input" >>
  putStrLn "" >>

  -- 7. Inspect custom optic list
  putStrLn "═══ 7. inspectAll (custom optics) ═══" >>
  newIORef "hello" >>= λ ref2 →
  inspectAll (("ref-optic" , refOptic ref2)
             ∷ ("const-42" , constIOOptic "42")
             ∷ []) >>
  putStrLn "" >>

  putStrLn "Done."
