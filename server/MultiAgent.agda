{-# OPTIONS --without-K --guardedness #-}

-- MultiAgent: Multiple agents exposed via HTTP + WebSocket
-- GET  /counter/state  → current count
-- POST /counter/step   → increment counter
-- GET  /toggle/state   → "on" or "off"
-- POST /toggle/step    → flip toggle
-- WS   /ws             → broadcasts on state changes

module MultiAgent where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false; Bool)
open import Data.Nat.Show using (show)
open import Data.Product using (proj₁; proj₂)

open import Agdelte.Concurrent.Agent
open import Agdelte.FFI.Server

------------------------------------------------------------------------
-- Counter Agent
------------------------------------------------------------------------

counterAgent : Agent Nat String String
counterAgent = mkAgent 0 show (λ n _ → suc n)

------------------------------------------------------------------------
-- Toggle Agent
------------------------------------------------------------------------

showBool : Bool → String
showBool true  = "on"
showBool false = "off"

flipBool : Bool → String → Bool
flipBool true  _ = false
flipBool false _ = true

toggleAgent : Agent Bool String String
toggleAgent = mkAgent false showBool flipBool

------------------------------------------------------------------------
-- Wire up: make AgentDef from Agent
------------------------------------------------------------------------

-- Create an AgentDef from a pure Agent coalgebra
-- This bridges Agda's pure Agent to the Haskell server runtime
wireAgent : ∀ {S} → String → String → Agent S String String → IO AgentDef
wireAgent name path agent =
  newIORef (observe agent (state agent)) >>= λ stateRef →
  newIORef agent >>= λ agentRef →
  let observeIO : IO String
      observeIO = readIORef agentRef >>= λ a →
                  pure (observe a (state a))

      stepIO : String → IO String
      stepIO input = readIORef agentRef >>= λ a →
                     let result = stepAgent a input in
                     let a' = proj₁ result in
                     let out = proj₂ result in
                     writeIORef agentRef a' >>
                     writeIORef stateRef out >>
                     pure out
  in
  pure (mkAgentDef name path stateRef observeIO stepIO)

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  wireAgent "counter" "/counter" counterAgent >>= λ counterDef →
  wireAgent "toggle" "/toggle" toggleAgent >>= λ toggleDef →
  putStrLn "Starting Multi-Agent Server..." >>
  runAgentServer2 3000 counterDef toggleDef
