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
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false; Bool)
open import Data.Nat.Show using (show)
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
-- Main
------------------------------------------------------------------------

main : IO ⊤
main =
  wireAgent "counter" "/counter" counterAgent >>= λ counterDef →
  wireAgent "toggle" "/toggle" toggleAgent >>= λ toggleDef →
  putStrLn "Starting Multi-Agent Server..." >>
  runAgentServerN 3000 (counterDef ∷ toggleDef ∷ [])
  where open import Agda.Builtin.List using (List; []; _∷_)
