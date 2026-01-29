{-# OPTIONS --without-K --guardedness #-}

-- HttpAgent: Counter Agent exposed via HTTP
-- GET  /state → current count
-- POST /step  → increment, return new count
-- Compiles via MAlonzo to native HTTP server

module HttpAgent where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false)
open import Data.Nat.Show using (show)
open import Data.Product using (proj₁; proj₂)

open import Agdelte.Concurrent.Agent
open import Agdelte.FFI.Server

------------------------------------------------------------------------
-- Counter Agent: increments on each POST /step
------------------------------------------------------------------------

counterAgent : Agent Nat String String
counterAgent = mkAgent 0 show (λ n _ → suc n)

------------------------------------------------------------------------
-- HTTP handler: routes requests to Agent
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  newIORef counterAgent >>= λ ref →
  putStrLn "Agdelte HTTP Agent on port 3000" >>
  putStrLn "  GET  /state → current count" >>
  putStrLn "  POST /step  → increment counter" >>
  listen 3000 (λ req →
    readIORef ref >>= λ agent →
    handleReq agent req ref)
  where
    route : String → Agent Nat String String → HttpRequest → IORef (Agent Nat String String) → IO String
    route path agent req ref with primStringEquality path "/state"
    ... | true  = pure (observe agent (state agent))
    ... | false with primStringEquality path "/step"
    ...   | true  =
              let result = stepAgent agent (reqBody req) in
              let agent' = proj₁ result in
              let output = proj₂ result in
              writeIORef ref agent' >>
              pure output
    ...   | false = pure "Not found"

    handleReq : Agent Nat String String → HttpRequest → IORef (Agent Nat String String) → IO String
    handleReq agent req ref = route (reqPath req) agent req ref
