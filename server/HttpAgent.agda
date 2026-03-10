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
  listen 3000 (λ req → handleReq req ref)
  where
    handleReq : HttpRequest → IORef (Agent Nat String String) → IO String
    handleReq req ref with primStringEquality (reqPath req) "/state"
    ... | true  = readIORef ref >>= λ agent →
                  pure (observe agent (state agent))
    ... | false with primStringEquality (reqPath req) "/step"
    ...   | true with primStringEquality (reqMethod req) "POST"
    ...     | true  = atomicModifyIORef ref
                        (λ agent → stepAgent agent (reqBody req))
    ...     | false = pure "Method not allowed (use POST)"
    ...   | false = pure "Not found"
