{-# OPTIONS --without-K --guardedness #-}

-- Server entry point: echo agent
-- Compiles via MAlonzo to native Haskell binary

module Main where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (proj₁; proj₂)

open import Agdelte.Concurrent.Agent
open import Agdelte.FFI.Server

------------------------------------------------------------------------
-- Echo Agent: counts and echoes lines
------------------------------------------------------------------------

-- The echo agent: counts inputs and echoes them back
-- State = ℕ (message count), Input = String, Output = String (count)
echoAgent : Agent ℕ String String
echoAgent = mkAgent 0 show λ n _ → suc n

------------------------------------------------------------------------
-- IO loop: feed stdin lines to agent
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
loop : Agent ℕ String String → IO ⊤
loop agent =
  getLine >>= λ line →
  let result = stepAgent agent line in
  let agent' = proj₁ result in
  let count  = proj₂ result in
  putStrLn ("Echo [" ++s count ++s "]: " ++s line) >>
  loop agent'

main : IO ⊤
main =
  putStrLn "Agdelte Echo Server (MAlonzo)" >>
  putStrLn "Type a line and press Enter:" >>
  loop echoAgent
