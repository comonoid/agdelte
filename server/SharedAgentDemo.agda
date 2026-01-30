{-# OPTIONS --without-K --guardedness #-}

-- SharedAgent Demo: multiplicity markers, registry, composition
--
-- Demonstrates:
--   1. share / asLinear — wrap agents with multiplicity witness
--   2. peekShared / stepShared — observe and step shared agents
--   3. useLinear — one-shot consumption of linear agent
--   4. _***shared_ — parallel composition of shared agents
--   5. _>>>shared_ — pipeline composition
--   6. fanoutShared — same input to two shared agents
--   7. NamedAgent / Registry / lookupAgent — named agent collection
--
-- Compiles to Haskell (MAlonzo): npm run build:shared-demo
-- Run: npm run run:shared-demo

module SharedAgentDemo where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.SharedAgent
open import Agdelte.FFI.Server using (_>>=_; _>>_; pure; putStrLn; _++s_)

------------------------------------------------------------------------
-- Demo Agents
------------------------------------------------------------------------

-- Counter: Nat state, increments on each step
counterAgent : Agent Nat String String
counterAgent = mkAgent 0 show (λ n _ → suc n)

-- Accumulator: appends input strings
accAgent : Agent String String String
accAgent = mkAgent "" (λ s → s) (λ s i → s ++s i)

-- Echo agent: returns input as-is
echoAgent : Agent String String String
echoAgent = mkAgent "" (λ s → s) (λ _ i → i)

-- Bang: appends "!" to input
bangAgent : Agent String String String
bangAgent = mkAgent "" (λ s → s) (λ _ i → i ++s "!")

------------------------------------------------------------------------
-- SharedAgents
------------------------------------------------------------------------

sharedCounter : SharedAgent String String
sharedCounter = share counterAgent

sharedAcc : SharedAgent String String
sharedAcc = share accAgent

sharedEcho : SharedAgent String String
sharedEcho = share echoAgent

sharedBang : SharedAgent String String
sharedBang = share bangAgent

------------------------------------------------------------------------
-- LinearAgent
------------------------------------------------------------------------

linearEcho : LinearAgent String String
linearEcho = asLinear echoAgent

------------------------------------------------------------------------
-- Composed SharedAgents
------------------------------------------------------------------------

-- Pipeline: echo >>> bang (input → echo → add "!")
pipelined : SharedAgent String String
pipelined = sharedEcho >>>shared sharedBang

-- Parallel: counter *** accumulator
parallel : SharedAgent (String × String) (String × String)
parallel = sharedCounter ***shared sharedAcc

-- Fanout: same input to counter and accumulator
fanned : SharedAgent String (String × String)
fanned = fanoutShared sharedCounter sharedAcc

------------------------------------------------------------------------
-- Registry
------------------------------------------------------------------------

registry : Registry
registry =
    mkNamed "counter" "/counter" sharedCounter
  ∷ mkNamed "accumulator" "/acc" sharedAcc
  ∷ mkNamed "pipeline" "/pipe" pipelined
  ∷ []

------------------------------------------------------------------------
-- Demo runner
------------------------------------------------------------------------

printLookup : String → IO ⊤
printLookup n with lookupAgent n registry
... | just na  = putStrLn ("  lookup \"" ++s n ++s "\" → found: " ++s NamedAgent.agentName na ++s " at " ++s NamedAgent.agentPath na)
... | nothing  = putStrLn ("  lookup \"" ++s n ++s "\" → not found")

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  putStrLn "╔══════════════════════════════════════╗" >>
  putStrLn "║     SharedAgent Demo                 ║" >>
  putStrLn "╚══════════════════════════════════════╝" >>
  putStrLn "" >>

  -- 1. Peek initial state
  putStrLn "═══ 1. Peek shared agents ═══" >>
  putStrLn ("  counter    → " ++s peekShared sharedCounter) >>
  putStrLn ("  accumulator → " ++s peekShared sharedAcc) >>
  putStrLn "" >>

  -- 2. Step shared counter (pure chain)
  putStrLn "═══ 2. Step shared counter 3× ═══" >>
  (let r1 = stepShared sharedCounter "go" in
   let c1 = proj₁ r1 in
   putStrLn ("  step 1 → " ++s proj₂ r1) >>
   let r2 = stepShared c1 "go" in
   let c2 = proj₁ r2 in
   putStrLn ("  step 2 → " ++s proj₂ r2) >>
   let r3 = stepShared c2 "go" in
   putStrLn ("  step 3 → " ++s proj₂ r3) >>
   putStrLn ("  final  → " ++s peekShared (proj₁ r3))) >>
  putStrLn "" >>

  -- 3. Step accumulator
  putStrLn "═══ 3. Step accumulator ═══" >>
  (let r1 = stepShared sharedAcc "hello" in
   let a1 = proj₁ r1 in
   putStrLn ("  +\"hello\" → " ++s proj₂ r1) >>
   let r2 = stepShared a1 " world" in
   putStrLn ("  +\" world\" → " ++s proj₂ r2) >>
   putStrLn ("  final    → " ++s peekShared (proj₁ r2))) >>
  putStrLn "" >>

  -- 4. Linear agent (one-shot)
  putStrLn "═══ 4. Linear agent (one-shot) ═══" >>
  putStrLn ("  useLinear echo \"one-shot\" → " ++s useLinear linearEcho "one-shot") >>
  putStrLn "" >>

  -- 5. Pipeline: echo >>> bang
  putStrLn "═══ 5. Pipeline (echo >>>shared bang) ═══" >>
  putStrLn ("  initial → " ++s peekShared pipelined) >>
  (let r1 = stepShared pipelined "hello" in
   putStrLn ("  step(\"hello\") → " ++s proj₂ r1) >>
   let r2 = stepShared (proj₁ r1) "world" in
   putStrLn ("  step(\"world\") → " ++s proj₂ r2)) >>
  putStrLn "" >>

  -- 6. Fanout: same input to counter + accumulator
  putStrLn "═══ 6. Fanout (counter & accumulator) ═══" >>
  (let r1 = stepShared fanned "tick" in
   let o1 = proj₂ r1 in
   putStrLn ("  fanout(\"tick\") → (" ++s proj₁ o1 ++s ", " ++s proj₂ o1 ++s ")") >>
   let r2 = stepShared (proj₁ r1) "tock" in
   let o2 = proj₂ r2 in
   putStrLn ("  fanout(\"tock\") → (" ++s proj₁ o2 ++s ", " ++s proj₂ o2 ++s ")")) >>
  putStrLn "" >>

  -- 7. Parallel: counter *** accumulator
  putStrLn "═══ 7. Parallel (counter ***shared accumulator) ═══" >>
  (let r1 = stepShared parallel ("go" , "aaa") in
   let o1 = proj₂ r1 in
   putStrLn ("  par(\"go\",\"aaa\") → (" ++s proj₁ o1 ++s ", " ++s proj₂ o1 ++s ")") >>
   let r2 = stepShared (proj₁ r1) ("go" , "bbb") in
   let o2 = proj₂ r2 in
   putStrLn ("  par(\"go\",\"bbb\") → (" ++s proj₁ o2 ++s ", " ++s proj₂ o2 ++s ")")) >>
  putStrLn "" >>

  -- 8. Registry lookup
  putStrLn "═══ 8. Registry lookup ═══" >>
  putStrLn ("  registry has " ++s show (len registry) ++s " agents") >>
  printLookup "counter" >>
  printLookup "accumulator" >>
  printLookup "pipeline" >>
  printLookup "nonexistent" >>
  putStrLn "" >>

  putStrLn "Done."

  where
    len : {A : Set₁} → List A → Nat
    len [] = zero
    len (_ ∷ xs) = suc (len xs)
