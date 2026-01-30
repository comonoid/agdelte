{-# OPTIONS --without-K --guardedness #-}

-- Research §2: Multi-step Session Execution
--
-- Compiles a Session protocol into a single Agent whose state
-- tracks progress through the protocol steps.
--
-- Key idea: encode "which step we're on" in the Agent state type.
-- A multi-step session (send A (recv B done)) becomes an Agent with:
--   State = Phase × actual-state
--   Phase tracks which protocol step is active
--
-- Two approaches implemented:
-- 1. SessionRunner: IO-based step-by-step execution
-- 2. SessionPipeline: compile session steps into Agent pipeline via _>>>_

module Agdelte.Concurrent.SessionExec where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; const)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring using (_>>>_)
open import Agdelte.Concurrent.Session

------------------------------------------------------------------------
-- Phase: tracks progress through a session protocol
------------------------------------------------------------------------

-- For a session like: recv A (send B (recv C done))
-- Phase tracks: step 0 = recv A, step 1 = send B, step 2 = recv C, step 3 = done

-- Count steps in a session
sessionSteps : Session → Nat
sessionSteps (send _ s) = suc (sessionSteps s)
sessionSteps (recv _ s) = suc (sessionSteps s)
sessionSteps (offer s₁ s₂) = suc (sessionSteps s₁)  -- follow left branch for counting
sessionSteps (choose s₁ s₂) = suc (sessionSteps s₁)
sessionSteps done = zero

------------------------------------------------------------------------
-- SessionRunner: IO-based step-by-step executor
------------------------------------------------------------------------

-- A SessionRunner executes a session protocol step by step.
-- Each step processes one send/recv operation.
-- State is threaded through all steps.

-- For ReqResp (recv Req (send Resp done)):
--   Step 1: receive Req input
--   Step 2: produce Resp output
--
-- The runner encodes this as an Agent with phased state.

-- Phase-indexed state: which step of the protocol we're executing
data Phase : Set where
  waiting    : Phase    -- waiting for input
  processing : Phase    -- processing / producing output
  completed  : Phase    -- protocol done

record SessionRunner (S : Set) : Set where
  field
    initState : S
    initPhase : Phase

open SessionRunner public

------------------------------------------------------------------------
-- Compile ReqResp session to phased Agent
------------------------------------------------------------------------

-- Most common pattern: recv → process → send → done
-- Compile to a single Agent with (Phase × S) state.

reqRespAgent : ∀ {Req Resp S : Set} →
               S →                       -- initial state
               (S → Req → S × Resp) →    -- process: state + request → new state + response
               Agent (Phase × S) String String
reqRespAgent {Req} {Resp} s₀ process = record
  { state   = waiting , s₀
  ; observe = observeF
  ; step    = stepF
  }
  where
    observeF : Phase × _ → String
    observeF (waiting , _)    = "waiting"
    observeF (processing , _) = "processing"
    observeF (completed , _)  = "completed"

    stepF : Phase × _ → String → Phase × _
    stepF (waiting , s) input = processing , s     -- received input, now processing
    stepF (processing , s) _ = completed , s       -- done processing
    stepF (completed , s) _  = completed , s       -- stay done

------------------------------------------------------------------------
-- Pipeline: compile multi-step session via _>>>_
------------------------------------------------------------------------

-- Each protocol step becomes a small Agent.
-- Pipeline composes them: step1 >>> step2 >>> step3

-- A "receive" step: accepts input, passes it through
recvAgent : Agent String String String
recvAgent = mkAgent "" id (λ _ input → input)

-- A "send" step: transforms input to output
sendAgent : (String → String) → Agent String String String
sendAgent f = mkAgent "" f (λ _ input → input)

-- A "process" step: applies a function to state
processAgent : (String → String) → Agent String String String
processAgent f = mkAgent "" f (λ s input → f input)

-- Example: ReqResp pipeline
-- recv >>> process >>> send
reqRespPipeline : (String → String) → Agent (String × String) String String
reqRespPipeline f = recvAgent >>> sendAgent f

------------------------------------------------------------------------
-- Multi-step pipeline builder
------------------------------------------------------------------------

-- Build a pipeline from a list of transformations.
-- Each transformation is one protocol step.

-- Two-step: recv then send
twoStep : (String → String) → Agent (String × String) String String
twoStep = reqRespPipeline

-- Three-step: recv then process then send
threeStep : (String → String) → (String → String) →
            Agent (String × (String × String)) String String
threeStep f g = recvAgent >>> (processAgent f >>> sendAgent g)

------------------------------------------------------------------------
-- Session-to-Pipeline compiler
------------------------------------------------------------------------

-- For simple linear sessions (no branching), compile to pipeline.
-- Each send/recv becomes one Agent stage.

-- Compile a linear session into a string-based Agent pipeline.
-- Returns the pipeline Agent with appropriate state nesting.

-- Single step agents for each session primitive
sendStepAgent : Agent String String String
sendStepAgent = mkAgent "" id (λ _ i → i)

recvStepAgent : Agent String String String
recvStepAgent = mkAgent "" id (λ _ i → i)

-- Compile a session into a pipeline (for linear sessions)
-- We compile inductively, building nested (S₁ × S₂) state types.

-- Base case: done → identity agent
doneAgent : Agent String String String
doneAgent = mkAgent "" id (λ s _ → s)

-- Recursive: send/recv → step >>> compile rest
compileSend : ∀ {S} → Agent S String String → Agent (String × S) String String
compileSend rest = sendStepAgent >>> rest

compileRecv : ∀ {S} → Agent S String String → Agent (String × S) String String
compileRecv rest = recvStepAgent >>> rest

------------------------------------------------------------------------
-- Example: echo protocol as pipeline
------------------------------------------------------------------------

-- Echo: recv → send → recv → send → ... (bounded)
-- For N rounds, build: (recv >>> send) >>> (recv >>> send) >>> ...

echoRound : Agent (String × String) String String
echoRound = recvAgent >>> sendAgent id

-- Two rounds of echo
echo2 : Agent ((String × String) × (String × String)) String String
echo2 = echoRound >>> echoRound

-- Three rounds
echo3 : Agent ((String × String) × ((String × String) × (String × String))) String String
echo3 = echoRound >>> echo2

------------------------------------------------------------------------
-- Coroutine: yield/await as Agent step
------------------------------------------------------------------------

-- A coroutine is an Agent that alternates between producing (yield)
-- and consuming (await) values. This is exactly what a session does.

record Coroutine (S : Set) : Set where
  field
    coState : S
    -- Each step: receive input → produce output × update state
    coStep  : S → String → String × S

open Coroutine public

-- Run a coroutine as an Agent
coroutineAgent : ∀ {S} → Coroutine S → Agent S String String
coroutineAgent co = record
  { state   = coState co
  ; observe = λ _ → ""
  ; step    = λ s i → proj₂ (coStep co s i)
  }

-- Coroutine that also observes output
coroutineAgentObs : ∀ {S} → Coroutine S → Agent (S × String) String String
coroutineAgentObs co = record
  { state   = coState co , ""
  ; observe = λ { (_ , out) → out }
  ; step    = λ { (s , _) i →
      let result = coStep co s i
      in proj₂ result , proj₁ result }
  }

------------------------------------------------------------------------
-- Echo coroutine
------------------------------------------------------------------------

-- Simplest coroutine: echo input back as output
echoCo : Coroutine ⊤
echoCo = record
  { coState = tt
  ; coStep  = λ _ input → input , tt
  }

-- Counter coroutine: count received messages
counterCo : Coroutine Nat
counterCo = record
  { coState = zero
  ; coStep  = λ n _ → showNat n , suc n
  }
  where
    showNat : Nat → String
    showNat zero = "0"
    showNat (suc n) = "suc"  -- simplified; full show requires more machinery
