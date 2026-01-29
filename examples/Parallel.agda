{-# OPTIONS --without-K #-}

-- Parallel: demonstrates workerWithProgress, parallel, race combinators
-- Three demos in one:
--   1. Worker with progress reporting (fibonacci)
--   2. Parallel HTTP requests (fetch two endpoints)
--   3. Race: HTTP request with timeout

module Parallel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const; id)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data Demo : Set where
  ProgressDemo  : Demo
  ParallelDemo  : Demo
  RaceDemo      : Demo

record Model : Set where
  constructor mkModel
  field
    demo       : Demo
    -- Progress demo
    progress   : String
    result     : String
    computing  : Bool
    -- Parallel demo
    results    : String
    fetching   : Bool
    -- Race demo
    raceResult : String
    racing     : Bool

open Model public

initModel : Model
initModel = mkModel ProgressDemo "" "" false "" false "" false

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  -- Navigation
  ShowProgress  : Msg
  ShowParallel  : Msg
  ShowRace      : Msg
  -- Progress demo
  StartCompute  : Msg
  GotProgress   : String → Msg
  GotResult     : String → Msg
  GotError      : String → Msg
  -- Parallel demo
  StartFetch    : Msg
  GotAll        : List String → Msg
  FetchError    : String → Msg
  -- Race demo
  StartRace     : Msg
  RaceWon       : String → Msg
  RaceTimeout   : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

showResults : List String → String
showResults [] = "(empty)"
showResults (x ∷ []) = x
showResults (x ∷ xs) = x ++ ", " ++ showResults xs

updateModel : Msg → Model → Model
updateModel ShowProgress  m = record m { demo = ProgressDemo }
updateModel ShowParallel  m = record m { demo = ParallelDemo }
updateModel ShowRace      m = record m { demo = RaceDemo }
updateModel StartCompute  m = record m { computing = true ; progress = "0%" ; result = "" }
updateModel (GotProgress s) m = record m { progress = s ++ "%" }
updateModel (GotResult s)   m = record m { computing = false ; result = s ; progress = "100%" }
updateModel (GotError e)    m = record m { computing = false ; result = "Error: " ++ e }
updateModel StartFetch    m = record m { fetching = true ; results = "" }
updateModel (GotAll xs)   m = record m { fetching = false ; results = show (length xs) ++ " results: " ++ showResults xs }
updateModel (FetchError e) m = record m { fetching = false ; results = "Error: " ++ e }
updateModel StartRace     m = record m { racing = true ; raceResult = "" }
updateModel (RaceWon s)   m = record m { racing = false ; raceResult = "Winner: " ++ s }
updateModel RaceTimeout   m = record m { racing = false ; raceResult = "Timed out!" }

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

progressText : Model → String
progressText m = if computing m then "Progress: " ++ progress m else progress m

resultText : Model → String
resultText m = if computing m then "Computing..." else result m

parallelText : Model → String
parallelText m = if fetching m then "Fetching..." else results m

raceText : Model → String
raceText m = if racing m then "Racing..." else raceResult m

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

parallelTemplate : Node Model Msg
parallelTemplate =
  div [ class "parallel-demo" ]
    ( h1 [] [ text "Concurrency Demos" ]
    ∷ div [ class "nav" ]
        ( button [ onClick ShowProgress ] [ text "Progress" ]
        ∷ button [ onClick ShowParallel ] [ text "Parallel" ]
        ∷ button [ onClick ShowRace ] [ text "Race" ]
        ∷ [] )
    -- Progress demo section
    ∷ div [ class "demo-section" ]
        ( h2 [] [ text "Worker with Progress" ]
        ∷ button [ onClick StartCompute ] [ text "Compute fib(10000)" ]
        ∷ p [] [ bindF progressText ]
        ∷ p [] [ bindF resultText ]
        ∷ [] )
    -- Parallel demo section
    ∷ div [ class "demo-section" ]
        ( h2 [] [ text "Parallel Requests" ]
        ∷ button [ onClick StartFetch ] [ text "Fetch All" ]
        ∷ p [] [ bindF parallelText ]
        ∷ [] )
    -- Race demo section
    ∷ div [ class "demo-section" ]
        ( h2 [] [ text "Race with Timeout" ]
        ∷ button [ onClick StartRace ] [ text "Race!" ]
        ∷ p [] [ bindF raceText ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs : Model → Event Msg
subs m =
  let progSub = if computing m
        then workerWithProgress
               "/runtime/workers/fibonacci-progress.js"
               "10000"
               GotProgress
               GotResult
               GotError
        else never
      parSub = if fetching m
        then parallel
               ( httpGet "/api/users" id (const "")
               ∷ httpGet "/api/posts" id (const "")
               ∷ [] )
               GotAll
        else never
      raceSub = if racing m
        then race
               ( mapE RaceWon (httpGet "/api/data" id (const "error"))
               ∷ timeout 3000 RaceTimeout
               ∷ [] )
        else never
  in merge progSub (merge parSub raceSub)

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel parallelTemplate
