{-# OPTIONS --without-K #-}

-- Worker: Web Worker example
-- Offloads heavy computation (fibonacci) to a background thread
-- Demonstrates structured concurrency: worker terminates on unsubscribe

module Worker where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd using (Cmd; ε)
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data Status : Set where
  Idle       : Status
  Computing  : Status
  Result     : String → Status
  Error      : String → Status

record Model : Set where
  constructor mkModel
  field
    fibInput    : ℕ
    status      : Status
    computeCount : ℕ

open Model public

initialModel : Model
initialModel = mkModel 10 Idle zero

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Increment   : Msg
  Decrement   : Msg
  Compute     : Msg
  GotResult   : String → Msg
  GotError    : String → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Increment m = record m { fibInput = suc (fibInput m) }
updateModel Decrement m = record m { fibInput = pred (fibInput m) }
  where
    pred : ℕ → ℕ
    pred zero    = zero
    pred (suc n) = n
updateModel Compute m = record m
  { status = Computing
  ; computeCount = suc (computeCount m)
  }
updateModel (GotResult s) m = record m { status = Result s }
updateModel (GotError e) m = record m { status = Error e }

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

isComputing : Model → Bool
isComputing m with status m
... | Computing = true
... | _ = false

statusText : Model → String
statusText m with status m
... | Idle = "Ready. Click Compute to start."
... | Computing = "Computing in Web Worker..."
... | Result s = "fib(" ++ show (fibInput m) ++ ") = " ++ s
... | Error e = "Error: " ++ e

inputText : Model → String
inputText m = "N = " ++ show (fibInput m)

countText : Model → String
countText m = "Computations: " ++ show (computeCount m)

buttonLabel : Model → String
buttonLabel m = if isComputing m then "Computing..." else "Compute fib(N)"

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

workerTemplate : Node Model Msg
workerTemplate =
  div [ class "worker-demo" ]
    ( h1 [] [ text "Web Worker Demo" ]
    ∷ p [] [ text "Heavy computation offloaded to a background thread" ]
    ∷ div [ class "controls" ]
        ( button [ onClick Decrement ] [ text "-" ]
        ∷ span [ class "input-value" ] [ bindF inputText ]
        ∷ button [ onClick Increment ] [ text "+" ]
        ∷ [] )
    ∷ button (onClick Compute ∷ class "compute-btn"
             ∷ disabledBind isComputing ∷ [])
        [ bindF buttonLabel ]
    ∷ p [ class "status" ] [ bindF statusText ]
    ∷ p [ class "count" ] [ bindF countText ]
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions: spawn worker when Computing
------------------------------------------------------------------------

subs' : Model → Event Msg
subs' m with status m
... | Computing = worker
    "/runtime/workers/fibonacci.js"
    (show (fibInput m))
    GotResult
    GotError
... | _ = never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel workerTemplate (λ _ _ → ε) subs'
