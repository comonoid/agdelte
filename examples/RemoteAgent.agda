{-# OPTIONS --without-K #-}

-- RemoteAgent: browser client talking to Haskell Agent server
-- Demonstrates Cmd integration: HTTP requests fired from update
-- Agent runs on port 3000, browser controls it via fetch

module RemoteAgent where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data Status : Set where
  Idle    : Status
  Polling : Status
  Stepping : Status
  Done    : String → Status
  Error   : String → Status

record Model : Set where
  constructor mkModel
  field
    count     : String
    status    : Status
    stepCount : ℕ

open Model public

initialModel : Model
initialModel = mkModel "?" Idle zero

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  PollState   : Msg
  StepAgent   : Msg
  GotState    : String → Msg
  GotStep     : String → Msg
  GotError    : String → Msg

------------------------------------------------------------------------
-- Server URL
------------------------------------------------------------------------

serverUrl : String
serverUrl = "http://127.0.0.1:3000"

------------------------------------------------------------------------
-- Update (pure state transition)
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel PollState m = record m { status = Polling }
updateModel StepAgent m = record m { status = Stepping ; stepCount = suc (stepCount m) }
updateModel (GotState s) m = record m { count = s ; status = Done s }
updateModel (GotStep s) m = record m { count = s ; status = Done s }
updateModel (GotError e) m = record m { status = Error e }

------------------------------------------------------------------------
-- Cmd (side effects triggered by messages)
------------------------------------------------------------------------

cmd : Msg → Model → Cmd Msg
cmd PollState _ = agentQuery (serverUrl ++ "/state") GotState GotError
cmd StepAgent _ = agentStep! (serverUrl ++ "/step") GotStep GotError
cmd _ _ = ε

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

isBusy : Model → Bool
isBusy m with status m
... | Polling  = true
... | Stepping = true
... | _        = false

statusText : Model → String
statusText m with status m
... | Idle       = "Click Poll to connect"
... | Polling    = "Polling server..."
... | Stepping   = "Stepping agent..."
... | Done s     = "Server count: " ++ s
... | Error e    = "Error: " ++ e

stepCountText : Model → String
stepCountText m = "Steps sent: " ++ show (stepCount m)

pollBtnText : Model → String
pollBtnText m = if isBusy m then "..." else "Poll State"

stepBtnText : Model → String
stepBtnText m = if isBusy m then "..." else "Step Agent"

countText : Model → String
countText m = "Agent state: " ++ count m

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

remoteTemplate : Node Model Msg
remoteTemplate =
  div [ class "remote-agent-demo" ]
    ( h1 [] [ text "Remote Agent" ]
    ∷ p  [] [ text "Browser ↔ Haskell Agent on port 3000" ]
    ∷ p  [ class "count" ] [ bindF countText ]
    ∷ p  [ class "status" ] [ bindF statusText ]
    ∷ p  [] [ bindF stepCountText ]
    ∷ div [ class "controls" ]
        ( button (onClick PollState ∷ class "poll-btn" ∷ disabledBind isBusy ∷ [])
            [ bindF pollBtnText ]
        ∷ button (onClick StepAgent ∷ class "step-btn" ∷ disabledBind isBusy ∷ [])
            [ bindF stepBtnText ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel remoteTemplate

-- cmd and subs are exported separately (see above)
-- Runtime picks them up: cmd : Msg → Model → Cmd Msg
