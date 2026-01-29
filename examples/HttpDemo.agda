{-# OPTIONS --without-K #-}

-- HttpDemo: демонстрация HTTP запросов
-- Загружает данные с публичного API
-- Reactive approach: no Virtual DOM, direct bindings

module HttpDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_]) renaming (_++_ to _++ˡ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data Status : Set where
  Idle    : Status
  Loading : Status
  Success : String → Status
  Error   : String → Status

record Model : Set where
  constructor mkModel
  field
    status    : Status
    fetchCount : ℕ

open Model public

initialModel : Model
initialModel = mkModel Idle zero

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  FetchData   : Msg
  GotData     : String → Msg
  GotError    : String → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel FetchData m = record m { status = Loading ; fetchCount = suc (fetchCount m) }
updateModel (GotData resp) m = record m { status = Success resp }
updateModel (GotError err) m = record m { status = Error err }

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

isLoading : Model → Bool
isLoading m with status m
... | Loading = true
... | _ = false

statusText : Status → String
statusText Idle = "Ready to fetch"
statusText Loading = "Loading..."
statusText (Success s) = "Response: " ++ s
statusText (Error e) = "Error: " ++ e

-- Status text from model
modelStatusText : Model → String
modelStatusText m = statusText (status m)

-- Fetch count text
fetchCountText : Model → String
fetchCountText m = "Fetch count: " ++ show (fetchCount m)

-- Button text
buttonText : Model → String
buttonText m = if isLoading m then "Loading..." else "Fetch Data"

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

httpTemplate : Node Model Msg
httpTemplate =
  div [ class "http-demo" ]
    ( h1 [] [ text "HTTP Demo" ]
    ∷ p [] [ bindF fetchCountText ]    -- auto-updates!
    ∷ p [ class "status" ] [ bindF modelStatusText ]  -- auto-updates!
    ∷ button (onClick FetchData ∷ class "fetch-btn" ∷ disabledBind isLoading ∷ [])
        [ bindF buttonText ]
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions: HTTP requests when Loading
------------------------------------------------------------------------

subs : Model → Event Msg
subs m with status m
... | Loading = httpGet
    "https://jsonplaceholder.typicode.com/posts/1"
    GotData
    GotError
... | _ = never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel httpTemplate

-- subs is exported separately (see above)
