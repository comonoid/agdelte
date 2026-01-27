{-# OPTIONS --without-K #-}

-- HttpDemo: демонстрация HTTP запросов
-- Загружает данные с публичного API

module HttpDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ˡ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
import Agdelte.App as App
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events

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

update : Msg → Model → Model
update FetchData m = record m { status = Loading ; fetchCount = suc (fetchCount m) }
update (GotData resp) m = record m { status = Success resp }
update (GotError err) m = record m { status = Error err }

------------------------------------------------------------------------
-- View
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

buttonAttrs : Model → List (Attr Msg)
buttonAttrs m = onClick FetchData ∷ class "fetch-btn" ∷ []
  ++ˡ (if isLoading m then disabled ∷ [] else [])

view : Model → Html Msg
view m = div (class "http-demo" ∷ [])
  ( h1 [] (text "HTTP Demo" ∷ [])
  ∷ p [] (text ("Fetch count: " ++ show (fetchCount m)) ∷ [])
  ∷ p (class "status" ∷ []) (text (statusText (status m)) ∷ [])
  ∷ button (buttonAttrs m)
      (text (if isLoading m then "Loading..." else "Fetch Data") ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Events (подписки на HTTP)
------------------------------------------------------------------------

events : Model → Event Msg
events m with status m
... | Loading = httpGet
    "https://jsonplaceholder.typicode.com/posts/1"
    GotData
    GotError
... | _ = never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : App.App Model Msg
app = App.mkApp initialModel update view events
