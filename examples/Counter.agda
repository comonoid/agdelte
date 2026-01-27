{-# OPTIONS --without-K #-}

-- Counter: простейший пример приложения Agdelte

module Counter where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.String using (String)
open import Data.List using ([]; _∷_; [_])
open import Function using (const)

open import Agdelte.Core.Event
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events
import Agdelte.App as App

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

Model : Set
Model = ℕ

initialModel : Model
initialModel = 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Increment : Msg
  Decrement : Msg
  Reset     : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

update : Msg → Model → Model
update Increment n = suc n
update Decrement zero = zero
update Decrement (suc n) = n
update Reset _ = 0

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

view : Model → Html Msg
view n =
  div (class "counter" ∷ [])
    ( h1 [] (text "Agdelte Counter" ∷ [])
    ∷ div (class "display" ∷ []) (text (show n) ∷ [])
    ∷ div (class "buttons" ∷ [])
        ( button (onClick Decrement ∷ class "btn" ∷ []) (text "-" ∷ [])
        ∷ button (onClick Reset ∷ class "btn" ∷ []) (text "Reset" ∷ [])
        ∷ button (onClick Increment ∷ class "btn" ∷ []) (text "+" ∷ [])
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Events (нет внешних событий)
------------------------------------------------------------------------

events : Model → Event Msg
events = const never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

counterApp : App.App Model Msg
counterApp = App.mkApp initialModel update view events

-- Или используя simpleApp:
-- counterApp = App.simpleApp initialModel update view
