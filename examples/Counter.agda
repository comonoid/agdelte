{-# OPTIONS --without-K #-}

-- Counter: simplest example of Agdelte application (Reactive, without Virtual DOM)

module Counter where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List using ([]; _∷_; [_])

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

Model : Set
Model = ℕ

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

updateModel : Msg → Model → Model
updateModel Increment n = suc n
updateModel Decrement zero = zero
updateModel Decrement (suc n) = n
updateModel Reset _ = 0

------------------------------------------------------------------------
-- Template: declarative, with reactive bindings
------------------------------------------------------------------------

counterTemplate : Node Model Msg
counterTemplate =
  div [ class "counter" ]
    ( h1 [] [ text "Agdelte Counter" ]
    ∷ div [ class "display" ] [ bindF show ]   -- auto-updates!
    ∷ div [ class "buttons" ]
        ( button (onClick Decrement ∷ class "btn" ∷ []) [ text "-" ]
        ∷ button (onClick Reset ∷ class "btn" ∷ []) [ text "Reset" ]
        ∷ button (onClick Increment ∷ class "btn" ∷ []) [ text "+" ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

counterApp : ReactiveApp Model Msg
counterApp = mkReactiveApp 0 updateModel counterTemplate

app : ReactiveApp Model Msg
app = counterApp
