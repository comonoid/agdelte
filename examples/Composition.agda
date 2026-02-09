{-# OPTIONS --without-K #-}

-- Composition: Widget composition via Lens + zoomNode
-- Two independent Counter components, composed with lenses
-- No manual message wrapping or binding duplication!

module Composition where

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node
open import Agdelte.Reactive.Lens

------------------------------------------------------------------------
-- Counter Component (reusable)
------------------------------------------------------------------------

module CounterComponent where
  record CounterModel : Set where
    constructor mkModel
    field
      count : ℕ
      name  : String

  open CounterModel public

  data CounterMsg : Set where
    Inc   : CounterMsg
    Dec   : CounterMsg
    Reset : CounterMsg

  updateCounter : CounterMsg → CounterModel → CounterModel
  updateCounter Inc m = record m { count = suc (count m) }
  updateCounter Dec m = record m { count = pred (count m) }
  updateCounter Reset m = record m { count = zero }

  countText : CounterModel → String
  countText m = show (count m)

  -- Component template: works with its own Model and Msg
  counterTemplate : Node CounterModel CounterMsg
  counterTemplate =
    div [ class "counter-component" ]
      ( h3 [] [ bindF name ]
      ∷ div [ class "counter-controls" ]
          ( button (onClick Dec ∷ class "btn" ∷ []) [ text "-" ]
          ∷ span [ class "count" ] [ bindF countText ]
          ∷ button (onClick Inc ∷ class "btn" ∷ []) [ text "+" ]
          ∷ button (onClick Reset ∷ class "reset-btn" ∷ []) [ text "Reset" ]
          ∷ [] )
      ∷ [] )

open CounterComponent using (CounterModel; CounterMsg; counterTemplate; updateCounter; countText)
  renaming (mkModel to mkCounterModel; count to counterCount; name to counterName)

------------------------------------------------------------------------
-- Composed Model: Two Counters
------------------------------------------------------------------------

Model : Set
Model = CounterModel × CounterModel

initialModel : Model
initialModel = mkCounterModel 0 "Left Counter" , mkCounterModel 10 "Right Counter"

------------------------------------------------------------------------
-- Messages (wrapping child messages)
------------------------------------------------------------------------

data Msg : Set where
  LeftMsg  : CounterMsg → Msg
  RightMsg : CounterMsg → Msg

------------------------------------------------------------------------
-- Update (using Lens.modify!)
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel (LeftMsg cm) m = modify fstLens (updateCounter cm) m
updateModel (RightMsg cm) m = modify sndLens (updateCounter cm) m

------------------------------------------------------------------------
-- Template: composed with zoomNode!
------------------------------------------------------------------------

totalCountText : Model → String
totalCountText (l , r) = "Total: " ++ show (counterCount l + counterCount r)

compositionTemplate : Node Model Msg
compositionTemplate =
  div [ class "composition-demo" ]
    ( h1 [] [ text "Composition Demo" ]
    ∷ p [ class "description" ]
        [ text "Two independent counters with shared total" ]
    ∷ p [ class "total" ]
        [ bindF totalCountText ]

    ∷ div [ class "counters-container" ]
        -- Left counter: zoom into fst, wrap messages with LeftMsg
        ( zoomNode proj₁ LeftMsg counterTemplate
        -- Right counter: zoom into snd, wrap messages with RightMsg
        ∷ zoomNode proj₂ RightMsg counterTemplate
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = simpleApp initialModel updateModel compositionTemplate
