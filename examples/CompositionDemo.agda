{-# OPTIONS --without-K #-}

-- CompositionDemo: демонстрация композиции приложений
-- Два независимых Counter работают параллельно
-- Reactive approach: no Virtual DOM, direct bindings

module CompositionDemo where

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Counter Component (переиспользуемый)
------------------------------------------------------------------------

module CounterComponent where
  -- Model
  record CounterModel : Set where
    constructor mkModel
    field
      count : ℕ
      name  : String

  open CounterModel public

  -- Messages
  data CounterMsg : Set where
    Inc   : CounterMsg
    Dec   : CounterMsg
    Reset : CounterMsg

  -- Update
  updateCounter : CounterMsg → CounterModel → CounterModel
  updateCounter Inc m = record m { count = suc (count m) }
  updateCounter Dec m = record m { count = pred (count m) }
  updateCounter Reset m = record m { count = zero }

  -- Helpers
  countText : CounterModel → String
  countText m = show (count m)

  -- Template
  counterTemplate : Node CounterModel CounterMsg
  counterTemplate =
    div [ class "counter-component" ]
      ( h3 [] [ bindF name ]  -- counter name
      ∷ div [ class "counter-controls" ]
          ( button (onClick Dec ∷ class "btn" ∷ []) [ text "-" ]
          ∷ span [ class "count" ] [ bindF countText ]  -- auto-updates!
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
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  LeftMsg  : CounterMsg → Msg
  RightMsg : CounterMsg → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel (LeftMsg cm) (l , r) = updateCounter cm l , r
updateModel (RightMsg cm) (l , r) = l , updateCounter cm r

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

totalCountText : Model → String
totalCountText (l , r) = "Total: " ++ show (counterCount l + counterCount r)

------------------------------------------------------------------------
-- Template: composed with focusNode
------------------------------------------------------------------------

-- Map counter messages to parent messages
mapLeftMsg : Msg → Msg
mapLeftMsg = λ m → m  -- identity, already wrapped

mapRightMsg : Msg → Msg
mapRightMsg = λ m → m  -- identity, already wrapped

-- Unfortunately, focusNode doesn't transform messages (only extracts model part)
-- So for proper composition with message transformation, we need a different approach
-- For now, we'll inline the counter templates with message wrapping

-- Left counter helper functions
leftCountText : Model → String
leftCountText (l , _) = countText l

leftName : Model → String
leftName (l , _) = CounterComponent.name l

-- Right counter helper functions
rightCountText : Model → String
rightCountText (_ , r) = countText r

rightName : Model → String
rightName (_ , r) = CounterComponent.name r

compositionTemplate : Node Model Msg
compositionTemplate =
  div [ class "composition-demo" ]
    ( h1 [] [ text "Composition Demo" ]
    ∷ p [ class "description" ]
        [ text "Two independent counters with shared total" ]
    ∷ p [ class "total" ]
        [ bindF totalCountText ]  -- auto-updates!

    ∷ div [ class "counters-container" ]
        -- Left counter (inline with LeftMsg wrapping)
        ( div [ class "counter-component" ]
            ( h3 [] [ bindF leftName ]
            ∷ div [ class "counter-controls" ]
                ( button (onClick (LeftMsg CounterComponent.Dec) ∷ class "btn" ∷ []) [ text "-" ]
                ∷ span [ class "count" ] [ bindF leftCountText ]  -- auto-updates!
                ∷ button (onClick (LeftMsg CounterComponent.Inc) ∷ class "btn" ∷ []) [ text "+" ]
                ∷ button (onClick (LeftMsg CounterComponent.Reset) ∷ class "reset-btn" ∷ []) [ text "Reset" ]
                ∷ [] )
            ∷ [] )

        -- Right counter (inline with RightMsg wrapping)
        ∷ div [ class "counter-component" ]
            ( h3 [] [ bindF rightName ]
            ∷ div [ class "counter-controls" ]
                ( button (onClick (RightMsg CounterComponent.Dec) ∷ class "btn" ∷ []) [ text "-" ]
                ∷ span [ class "count" ] [ bindF rightCountText ]  -- auto-updates!
                ∷ button (onClick (RightMsg CounterComponent.Inc) ∷ class "btn" ∷ []) [ text "+" ]
                ∷ button (onClick (RightMsg CounterComponent.Reset) ∷ class "reset-btn" ∷ []) [ text "Reset" ]
                ∷ [] )
            ∷ [] )
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel compositionTemplate
