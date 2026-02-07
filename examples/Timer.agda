{-# OPTIONS --without-K #-}

-- Timer: example with external events (interval)
-- Reactive approach: no Virtual DOM, direct bindings

module Timer where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_; length)
open import Data.List using ([]; _∷_; [_])

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    tenths  : ℕ    -- Tenths of a second
    running : Bool

open Model public

initialModel : Model
initialModel = mkModel 0 false

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Tick      : Msg
  Toggle    : Msg
  Reset     : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Tick m = if running m then record m { tenths = suc (tenths m) } else m
updateModel Toggle m = record m { running = not (running m) }
updateModel Reset m = record m { tenths = 0 ; running = false }

------------------------------------------------------------------------
-- Formatting
------------------------------------------------------------------------

formatTime : ℕ → String
formatTime t =
  let totalSecs = t / 10
      tenthsPart = t % 10
      mins = totalSecs / 60
      secs = totalSecs % 60
  in pad (show mins) ++ ":" ++ pad (show secs) ++ "." ++ show tenthsPart
  where
    open import Data.Nat.DivMod using (_/_; _%_)
    open import Data.Nat using (_<ᵇ_)

    pad : String → String
    pad s = if length s <ᵇ 2 then "0" ++ s else s

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

-- Button text depends on running state
buttonText : Model → String
buttonText m = if running m then "Pause" else "Start"

timerTemplate : Node Model Msg
timerTemplate =
  div [ class "timer" ]
    ( h1 [] [ text "Agdelte Timer" ]
    ∷ div (class "display" ∷ styles "font-size" "48px" ∷ [])
        [ bindF (formatTime ∘ tenths) ]  -- auto-updates!
    ∷ div [ class "controls" ]
        ( button (onClick Toggle ∷ class "btn" ∷ [])
            [ bindF buttonText ]  -- auto-updates!
        ∷ button (onClick Reset ∷ class "btn" ∷ [])
            [ text "Reset" ]
        ∷ [] )
    ∷ [] )
  where open import Function using (_∘_)

------------------------------------------------------------------------
-- Subscriptions: interval when timer is running
------------------------------------------------------------------------

subs : Model → Event Msg
subs m = if running m
         then interval 100 Tick  -- Every 0.1 seconds
         else never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel timerTemplate

-- subs is exported separately (see above)
