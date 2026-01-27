{-# OPTIONS --without-K #-}

-- Timer: пример с внешними событиями (interval)

module Timer where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not)
open import Data.String using (String; _++_)
open import Data.List using ([]; _∷_; [_])

open import Agdelte.Core.Event
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events
import Agdelte.App as App

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    tenths  : ℕ    -- Десятые доли секунды
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

update : Msg → Model → Model
update Tick m = if running m then record m { tenths = suc (tenths m) } else m
  where open import Data.Bool using (if_then_else_)
update Toggle m = record m { running = not (running m) }
update Reset m = record m { tenths = 0 }  -- Не останавливает таймер!

------------------------------------------------------------------------
-- View
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
    open import Data.String using (length)
    open import Data.Bool using (if_then_else_)

    pad : String → String
    pad s = if length s <ᵇ 2 then "0" ++ s else s

view : Model → Html Msg
view m =
  div (class "timer" ∷ [])
    ( h1 [] (text "Agdelte Timer" ∷ [])
    ∷ div (class "display" ∷ fontSize "48px" ∷ [])
        (text (formatTime (tenths m)) ∷ [])
    ∷ div (class "controls" ∷ [])
        ( button (onClick Toggle ∷ class "btn" ∷ [])
            (text (if running m then "Pause" else "Start") ∷ [])
        ∷ button (onClick Reset ∷ class "btn" ∷ [])
            (text "Reset" ∷ [])
        ∷ [] )
    ∷ [] )
  where open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- Events: подписка на interval когда таймер запущен
------------------------------------------------------------------------

events : Model → Event Msg
events m = if running m
           then interval 100 Tick  -- Каждые 0.1 секунды
           else never
  where open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

timerApp : App.App Model Msg
timerApp = App.mkApp initialModel update view events
