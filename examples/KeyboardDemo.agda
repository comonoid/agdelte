{-# OPTIONS --without-K #-}

-- KeyboardDemo: демонстрация глобальных событий клавиатуры
-- Стрелки перемещают квадрат, Escape сбрасывает позицию

module KeyboardDemo where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Integer.Base using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_)
open import Data.String using (String; _++_)
open import Data.List using ([]; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const)

-- Используем новый Event из Core (всё включено!)
open import Agdelte.Core.Event
import Agdelte.App as App
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events hiding (onEnter; onEscape)

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    x : ℤ
    y : ℤ
    lastKey : String

open Model public

initialModel : Model
initialModel = mkModel (+ 225) (+ 215) "Press arrow keys!"

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  MoveUp    : Msg
  MoveDown  : Msg
  MoveLeft  : Msg
  MoveRight : Msg
  Reset     : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

moveStep : ℤ
moveStep = + 20

update : Msg → Model → Model
update MoveUp    m = record m { y = y m -ℤ moveStep ; lastKey = "↑" }
update MoveDown  m = record m { y = y m +ℤ moveStep ; lastKey = "↓" }
update MoveLeft  m = record m { x = x m -ℤ moveStep ; lastKey = "←" }
update MoveRight m = record m { x = x m +ℤ moveStep ; lastKey = "→" }
update Reset     m = initialModel

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

showNat : ℕ → String
showNat = Data.Nat.Show.show
  where import Data.Nat.Show

showInt : ℤ → String
showInt (+ n) = showNat n
showInt (-[1+ n ]) = "-" ++ showNat (suc n)

view : Model → Html Msg
view m = div (class "keyboard-demo" ∷ [])
  ( h1 [] (text "Keyboard Demo" ∷ [])
  ∷ p [] (text ("Position: (" ++ showInt (x m) ++ ", " ++ showInt (y m) ++ ")") ∷ [])
  ∷ p [] (text ("Last key: " ++ lastKey m) ∷ [])
  ∷ div
      ( class "box"
      ∷ styles "position" "absolute"
      ∷ styles "left" (showInt (x m) ++ "px")
      ∷ styles "top" (showInt (y m) ++ "px")
      ∷ styles "width" "50px"
      ∷ styles "height" "50px"
      ∷ styles "background" "#3b82f6"
      ∷ styles "border-radius" "8px"
      ∷ [])
      []
  ∷ div (class "instructions" ∷ [])
      ( p [] (text "Use arrow keys to move" ∷ [])
      ∷ p [] (text "Press Escape to reset" ∷ [])
      ∷ [])
  ∷ button (onClick Reset ∷ class "reset-btn" ∷ [])
      (text "Reset Position" ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Events (один listener для всех клавиш — эффективно!)
------------------------------------------------------------------------

events : Model → Event Msg
events _ = onKeys
  ( ("ArrowUp"    , MoveUp)
  ∷ ("ArrowDown"  , MoveDown)
  ∷ ("ArrowLeft"  , MoveLeft)
  ∷ ("ArrowRight" , MoveRight)
  ∷ ("Escape"     , Reset)
  ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : App.App Model Msg
app = App.mkApp initialModel update view events
