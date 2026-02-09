{-# OPTIONS --without-K #-}

-- Keyboard: demonstration of global keyboard events
-- Arrow keys move the square, Escape resets position
-- Reactive approach: no Virtual DOM, direct bindings

module Keyboard where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Integer.Base using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_)
open import Data.String using (String; _++_)
open import Data.List using ([]; _∷_; [_])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd using (Cmd; ε)
open import Agdelte.Reactive.Node

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

updateModel : Msg → Model → Model
updateModel MoveUp    m = record m { y = y m -ℤ moveStep ; lastKey = "↑" }
updateModel MoveDown  m = record m { y = y m +ℤ moveStep ; lastKey = "↓" }
updateModel MoveLeft  m = record m { x = x m -ℤ moveStep ; lastKey = "←" }
updateModel MoveRight m = record m { x = x m +ℤ moveStep ; lastKey = "→" }
updateModel Reset     m = initialModel

------------------------------------------------------------------------
-- Helpers for display
------------------------------------------------------------------------

showNat : ℕ → String
showNat = Data.Nat.Show.show
  where import Data.Nat.Show

showInt : ℤ → String
showInt (+ n) = showNat n
showInt (-[1+ n ]) = "-" ++ showNat (suc n)

-- Position text
positionStr : Model → String
positionStr m = "Position: (" ++ showInt (x m) ++ ", " ++ showInt (y m) ++ ")"

-- Last key text
lastKeyStr : Model → String
lastKeyStr m = "Last key: " ++ lastKey m

-- Box left style value
boxLeft : Model → String
boxLeft m = showInt (x m) ++ "px"

-- Box top style value
boxTop : Model → String
boxTop m = showInt (y m) ++ "px"

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

keyboardTemplate : Node Model Msg
keyboardTemplate =
  div [ class "keyboard-demo" ]
    ( h1 [] [ text "Keyboard Demo" ]
    ∷ p [] [ bindF positionStr ]   -- auto-updates!
    ∷ p [] [ bindF lastKeyStr ]    -- auto-updates!
    ∷ div
        ( class "box"
        ∷ styles "position" "absolute"
        ∷ styleBind "left" (stringBinding boxLeft)
        ∷ styleBind "top" (stringBinding boxTop)
        ∷ styles "width" "50px"
        ∷ styles "height" "50px"
        ∷ styles "background" "#3b82f6"
        ∷ styles "border-radius" "8px"
        ∷ [])
        []
    ∷ div [ class "instructions" ]
        ( p [] [ text "Use arrow keys to move" ]
        ∷ p [] [ text "Press Escape to reset" ]
        ∷ [] )
    ∷ button (onClick Reset ∷ class "reset-btn" ∷ [])
        [ text "Reset Position" ]
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions: global keyboard events
------------------------------------------------------------------------

subs' : Model → Event Msg
subs' _ = onKeys
  ( ("ArrowUp"    , MoveUp)
  ∷ ("ArrowDown"  , MoveDown)
  ∷ ("ArrowLeft"  , MoveLeft)
  ∷ ("ArrowRight" , MoveRight)
  ∷ ("Escape"     , Reset)
  ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel keyboardTemplate (λ _ _ → ε) subs'
