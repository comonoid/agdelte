{-# OPTIONS --without-K #-}

-- Keyboard convenience constructors for Event.
-- Re-exported by Agdelte.Core.Event for backward compatibility.

module Agdelte.Core.Event.Keyboard where

open import Data.String using (String)
open import Data.Bool using (Bool; if_then_else_; _∧_)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Event.Core using
  ( Event; KeyboardEvent; key; code; ctrl; alt; shift; meta
  ; onKeyDown; onKeyUp
  )

private
  variable
    A : Set

  lookupKey : {A : Set} → String → List (String × A) → Maybe A
  lookupKey _ []              = nothing
  lookupKey k ((k' , v) ∷ rest) =
    if primStringEquality k k' then just v else lookupKey k rest

------------------------------------------------------------------------
-- Keyboard convenience constructors
------------------------------------------------------------------------

onKey : String → A → Event A
onKey k msg = onKeyDown (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

onKeys : List (String × A) → Event A
onKeys pairs = onKeyDown (λ e → lookupKey (KeyboardEvent.key e) pairs)

onKeyWhen : (KeyboardEvent → Bool) → A → Event A
onKeyWhen pred msg = onKeyDown (λ e → if pred e then just msg else nothing)

onCtrlKey : String → A → Event A
onCtrlKey k msg = onKeyWhen (λ e → ctrl e ∧ primStringEquality k (key e)) msg

onAltKey : String → A → Event A
onAltKey k msg = onKeyWhen (λ e → alt e ∧ primStringEquality k (key e)) msg

onShiftKey : String → A → Event A
onShiftKey k msg = onKeyWhen (λ e → shift e ∧ primStringEquality k (key e)) msg

onMetaKey : String → A → Event A
onMetaKey k msg = onKeyWhen (λ e → meta e ∧ primStringEquality k (key e)) msg

onArrowUp : A → Event A
onArrowUp msg = onKey "ArrowUp" msg

onArrowDown : A → Event A
onArrowDown msg = onKey "ArrowDown" msg

onArrowLeft : A → Event A
onArrowLeft msg = onKey "ArrowLeft" msg

onArrowRight : A → Event A
onArrowRight msg = onKey "ArrowRight" msg

onEnter : A → Event A
onEnter msg = onKey "Enter" msg

onEscape : A → Event A
onEscape msg = onKey "Escape" msg

onSpace : A → Event A
onSpace msg = onKey " " msg

------------------------------------------------------------------------
-- KeyUp helpers
------------------------------------------------------------------------

onKeyReleased : String → A → Event A
onKeyReleased k msg = onKeyUp (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

onKeysUp : List (String × A) → Event A
onKeysUp pairs = onKeyUp (λ e → lookupKey (KeyboardEvent.key e) pairs)

onKeyUpWhen : (KeyboardEvent → Bool) → A → Event A
onKeyUpWhen pred msg = onKeyUp (λ e → if pred e then just msg else nothing)
