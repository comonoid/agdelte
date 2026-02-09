{-# OPTIONS --without-K #-}

-- Checkbox: Single checkbox and checkbox groups
-- CSS classes: .agdelte-checkbox, .agdelte-checkbox__input,
--              .agdelte-checkbox__label, .agdelte-checkbox-group

module Agdelte.Html.Controls.Checkbox where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map; any)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Single checkbox
------------------------------------------------------------------------

-- | Single checkbox with label.
-- | lbl: label text
-- | isChecked: extract checked state from model
-- | toggleMsg: message to send when toggled
checkbox : ∀ {M A} → String → (M → Bool) → A → Node M A
checkbox lbl isChecked toggleMsg =
  label ( class "agdelte-checkbox" ∷ [] )
    ( input ( type' "checkbox"
            ∷ class "agdelte-checkbox__input"
            ∷ checkedBind isChecked
            ∷ onChange (λ _ → toggleMsg)
            ∷ [] )
    ∷ span ( class "agdelte-checkbox__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Checkbox with custom ID (for form association)
------------------------------------------------------------------------

-- | Checkbox with explicit ID for form association
checkboxWithId : ∀ {M A} → String → String → (M → Bool) → A → Node M A
checkboxWithId cbId lbl isChecked toggleMsg =
  div ( class "agdelte-checkbox" ∷ [] )
    ( input ( type' "checkbox"
            ∷ id' cbId
            ∷ class "agdelte-checkbox__input"
            ∷ checkedBind isChecked
            ∷ onChange (λ _ → toggleMsg)
            ∷ [] )
    ∷ label ( attr "for" cbId
            ∷ class "agdelte-checkbox__label"
            ∷ [] )
        ( text lbl ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Checkbox group (multiple selection)
------------------------------------------------------------------------

-- Re-use SelectOption from Dropdown
open import Agdelte.Html.Controls.Dropdown using (SelectOption; mkOption; optValue; optLabel)

private
  -- Check if value is in list
  {-# TERMINATING #-}
  elemBy : {V : Set} → (V → V → Bool) → V → List V → Bool
  elemBy _ _ [] = false
  elemBy eq v (x ∷ xs) = if eq v x then true else elemBy eq v xs

-- | Checkbox group for multiple selection.
-- | eqV: equality function for values
-- | getSelected: extract list of selected values from model
-- | toggleMsg: message constructor for toggling a value
-- | options: list of options
checkboxGroup : ∀ {V M A}
              → (V → V → Bool)           -- value equality
              → (M → List V)             -- selected values
              → (V → A)                  -- toggle message
              → List (SelectOption V)
              → Node M A
checkboxGroup {V} {M} {A} eqV getSelected toggleMsg options =
  div ( class "agdelte-checkbox-group" ∷ attr "role" "group" ∷ [] )
    (map renderOption options)
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

    renderOption : SelectOption V → Node M A
    renderOption opt =
      label ( class "agdelte-checkbox" ∷ [] )
        ( input ( type' "checkbox"
                ∷ class "agdelte-checkbox__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if elemBy eqV (optValue opt) (getSelected m)
                           then "true" else "")
                    eqStr)
                ∷ onChange (λ _ → toggleMsg (optValue opt))
                ∷ [] )
        ∷ span ( class "agdelte-checkbox__label" ∷ [] )
            ( text (optLabel opt) ∷ [] )
        ∷ [] )

------------------------------------------------------------------------
-- Checkbox group with index-based selection
------------------------------------------------------------------------

-- | Checkbox group using indices (simpler when you don't need typed values)
checkboxGroupIdx : ∀ {M A}
                 → (M → List ℕ)          -- selected indices
                 → (ℕ → A)               -- toggle message
                 → List String           -- option labels
                 → Node M A
checkboxGroupIdx {M} {A} getSelected toggleMsg labels =
  div ( class "agdelte-checkbox-group" ∷ attr "role" "group" ∷ [] )
    (renderOptions 0 labels)
  where
    open import Data.Nat using (_≡ᵇ_)

    {-# TERMINATING #-}
    elemℕ : ℕ → List ℕ → Bool
    elemℕ _ [] = false
    elemℕ n (x ∷ xs) = if n ≡ᵇ x then true else elemℕ n xs

    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

    renderOption : ℕ → String → Node M A
    renderOption idx lbl =
      label ( class "agdelte-checkbox" ∷ [] )
        ( input ( type' "checkbox"
                ∷ class "agdelte-checkbox__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if elemℕ idx (getSelected m) then "true" else "")
                    eqStr)
                ∷ onChange (λ _ → toggleMsg idx)
                ∷ [] )
        ∷ span ( class "agdelte-checkbox__label" ∷ [] )
            ( text lbl ∷ [] )
        ∷ [] )

    {-# TERMINATING #-}
    renderOptions : ℕ → List String → List (Node M A)
    renderOptions _ [] = []
    renderOptions idx (lbl ∷ rest) =
      renderOption idx lbl ∷ renderOptions (ℕ.suc idx) rest
      where open import Data.Nat as ℕ using (suc)
