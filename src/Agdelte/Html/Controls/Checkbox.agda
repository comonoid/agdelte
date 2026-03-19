{-# OPTIONS --without-K #-}

-- Checkbox: Single checkbox and checkbox groups
-- CSS classes: .agdelte-checkbox, .agdelte-checkbox__input,
--              .agdelte-checkbox__label, .agdelte-checkbox-group

module Agdelte.Html.Controls.Checkbox where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map; any)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; case_of_)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)

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
            ∷ attrBind "aria-checked" (mkBinding
                (λ m → if isChecked m then "true" else "false")
                eqStr)
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
            ∷ attrBind "aria-checked" (mkBinding
                (λ m → if isChecked m then "true" else "false")
                eqStr)
            ∷ onChange (λ _ → toggleMsg)
            ∷ [] )
    ∷ label ( attr "for" cbId
            ∷ class "agdelte-checkbox__label"
            ∷ [] )
        ( text lbl ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Checkbox with indeterminate state
------------------------------------------------------------------------

-- | Checkbox with tri-state: Nothing = indeterminate, Just true = checked, Just false = unchecked.
-- | The visual indeterminate state uses the CSS class .agdelte-checkbox--indeterminate
-- | with a dash/minus icon via ::before pseudo-element.
checkboxIndeterminate : ∀ {M A} → String → (M → Maybe Bool) → A → Node M A
checkboxIndeterminate lbl getState toggleMsg =
  label ( classBind (λ m → case getState m of λ where
              nothing → "agdelte-checkbox agdelte-checkbox--indeterminate"
              (just _) → "agdelte-checkbox")
        ∷ [] )
    ( input ( type' "checkbox"
            ∷ class "agdelte-checkbox__input"
            ∷ checkedBind (λ m → case getState m of λ where
                nothing → false
                (just b) → b)
            ∷ attrBind "aria-checked" (mkBinding
                (λ m → case getState m of λ where
                    nothing → "mixed"
                    (just true) → "true"
                    (just false) → "false")
                eqStr)
            ∷ onChange (λ _ → toggleMsg)
            ∷ [] )
    ∷ span ( class "agdelte-checkbox__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ [] )
  where
    open import Data.Maybe using (Maybe; just; nothing)

------------------------------------------------------------------------
-- Checkbox group (multiple selection)
------------------------------------------------------------------------

-- Re-use SelectOption from Dropdown
open import Agdelte.Html.Controls.Dropdown using (SelectOption; mkOption; optValue; optLabel)

private
  -- Check if value is in list
  elemBy : {V : Set} → (V → V → Bool) → V → List V → Bool
  elemBy _ _ [] = false
  elemBy eq v (x ∷ xs) with eq v x
  ... | true  = true
  ... | false = elemBy eq v xs

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
    open import Agdelte.Html.Controls.Util using (eqStr)

    renderOption : SelectOption V → Node M A
    renderOption opt =
      label ( class "agdelte-checkbox" ∷ [] )
        ( input ( type' "checkbox"
                ∷ class "agdelte-checkbox__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if elemBy eqV (optValue opt) (getSelected m)
                           then "true" else "")
                    eqStr)
                ∷ attrBind "aria-checked" (mkBinding
                    (λ m → if elemBy eqV (optValue opt) (getSelected m)
                           then "true" else "false")
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
    open import Agdelte.Html.Controls.Util using (eqStr)

    elemℕ : ℕ → List ℕ → Bool
    elemℕ _ [] = false
    elemℕ n (x ∷ xs) with n ≡ᵇ x
    ... | true  = true
    ... | false = elemℕ n xs

    renderOption : ℕ → String → Node M A
    renderOption idx lbl =
      label ( class "agdelte-checkbox" ∷ [] )
        ( input ( type' "checkbox"
                ∷ class "agdelte-checkbox__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if elemℕ idx (getSelected m) then "true" else "")
                    eqStr)
                ∷ attrBind "aria-checked" (mkBinding
                    (λ m → if elemℕ idx (getSelected m) then "true" else "false")
                    eqStr)
                ∷ onChange (λ _ → toggleMsg idx)
                ∷ [] )
        ∷ span ( class "agdelte-checkbox__label" ∷ [] )
            ( text lbl ∷ [] )
        ∷ [] )

    renderOptions : ℕ → List String → List (Node M A)
    renderOptions _ [] = []
    renderOptions idx (lbl ∷ rest) =
      renderOption idx lbl ∷ renderOptions (ℕ.suc idx) rest
      where open import Data.Nat as ℕ using (suc)
