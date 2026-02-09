{-# OPTIONS --without-K #-}

-- RadioGroup: Radio button groups for single selection
-- CSS classes: .agdelte-radio, .agdelte-radio__input,
--              .agdelte-radio__label, .agdelte-radio-group

module Agdelte.Html.Controls.RadioGroup where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

-- Re-use SelectOption from Dropdown
open import Agdelte.Html.Controls.Dropdown using (SelectOption; mkOption; optValue; optLabel)

------------------------------------------------------------------------
-- Helper: string equality
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

------------------------------------------------------------------------
-- Radio group with typed values
------------------------------------------------------------------------

-- | Radio group for single selection with typed values.
-- | name: HTML name attribute (groups radios together)
-- | eqV: equality function for values
-- | getSelected: extract selected value from model (Maybe V)
-- | selectMsg: message constructor for selecting a value
-- | options: list of options
radioGroup : ∀ {V M A}
           → String                    -- group name
           → (V → V → Bool)            -- value equality
           → (M → Maybe V)             -- selected value
           → (V → A)                   -- select message
           → List (SelectOption V)
           → Node M A
radioGroup {V} {M} {A} name eqV getSelected selectMsg options =
  div ( class "agdelte-radio-group" ∷ attr "role" "radiogroup" ∷ [] )
    (map renderOption options)
  where
    isSelected : V → M → Bool
    isSelected v m with getSelected m
    ... | nothing = false
    ... | just sel = eqV v sel

    renderOption : SelectOption V → Node M A
    renderOption opt =
      label ( class "agdelte-radio" ∷ [] )
        ( input ( type' "radio"
                ∷ attr "name" name
                ∷ class "agdelte-radio__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if isSelected (optValue opt) m then "true" else "")
                    eqStr)
                ∷ onChange (λ _ → selectMsg (optValue opt))
                ∷ [] )
        ∷ span ( class "agdelte-radio__label" ∷ [] )
            ( text (optLabel opt) ∷ [] )
        ∷ [] )

------------------------------------------------------------------------
-- Radio group with index-based selection
------------------------------------------------------------------------

-- | Radio group using indices (simpler when you don't need typed values)
radioGroupIdx : ∀ {M A}
              → String                 -- group name
              → (M → Maybe ℕ)          -- selected index
              → (ℕ → A)                -- select message
              → List String            -- option labels
              → Node M A
radioGroupIdx {M} {A} name getSelected selectMsg labels =
  div ( class "agdelte-radio-group" ∷ attr "role" "radiogroup" ∷ [] )
    (renderOptions 0 labels)
  where
    isSelected : ℕ → M → Bool
    isSelected idx m with getSelected m
    ... | nothing = false
    ... | just sel = idx ≡ᵇ sel

    renderOption : ℕ → String → Node M A
    renderOption idx lbl =
      label ( class "agdelte-radio" ∷ [] )
        ( input ( type' "radio"
                ∷ attr "name" name
                ∷ class "agdelte-radio__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if isSelected idx m then "true" else "")
                    eqStr)
                ∷ onChange (λ _ → selectMsg idx)
                ∷ [] )
        ∷ span ( class "agdelte-radio__label" ∷ [] )
            ( text lbl ∷ [] )
        ∷ [] )

    {-# TERMINATING #-}
    renderOptions : ℕ → List String → List (Node M A)
    renderOptions _ [] = []
    renderOptions idx (lbl ∷ rest) =
      renderOption idx lbl ∷ renderOptions (suc idx) rest

------------------------------------------------------------------------
-- String-based radio group (simplest)
------------------------------------------------------------------------

-- | Radio group with string values
stringRadioGroup : ∀ {M A}
                 → String              -- group name
                 → (M → Maybe String)  -- selected value
                 → (String → A)        -- select message
                 → List String         -- options (value = label)
                 → Node M A
stringRadioGroup {M} {A} name getSelected selectMsg labels =
  div ( class "agdelte-radio-group" ∷ attr "role" "radiogroup" ∷ [] )
    (map renderOption labels)
  where
    isSelected : String → M → Bool
    isSelected v m with getSelected m
    ... | nothing = false
    ... | just sel = eqStr v sel

    renderOption : String → Node M A
    renderOption lbl =
      label ( class "agdelte-radio" ∷ [] )
        ( input ( type' "radio"
                ∷ attr "name" name
                ∷ class "agdelte-radio__input"
                ∷ attrBind "checked" (mkBinding
                    (λ m → if isSelected lbl m then "true" else "")
                    eqStr)
                ∷ onChange (λ _ → selectMsg lbl)
                ∷ [] )
        ∷ span ( class "agdelte-radio__label" ∷ [] )
            ( text lbl ∷ [] )
        ∷ [] )
