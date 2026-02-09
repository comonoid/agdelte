{-# OPTIONS --without-K #-}

-- Dropdown: Select menu with options
-- CSS classes: .agdelte-dropdown, .agdelte-dropdown__trigger,
--              .agdelte-dropdown__menu, .agdelte-dropdown__option,
--              .agdelte-dropdown__option--selected, .agdelte-dropdown--open

module Agdelte.Html.Controls.Dropdown where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Option record
------------------------------------------------------------------------

record SelectOption (V : Set) : Set where
  constructor mkOption
  field
    optValue : V
    optLabel : String

open SelectOption public

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

  {-# TERMINATING #-}
  getOptionLabelByIdx : ℕ → List String → String
  getOptionLabelByIdx _ [] = "Select..."
  getOptionLabelByIdx zero (lbl ∷ _) = lbl
  getOptionLabelByIdx (suc n) (_ ∷ rest) = getOptionLabelByIdx n rest

  {-# TERMINATING #-}
  findOptionLabel : ∀ {V} → (V → V → Bool) → V → List (SelectOption V) → String
  findOptionLabel _ _ [] = "Select..."
  findOptionLabel eq v (opt ∷ rest) =
    if eq v (optValue opt)
    then optLabel opt
    else findOptionLabel eq v rest

------------------------------------------------------------------------
-- Basic dropdown (index-based selection)
------------------------------------------------------------------------

private
  renderOptionIdx : ∀ {M A} → (M → Maybe ℕ) → (ℕ → A) → ℕ → String → Node M A
  renderOptionIdx getSelected selectMsg idx lbl =
    div ( classBind (λ m →
            case getSelected m of λ where
              nothing → "agdelte-dropdown__option"
              (just sel) →
                if sel ≡ᵇ idx
                then "agdelte-dropdown__option agdelte-dropdown__option--selected"
                else "agdelte-dropdown__option")
        ∷ onClick (selectMsg idx)
        ∷ [] )
        ( text lbl ∷ [] )
    where
      case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
      case x of f = f x

  {-# TERMINATING #-}
  renderOptionsIdx : ∀ {M A} → (M → Maybe ℕ) → (ℕ → A) → ℕ → List String → List (Node M A)
  renderOptionsIdx getSelected selectMsg idx [] = []
  renderOptionsIdx getSelected selectMsg idx (lbl ∷ rest) =
    renderOptionIdx getSelected selectMsg idx lbl
    ∷ renderOptionsIdx getSelected selectMsg (suc idx) rest

-- | Dropdown with index-based selection.
dropdownIdx : ∀ {M A}
            → (M → Maybe ℕ)      -- selected index
            → (M → Bool)         -- is open
            → A                  -- toggle message
            → (ℕ → A)            -- select message
            → List String        -- option labels
            → Node M A
dropdownIdx {M} getSelected getOpen toggleMsg selectMsg options =
  let
    displayText : M → String
    displayText m = case getSelected m of λ where
      nothing → "Select..."
      (just idx) → getOptionLabelByIdx idx options
  in
  div ( classBind (λ m →
          if getOpen m
          then "agdelte-dropdown agdelte-dropdown--open"
          else "agdelte-dropdown")
      ∷ [] )
    ( button ( class "agdelte-dropdown__trigger"
             ∷ onClick toggleMsg
             ∷ attr "aria-haspopup" "listbox"
             ∷ attrBind "aria-expanded" (mkBinding
                 (λ m → if getOpen m then "true" else "false")
                 eqStr)
             ∷ [] )
        ( bindF displayText ∷ [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__menu"
              ∷ attr "role" "listbox"
              ∷ [] )
            (renderOptionsIdx getSelected selectMsg 0 options) )
    ∷ [] )
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

------------------------------------------------------------------------
-- Dropdown with typed values
------------------------------------------------------------------------

private
  renderOptionV : ∀ {V M A} → (V → V → Bool) → (M → Maybe V) → (V → A)
                → SelectOption V → Node M A
  renderOptionV eqV getSelected selectMsg opt =
    div ( classBind (λ m →
            case getSelected m of λ where
              nothing → "agdelte-dropdown__option"
              (just sel) →
                if eqV sel (optValue opt)
                then "agdelte-dropdown__option agdelte-dropdown__option--selected"
                else "agdelte-dropdown__option")
        ∷ onClick (selectMsg (optValue opt))
        ∷ [] )
        ( text (optLabel opt) ∷ [] )
    where
      case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
      case x of f = f x

-- | Dropdown with typed value selection.
dropdown : ∀ {V M A}
         → (V → V → Bool)        -- value equality
         → (M → Maybe V)         -- selected value
         → (M → Bool)            -- is open
         → A                     -- toggle message
         → (V → A)               -- select message
         → List (SelectOption V) -- options
         → Node M A
dropdown {_} {M} eqV getSelected getOpen toggleMsg selectMsg options =
  let
    displayText : M → String
    displayText m = case getSelected m of λ where
      nothing → "Select..."
      (just sel) → findOptionLabel eqV sel options
  in
  div ( classBind (λ m →
          if getOpen m
          then "agdelte-dropdown agdelte-dropdown--open"
          else "agdelte-dropdown")
      ∷ [] )
    ( button ( class "agdelte-dropdown__trigger"
             ∷ onClick toggleMsg
             ∷ attr "aria-haspopup" "listbox"
             ∷ attrBind "aria-expanded" (mkBinding
                 (λ m → if getOpen m then "true" else "false")
                 eqStr)
             ∷ [] )
        ( bindF displayText ∷ [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__menu"
              ∷ attr "role" "listbox"
              ∷ [] )
            (map (renderOptionV eqV getSelected selectMsg) options) )
    ∷ [] )
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

------------------------------------------------------------------------
-- Simple string dropdown
------------------------------------------------------------------------

-- | Convenience: dropdown where value = label (String)
stringDropdown : ∀ {M A}
               → (M → Maybe String)   -- selected value
               → (M → Bool)           -- is open
               → A                    -- toggle message
               → (String → A)         -- select message
               → List String          -- options (value = label)
               → Node M A
stringDropdown getSelected getOpen toggleMsg selectMsg options =
  dropdown eqStr getSelected getOpen toggleMsg selectMsg
    (map (λ s → mkOption s s) options)
