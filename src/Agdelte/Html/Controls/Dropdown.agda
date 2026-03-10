{-# OPTIONS --without-K #-}

-- Dropdown: Select menu with options
-- CSS classes: .agdelte-dropdown, .agdelte-dropdown__trigger,
--              .agdelte-dropdown__menu, .agdelte-dropdown__option,
--              .agdelte-dropdown__option--selected, .agdelte-dropdown--open,
--              .agdelte-dropdown__option--highlighted,
--              .agdelte-dropdown__backdrop
--
-- Clicking outside an open dropdown closes it via a transparent backdrop overlay.
--
-- Keyboard: Escape/ArrowDown/ArrowUp/Enter forwarded via onKeyFiltered.
-- The caller manages highlighted-index state and handles key messages.

module Agdelte.Html.Controls.Dropdown where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr; case_of_)

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
  getOptionLabelByIdx : ℕ → List String → String
  getOptionLabelByIdx _ [] = "Select..."
  getOptionLabelByIdx zero (lbl ∷ _) = lbl
  getOptionLabelByIdx (suc n) (_ ∷ rest) = getOptionLabelByIdx n rest

  findOptionLabel : ∀ {V} → (V → V → Bool) → V → List (SelectOption V) → String
  findOptionLabel _ _ [] = "Select..."
  findOptionLabel eq v (opt ∷ rest) with eq v (optValue opt)
  ... | true  = optLabel opt
  ... | false = findOptionLabel eq v rest

  -- Build CSS class string for an option given selected/highlighted state
  optionClass : Bool → Bool → String
  optionClass false false = "agdelte-dropdown__option"
  optionClass true  false = "agdelte-dropdown__option agdelte-dropdown__option--selected"
  optionClass false true  = "agdelte-dropdown__option agdelte-dropdown__option--highlighted"
  optionClass true  true  = "agdelte-dropdown__option agdelte-dropdown__option--selected agdelte-dropdown__option--highlighted"

------------------------------------------------------------------------
-- Basic dropdown (index-based selection)
------------------------------------------------------------------------

private
  renderOptionIdx : ∀ {M A} → (M → Maybe ℕ) → (M → Maybe ℕ) → (ℕ → A) → ℕ → String → Node M A
  renderOptionIdx getSelected getHighlighted selectMsg idx lbl =
    div ( classBind (λ m →
            let isSel = case getSelected m of λ where
                  nothing → false
                  (just sel) → sel ≡ᵇ idx
                isHl = case getHighlighted m of λ where
                  nothing → false
                  (just hl) → hl ≡ᵇ idx
            in optionClass isSel isHl)
        ∷ attr "role" "option"
        ∷ attr "tabindex" "0"
        ∷ attrBind "aria-selected" (mkBinding
            (λ m → case getSelected m of λ where
              nothing → "false"
              (just sel) → if sel ≡ᵇ idx then "true" else "false")
            eqStr)
        ∷ onClick (selectMsg idx)
        ∷ [] )
        ( text lbl ∷ [] )

  renderOptionsIdx : ∀ {M A} → (M → Maybe ℕ) → (M → Maybe ℕ) → (ℕ → A) → ℕ → List String → List (Node M A)
  renderOptionsIdx getSelected getHighlighted selectMsg idx [] = []
  renderOptionsIdx getSelected getHighlighted selectMsg idx (lbl ∷ rest) =
    renderOptionIdx getSelected getHighlighted selectMsg idx lbl
    ∷ renderOptionsIdx getSelected getHighlighted selectMsg (suc idx) rest

-- | Dropdown with index-based selection.
dropdownIdx : ∀ {M A}
            → (M → Maybe ℕ)      -- selected index
            → (M → Maybe ℕ)      -- highlighted index (keyboard cursor)
            → (M → Bool)         -- is open
            → A                  -- toggle message
            → (ℕ → A)            -- select message
            → (String → A)       -- key message (ArrowDown/ArrowUp/Enter/Escape)
            → List String        -- option labels
            → Node M A
dropdownIdx {M} getSelected getHighlighted getOpen toggleMsg selectMsg keyMsg options =
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
      ∷ onKeyFiltered ("Escape" ∷ "ArrowDown" ∷ "ArrowUp" ∷ "Enter" ∷ []) keyMsg
      ∷ [] )
    ( button ( class "agdelte-dropdown__trigger"
             ∷ attr "type" "button"
             ∷ onClick toggleMsg
             ∷ attr "aria-haspopup" "listbox"
             ∷ attrBind "aria-expanded" (mkBinding
                 (λ m → if getOpen m then "true" else "false")
                 eqStr)
             ∷ [] )
        ( bindF displayText ∷ [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__backdrop"
              ∷ onClick toggleMsg
              ∷ [] ) [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__menu"
              ∷ attr "role" "listbox"
              ∷ [] )
            (renderOptionsIdx getSelected getHighlighted selectMsg 0 options) )
    ∷ [] )

------------------------------------------------------------------------
-- Dropdown with typed values
------------------------------------------------------------------------

private
  renderOptionV : ∀ {V M A} → (V → V → Bool) → (M → Maybe V) → (M → Maybe ℕ)
                → (V → A) → ℕ → SelectOption V → Node M A
  renderOptionV eqV getSelected getHighlighted selectMsg idx opt =
    div ( classBind (λ m →
            let isSel = case getSelected m of λ where
                  nothing → false
                  (just sel) → eqV sel (optValue opt)
                isHl = case getHighlighted m of λ where
                  nothing → false
                  (just hl) → hl ≡ᵇ idx
            in optionClass isSel isHl)
        ∷ attr "role" "option"
        ∷ attr "tabindex" "0"
        ∷ attrBind "aria-selected" (mkBinding
            (λ m → case getSelected m of λ where
              nothing → "false"
              (just sel) → if eqV sel (optValue opt) then "true" else "false")
            eqStr)
        ∷ onClick (selectMsg (optValue opt))
        ∷ [] )
        ( text (optLabel opt) ∷ [] )

  renderOptionsV : ∀ {V M A} → (V → V → Bool) → (M → Maybe V) → (M → Maybe ℕ)
                 → (V → A) → ℕ → List (SelectOption V) → List (Node M A)
  renderOptionsV eqV getSelected getHighlighted selectMsg idx [] = []
  renderOptionsV eqV getSelected getHighlighted selectMsg idx (opt ∷ rest) =
    renderOptionV eqV getSelected getHighlighted selectMsg idx opt
    ∷ renderOptionsV eqV getSelected getHighlighted selectMsg (suc idx) rest

-- | Dropdown with typed value selection.
dropdown : ∀ {V M A}
         → (V → V → Bool)        -- value equality
         → (M → Maybe V)         -- selected value
         → (M → Maybe ℕ)         -- highlighted index (keyboard cursor)
         → (M → Bool)            -- is open
         → A                     -- toggle message
         → (V → A)               -- select message
         → (String → A)          -- key message (ArrowDown/ArrowUp/Enter/Escape)
         → List (SelectOption V) -- options
         → Node M A
dropdown {_} {M} eqV getSelected getHighlighted getOpen toggleMsg selectMsg keyMsg options =
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
      ∷ onKeyFiltered ("Escape" ∷ "ArrowDown" ∷ "ArrowUp" ∷ "Enter" ∷ []) keyMsg
      ∷ [] )
    ( button ( class "agdelte-dropdown__trigger"
             ∷ attr "type" "button"
             ∷ onClick toggleMsg
             ∷ attr "aria-haspopup" "listbox"
             ∷ attrBind "aria-expanded" (mkBinding
                 (λ m → if getOpen m then "true" else "false")
                 eqStr)
             ∷ [] )
        ( bindF displayText ∷ [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__backdrop"
              ∷ onClick toggleMsg
              ∷ [] ) [] )
    ∷ when getOpen
        ( div ( class "agdelte-dropdown__menu"
              ∷ attr "role" "listbox"
              ∷ [] )
            (renderOptionsV eqV getSelected getHighlighted selectMsg 0 options) )
    ∷ [] )

------------------------------------------------------------------------
-- Simple string dropdown
------------------------------------------------------------------------

-- | Convenience: dropdown where value = label (String)
stringDropdown : ∀ {M A}
               → (M → Maybe String)   -- selected value
               → (M → Maybe ℕ)        -- highlighted index (keyboard cursor)
               → (M → Bool)           -- is open
               → A                    -- toggle message
               → (String → A)         -- select message
               → (String → A)         -- key message
               → List String          -- options (value = label)
               → Node M A
stringDropdown getSelected getHighlighted getOpen toggleMsg selectMsg keyMsg options =
  dropdown eqStr getSelected getHighlighted getOpen toggleMsg selectMsg keyMsg
    (map (λ s → mkOption s s) options)
