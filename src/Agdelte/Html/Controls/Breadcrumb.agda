{-# OPTIONS --without-K #-}

-- Breadcrumb: Navigation breadcrumb trail
-- CSS classes: .agdelte-breadcrumb, .agdelte-breadcrumb__item,
--              .agdelte-breadcrumb__link, .agdelte-breadcrumb__separator,
--              .agdelte-breadcrumb__current

module Agdelte.Html.Controls.Breadcrumb where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _∸_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Breadcrumb item definition
------------------------------------------------------------------------

record BreadcrumbItem (A : Set) : Set where
  constructor mkBreadcrumbItem
  field
    crumbLabel : String
    crumbMsg   : A          -- click message (for navigation)

open BreadcrumbItem public

------------------------------------------------------------------------
-- Simple breadcrumb
------------------------------------------------------------------------

-- | Simple breadcrumb navigation.
-- | items: list of breadcrumb items (last is current page)
breadcrumb : ∀ {M A}
           → List (BreadcrumbItem A)
           → Node M A
breadcrumb {M} {A} items =
  nav ( class "agdelte-breadcrumb"
      ∷ attr "aria-label" "Breadcrumb"
      ∷ [] )
    ( elem "ol" ( class "agdelte-breadcrumb__list" ∷ [] )
        (renderItems 0 (length items) items)
    ∷ [] )
  where
    isLast : ℕ → ℕ → Bool
    isLast idx total = suc idx ≡ᵇ total

    renderItem : ℕ → ℕ → BreadcrumbItem A → Node M A
    renderItem idx total item =
      elem "li" ( class "agdelte-breadcrumb__item" ∷ [] )
        ( if isLast idx total
          then span ( class "agdelte-breadcrumb__current"
                    ∷ attr "aria-current" "page"
                    ∷ [] )
                 ( text (crumbLabel item) ∷ [] )
               ∷ []
          else button ( class "agdelte-breadcrumb__link"
                      ∷ onClick (crumbMsg item)
                      ∷ [] )
                 ( text (crumbLabel item) ∷ [] )
               ∷ span ( class "agdelte-breadcrumb__separator"
                      ∷ attr "aria-hidden" "true"
                      ∷ [] )
                   ( text "/" ∷ [] )
               ∷ [] )

    {-# TERMINATING #-}
    renderItems : ℕ → ℕ → List (BreadcrumbItem A) → List (Node M A)
    renderItems _ _ [] = []
    renderItems idx total (item ∷ rest) =
      renderItem idx total item ∷ renderItems (suc idx) total rest

------------------------------------------------------------------------
-- Breadcrumb with custom separator
------------------------------------------------------------------------

-- | Breadcrumb with custom separator character.
breadcrumbWith : ∀ {M A}
               → String                  -- separator (e.g., ">", "→", "»")
               → List (BreadcrumbItem A)
               → Node M A
breadcrumbWith {M} {A} sep items =
  nav ( class "agdelte-breadcrumb"
      ∷ attr "aria-label" "Breadcrumb"
      ∷ [] )
    ( elem "ol" ( class "agdelte-breadcrumb__list" ∷ [] )
        (renderItems 0 (length items) items)
    ∷ [] )
  where
    isLast : ℕ → ℕ → Bool
    isLast idx total = suc idx ≡ᵇ total

    renderItem : ℕ → ℕ → BreadcrumbItem A → Node M A
    renderItem idx total item =
      elem "li" ( class "agdelte-breadcrumb__item" ∷ [] )
        ( if isLast idx total
          then span ( class "agdelte-breadcrumb__current"
                    ∷ attr "aria-current" "page"
                    ∷ [] )
                 ( text (crumbLabel item) ∷ [] )
               ∷ []
          else button ( class "agdelte-breadcrumb__link"
                      ∷ onClick (crumbMsg item)
                      ∷ [] )
                 ( text (crumbLabel item) ∷ [] )
               ∷ span ( class "agdelte-breadcrumb__separator"
                      ∷ attr "aria-hidden" "true"
                      ∷ [] )
                   ( text sep ∷ [] )
               ∷ [] )

    {-# TERMINATING #-}
    renderItems : ℕ → ℕ → List (BreadcrumbItem A) → List (Node M A)
    renderItems _ _ [] = []
    renderItems idx total (item ∷ rest) =
      renderItem idx total item ∷ renderItems (suc idx) total rest

------------------------------------------------------------------------
-- Breadcrumb from string list (simple)
------------------------------------------------------------------------

-- | Simple breadcrumb from list of labels.
-- | All items click the same message with their index.
simpleBreadcrumb : ∀ {M A}
                 → (ℕ → A)          -- click handler (receives index)
                 → List String      -- labels
                 → Node M A
simpleBreadcrumb {M} {A} handler labels =
  nav ( class "agdelte-breadcrumb"
      ∷ attr "aria-label" "Breadcrumb"
      ∷ [] )
    ( elem "ol" ( class "agdelte-breadcrumb__list" ∷ [] )
        (renderItems 0 (length labels) labels)
    ∷ [] )
  where
    isLast : ℕ → ℕ → Bool
    isLast idx total = suc idx ≡ᵇ total

    renderItem : ℕ → ℕ → String → Node M A
    renderItem idx total lbl =
      elem "li" ( class "agdelte-breadcrumb__item" ∷ [] )
        ( if isLast idx total
          then span ( class "agdelte-breadcrumb__current"
                    ∷ attr "aria-current" "page"
                    ∷ [] )
                 ( text lbl ∷ [] )
               ∷ []
          else button ( class "agdelte-breadcrumb__link"
                      ∷ onClick (handler idx)
                      ∷ [] )
                 ( text lbl ∷ [] )
               ∷ span ( class "agdelte-breadcrumb__separator"
                      ∷ attr "aria-hidden" "true"
                      ∷ [] )
                   ( text "/" ∷ [] )
               ∷ [] )

    {-# TERMINATING #-}
    renderItems : ℕ → ℕ → List String → List (Node M A)
    renderItems _ _ [] = []
    renderItems idx total (lbl ∷ rest) =
      renderItem idx total lbl ∷ renderItems (suc idx) total rest

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | Create a breadcrumb item
crumb : ∀ {A} → String → A → BreadcrumbItem A
crumb = mkBreadcrumbItem
