{-# OPTIONS --without-K #-}

-- Pagination: Page navigation controls
-- CSS classes: .agdelte-pagination, .agdelte-pagination__btn,
--              .agdelte-pagination__page, .agdelte-pagination__page--active,
--              .agdelte-pagination__ellipsis

module Agdelte.Html.Controls.Pagination where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

open import Agda.Builtin.String using (primStringFromList)
open import Data.Char using (fromℕ)

------------------------------------------------------------------------
-- Number to string conversion
------------------------------------------------------------------------

private
  open import Data.Char using (Char)
  open import Data.Nat using (_/_; _%_)

  -- Digit to character
  digitChar : ℕ → Char
  digitChar n = fromℕ (48 + n)

  -- Natural number to string (simple, for page numbers)
  {-# TERMINATING #-}
  showℕ : ℕ → String
  showℕ 0 = "0"
  showℕ n = primStringFromList (go n [])
    where
      go : ℕ → List Char → List Char
      go 0 acc = acc
      go m acc = go (m / 10) (digitChar (m % 10) ∷ acc)

------------------------------------------------------------------------
-- Simple pagination (prev/next only)
------------------------------------------------------------------------

-- | Simple prev/next pagination.
-- | currentPage: extract current page (1-indexed)
-- | totalPages: extract total pages
-- | prevMsg: message to go to previous page
-- | nextMsg: message to go to next page
simplePagination : ∀ {M A}
                 → (M → ℕ)       -- current page
                 → (M → ℕ)       -- total pages
                 → A             -- prev page message
                 → A             -- next page message
                 → Node M A
simplePagination {M} {A} currentPage totalPages prevMsg nextMsg =
  div ( class "agdelte-pagination" ∷ [] )
    ( button ( class "agdelte-pagination__btn"
             ∷ attrBind "disabled" (mkBinding
                 (λ m → if currentPage m ≤ᵇ 1 then "true" else "")
                 eqStr)
             ∷ onClick prevMsg
             ∷ [] )
        ( text "← Prev" ∷ [] )
    ∷ span ( class "agdelte-pagination__info" ∷ [] )
        ( text "Page "
        ∷ bindF (showℕ ∘ currentPage)
        ∷ text " of "
        ∷ bindF (showℕ ∘ totalPages)
        ∷ [] )
    ∷ button ( class "agdelte-pagination__btn"
             ∷ attrBind "disabled" (mkBinding
                 (λ m → if currentPage m <ᵇ totalPages m then "" else "true")
                 eqStr)
             ∷ onClick nextMsg
             ∷ [] )
        ( text "Next →" ∷ [] )
    ∷ [] )
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

------------------------------------------------------------------------
-- Numbered pagination (static page count)
------------------------------------------------------------------------

-- | Numbered pagination with fixed page buttons (for small page counts).
-- | pages: list of page numbers to show
numberedPagination : ∀ {M A}
                   → (M → ℕ)       -- current page (1-indexed)
                   → (ℕ → A)       -- go to page message
                   → A             -- prev message
                   → A             -- next message
                   → List ℕ        -- pages to show
                   → Node M A
numberedPagination {M} {A} currentPage goToPage prevMsg nextMsg pages =
  div ( class "agdelte-pagination" ∷ [] )
    ( button ( class "agdelte-pagination__btn"
             ∷ attrBind "disabled" (mkBinding
                 (λ m → if currentPage m ≤ᵇ 1 then "true" else "")
                 eqStr)
             ∷ onClick prevMsg
             ∷ [] )
        ( text "←" ∷ [] )
    ∷ renderPages pages
    ++ ( button ( class "agdelte-pagination__btn"
                ∷ onClick nextMsg
                ∷ [] )
           ( text "→" ∷ [] )
       ∷ [] ) )
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

    -- Render a single page button
    pageBtn : ℕ → Node M A
    pageBtn page =
      button ( attrBind "class" (mkBinding
                 (λ m → if page ≡ᵇ currentPage m
                        then "agdelte-pagination__page agdelte-pagination__page--active"
                        else "agdelte-pagination__page")
                 eqStr)
             ∷ onClick (goToPage page)
             ∷ [] )
        ( text (showℕ page) ∷ [] )

    {-# TERMINATING #-}
    renderPages : List ℕ → List (Node M A)
    renderPages [] = []
    renderPages (p ∷ ps) = pageBtn p ∷ renderPages ps

------------------------------------------------------------------------
-- Compact pagination (just page numbers)
------------------------------------------------------------------------

-- | Compact pagination showing only current/total.
compactPagination : ∀ {M A}
                  → (M → ℕ)       -- current page
                  → (M → ℕ)       -- total pages
                  → A             -- prev message
                  → A             -- next message
                  → Node M A
compactPagination {M} {A} currentPage totalPages prevMsg nextMsg =
  div ( class "agdelte-pagination agdelte-pagination--compact" ∷ [] )
    ( button ( class "agdelte-pagination__btn"
             ∷ attrBind "disabled" (mkBinding
                 (λ m → if currentPage m ≤ᵇ 1 then "true" else "")
                 eqStr)
             ∷ onClick prevMsg
             ∷ [] )
        ( text "‹" ∷ [] )
    ∷ span ( class "agdelte-pagination__current" ∷ [] )
        ( bindF (showℕ ∘ currentPage)
        ∷ text "/"
        ∷ bindF (showℕ ∘ totalPages)
        ∷ [] )
    ∷ button ( class "agdelte-pagination__btn"
             ∷ attrBind "disabled" (mkBinding
                 (λ m → if currentPage m <ᵇ totalPages m then "" else "true")
                 eqStr)
             ∷ onClick nextMsg
             ∷ [] )
        ( text "›" ∷ [] )
    ∷ [] )
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false
