{-# OPTIONS --without-K #-}

-- Skeleton: Placeholder loading states
-- Shows grey shapes while content is loading
-- CSS classes: .agdelte-skeleton, .agdelte-skeleton--circle,
--              .agdelte-skeleton--text, .agdelte-skeleton-card,
--              .agdelte-skeleton-avatar-text, .agdelte-skeleton-table

module Agdelte.Html.Controls.Skeleton where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Skeleton shape configuration
------------------------------------------------------------------------

data SkeletonShape : Set where
  rect    : String → String → SkeletonShape   -- width, height
  circle' : String → SkeletonShape             -- diameter
  line    : SkeletonShape                      -- full-width text line
  lineW   : String → SkeletonShape             -- text line with custom width

-- | Core skeleton renderer from shape config
skeletonShape : ∀ {M A} → SkeletonShape → Node M A
skeletonShape (rect w h) =
  div ( class "agdelte-skeleton"
      ∷ style "width" w ∷ style "height" h ∷ [] ) []
skeletonShape (circle' size) =
  div ( class "agdelte-skeleton agdelte-skeleton--circle"
      ∷ style "width" size ∷ style "height" size ∷ [] ) []
skeletonShape line =
  div (class "agdelte-skeleton agdelte-skeleton--text" ∷ []) []
skeletonShape (lineW w) =
  div ( class "agdelte-skeleton agdelte-skeleton--text"
      ∷ style "width" w ∷ [] ) []

------------------------------------------------------------------------
-- Backward-compatible convenience functions
------------------------------------------------------------------------

skeleton : ∀ {M A} → String → String → Node M A
skeleton w h = skeletonShape (rect w h)

skeletonCircle : ∀ {M A} → String → Node M A
skeletonCircle size = skeletonShape (circle' size)

skeletonLine : ∀ {M A} → Node M A
skeletonLine = skeletonShape line

skeletonLineW : ∀ {M A} → String → Node M A
skeletonLineW w = skeletonShape (lineW w)

------------------------------------------------------------------------
-- Composite skeleton patterns
------------------------------------------------------------------------

-- | Multiple text line skeletons
skeletonText : ∀ {M A} → ℕ → Node M A
skeletonText n =
  div (class "agdelte-skeleton-text" ∷ []) (renderLines n)
  where
    renderLines : ℕ → List (Node _ _)
    renderLines zero = []
    renderLines (suc zero) =
      div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "60%"
          ∷ [] ) []
      ∷ []
    renderLines (suc m) =
      div (class "agdelte-skeleton agdelte-skeleton--text" ∷ []) []
      ∷ renderLines m

-- | Card placeholder with image and text
skeletonCard : ∀ {M A} → Node M A
skeletonCard =
  div (class "agdelte-skeleton-card" ∷ [])
    ( skeletonShape (rect "100%" "150px")
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "70%"
          ∷ style "margin-top" "12px"
          ∷ [] ) []
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "margin-top" "8px"
          ∷ [] ) []
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "80%"
          ∷ style "margin-top" "4px"
          ∷ [] ) []
    ∷ [] )

-- | Avatar circle with text lines
skeletonAvatarText : ∀ {M A} → Node M A
skeletonAvatarText =
  div ( class "agdelte-skeleton-avatar-text"
      ∷ style "display" "flex"
      ∷ style "gap" "12px"
      ∷ style "align-items" "center"
      ∷ [] )
    ( div ( class "agdelte-skeleton agdelte-skeleton--circle"
          ∷ style "width" "40px"
          ∷ style "height" "40px"
          ∷ style "flex-shrink" "0"
          ∷ [] ) []
    ∷ div (style "flex" "1" ∷ [])
        ( div ( class "agdelte-skeleton agdelte-skeleton--text"
              ∷ style "width" "60%"
              ∷ [] ) []
        ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
              ∷ style "width" "40%"
              ∷ style "margin-top" "4px"
              ∷ [] ) []
        ∷ [] )
    ∷ [] )

-- | Table placeholder with rows and columns
skeletonTable : ∀ {M A} → ℕ → ℕ → Node M A
skeletonTable rows cols =
  div (class "agdelte-skeleton-table" ∷ []) (renderRows rows)
  where
    renderCells : ℕ → List (Node _ _)
    renderCells zero = []
    renderCells (suc n) =
      div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "flex" "1"
          ∷ [] ) []
      ∷ renderCells n

    renderRows : ℕ → List (Node _ _)
    renderRows zero = []
    renderRows (suc n) =
      div ( style "display" "flex"
          ∷ style "gap" "16px"
          ∷ style "margin-bottom" "8px"
          ∷ [] )
        (renderCells cols)
      ∷ renderRows n

-- | List of avatar-text placeholders
skeletonList : ∀ {M A} → ℕ → Node M A
skeletonList n =
  div (class "agdelte-skeleton-list" ∷ []) (renderItems n)
  where
    renderItems : ℕ → List (Node _ _)
    renderItems zero = []
    renderItems (suc m) =
      skeletonAvatarText
      ∷ renderItems m

------------------------------------------------------------------------
-- Conditional skeleton
------------------------------------------------------------------------

-- | Show skeleton while loading, content when done
withSkeleton : ∀ {M A}
             → (M → Bool)       -- isLoading
             → Node M A         -- skeleton placeholder
             → Node M A         -- actual content
             → Node M A
withSkeleton {M} isLoading skeletonNode content =
  div ( class "agdelte-skeleton-wrapper"
      ∷ [] )
    ( when isLoading skeletonNode
    ∷ when (not ∘ isLoading) content
    ∷ [] )
