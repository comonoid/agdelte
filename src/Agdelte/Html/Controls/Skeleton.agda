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
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Basic skeleton
------------------------------------------------------------------------

-- | Rectangular skeleton with custom dimensions
skeleton : ∀ {M A} → String → String → Node M A
skeleton w h =
  div ( class "agdelte-skeleton"
      ∷ style "width" w
      ∷ style "height" h
      ∷ [] ) []

------------------------------------------------------------------------
-- Common skeleton shapes
------------------------------------------------------------------------

-- | Circle skeleton (avatar placeholder)
skeletonCircle : ∀ {M A} → String → Node M A
skeletonCircle size =
  div ( class "agdelte-skeleton agdelte-skeleton--circle"
      ∷ style "width" size
      ∷ style "height" size
      ∷ [] ) []

-- | Text line skeleton (single line)
skeletonLine : ∀ {M A} → Node M A
skeletonLine = div (class "agdelte-skeleton agdelte-skeleton--text" ∷ []) []

-- | Text line with custom width
skeletonLineW : ∀ {M A} → String → Node M A
skeletonLineW w =
  div ( class "agdelte-skeleton agdelte-skeleton--text"
      ∷ style "width" w
      ∷ [] ) []

------------------------------------------------------------------------
-- Multi-line text skeleton
------------------------------------------------------------------------

-- | Multiple text line skeletons
skeletonText : ∀ {M A} → ℕ → Node M A
skeletonText n =
  div (class "agdelte-skeleton-text" ∷ []) (renderLines n)
  where
    renderLines : ℕ → List (Node _ _)
    renderLines zero = []
    renderLines (suc zero) =
      -- Last line shorter
      div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "60%"
          ∷ [] ) []
      ∷ []
    renderLines (suc m) =
      div (class "agdelte-skeleton agdelte-skeleton--text" ∷ []) []
      ∷ renderLines m

------------------------------------------------------------------------
-- Card skeleton
------------------------------------------------------------------------

-- | Card placeholder with image and text
skeletonCard : ∀ {M A} → Node M A
skeletonCard =
  div (class "agdelte-skeleton-card" ∷ [])
    ( -- Image placeholder
      div ( class "agdelte-skeleton"
          ∷ style "width" "100%"
          ∷ style "height" "150px"
          ∷ [] ) []
    -- Title
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "70%"
          ∷ style "margin-top" "12px"
          ∷ [] ) []
    -- Description lines
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "margin-top" "8px"
          ∷ [] ) []
    ∷ div ( class "agdelte-skeleton agdelte-skeleton--text"
          ∷ style "width" "80%"
          ∷ style "margin-top" "4px"
          ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Avatar with text skeleton
------------------------------------------------------------------------

-- | Avatar circle with text lines
skeletonAvatarText : ∀ {M A} → Node M A
skeletonAvatarText =
  div ( class "agdelte-skeleton-avatar-text"
      ∷ style "display" "flex"
      ∷ style "gap" "12px"
      ∷ style "align-items" "center"
      ∷ [] )
    ( -- Avatar
      div ( class "agdelte-skeleton agdelte-skeleton--circle"
          ∷ style "width" "40px"
          ∷ style "height" "40px"
          ∷ style "flex-shrink" "0"
          ∷ [] ) []
    -- Text lines
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

------------------------------------------------------------------------
-- Table skeleton
------------------------------------------------------------------------

-- | Table placeholder with rows and columns
skeletonTable : ∀ {M A} → ℕ → ℕ → Node M A
skeletonTable cols rows =
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

------------------------------------------------------------------------
-- List skeleton
------------------------------------------------------------------------

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
  div (class "agdelte-skeleton-wrapper" ∷ [])
    ( when isLoading skeletonNode
    ∷ when (not' isLoading) content
    ∷ [] )
  where
    not' : (M → Bool) → M → Bool
    not' f m = if f m then false else true
