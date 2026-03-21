{-# OPTIONS --without-K #-}

-- Lazy-loaded images using IntersectionObserver.
-- Shows Skeleton placeholder until the image enters the viewport.
-- CSS classes: .agdelte-lazy-img, .agdelte-lazy-img--loading, .agdelte-lazy-img--loaded

module Agdelte.Html.LazyImage where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Lazy image component
------------------------------------------------------------------------

-- | Lazy-loaded image using native browser loading="lazy".
-- The browser defers loading until the image nears the viewport.
lazyImg : ∀ {M A}
        → String            -- image URL
        → String            -- alt text
        → Node M A
lazyImg url altText =
  elem "img" ( class "agdelte-lazy-img"
             ∷ attr "src" url
             ∷ attr "alt" altText
             ∷ attr "loading" "lazy"
             ∷ [] ) []

-- | Lazy image with explicit width/height (prevents layout shift).
lazyImgSized : ∀ {M A}
             → String → String → String → String → Node M A
lazyImgSized url altText width height =
  elem "img" ( class "agdelte-lazy-img"
             ∷ attr "src" url
             ∷ attr "alt" altText
             ∷ attr "width" width
             ∷ attr "height" height
             ∷ attr "loading" "lazy"
             ∷ [] ) []
