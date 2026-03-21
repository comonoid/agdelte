{-# OPTIONS --without-K #-}

-- Star rating component (1–5 stars).
-- CSS classes: .agdelte-rating, .agdelte-rating__star,
--              .agdelte-rating__star--filled, .agdelte-rating__star--hover

module Agdelte.Html.Controls.Rating where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agda.Builtin.String using (primShowNat)
open import Agdelte.Reactive.Node
open import Agdelte.I18n using (pluralRu)

------------------------------------------------------------------------
-- Rating display (read-only)
------------------------------------------------------------------------

-- | Display N filled stars out of 5 (read-only).
ratingDisplay : ∀ {M A}
              → (M → ℕ)            -- current rating (1–5)
              → Node M A
ratingDisplay getRating =
  span (class "agdelte-rating agdelte-rating--readonly" ∷ [])
    ( star 1 ∷ star 2 ∷ star 3 ∷ star 4 ∷ star 5 ∷ [] )
  where
    star : ℕ → Node _ _
    star n = span
      ( classBind (λ m → if n ≤ᵇ getRating m
                         then "agdelte-rating__star agdelte-rating__star--filled"
                         else "agdelte-rating__star") ∷ [] )
      ( text "★" ∷ [] )

------------------------------------------------------------------------
-- Rating input (interactive)
------------------------------------------------------------------------

-- | Interactive star rating: click to set rating.
ratingInput : ∀ {M A}
            → (M → ℕ)            -- current rating
            → (ℕ → A)            -- on rate (1–5)
            → Node M A
ratingInput getRating onRate =
  span (class "agdelte-rating agdelte-rating--input" ∷ [])
    ( istar 1 ∷ istar 2 ∷ istar 3 ∷ istar 4 ∷ istar 5 ∷ [] )
  where
    istar : ℕ → Node _ _
    istar n = span
      ( classBind (λ m → if n ≤ᵇ getRating m
                         then "agdelte-rating__star agdelte-rating__star--filled"
                         else "agdelte-rating__star")
      ∷ onClick (onRate n)
      ∷ [] )
      ( text "★" ∷ [] )

------------------------------------------------------------------------
-- Average rating display
------------------------------------------------------------------------

-- | "4.2 ★ (128 отзывов)"
ratingSummary : ∀ {M A}
              → (M → String)       -- average as string ("4.2")
              → (M → ℕ)            -- review count
              → Node M A
ratingSummary getAvg getCount =
  span (class "agdelte-rating-summary" ∷ [])
    ( bindF (λ m → getAvg m ++ " ★ (" ++ pluralRu (getCount m) "отзыв" "отзыва" "отзывов" ++ ")")
    ∷ [] )
