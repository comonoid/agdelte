{-# OPTIONS --without-K #-}

-- Optic tests — propositional equality proofs
-- Tests for Prism, Traversal, Affine, Optic composition, routeMsg

module Agdelte.Test.OpticTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Reactive.Optic

------------------------------------------------------------------------
-- Test data
------------------------------------------------------------------------

-- Simple sum type for Prism testing
data Color : Set where
  Red Green Blue : Color

-- Prism into Red
redPrism : Prism Color ℕ
redPrism = mkPrism matchRed buildRed
  where
    matchRed : Color → Maybe ℕ
    matchRed Red = just 0
    matchRed _   = nothing
    buildRed : ℕ → Color
    buildRed _ = Red

------------------------------------------------------------------------
-- Lens tests
------------------------------------------------------------------------

test-lens-get : get fstLens (1 , 2) ≡ 1
test-lens-get = refl

test-lens-set : Lens.set fstLens 10 (1 , 2) ≡ (10 , 2)
test-lens-set = refl

test-lens-modify : modify fstLens suc (1 , 2) ≡ (2 , 2)
test-lens-modify = refl

test-lens-compose : get (fstLens ∘L fstLens) ((1 , 2) , 3) ≡ 1
test-lens-compose = refl

------------------------------------------------------------------------
-- Prism tests
------------------------------------------------------------------------

test-prism-match : match redPrism Red ≡ just 0
test-prism-match = refl

test-prism-miss : match redPrism Green ≡ nothing
test-prism-miss = refl

test-prism-build : build redPrism 42 ≡ Red
test-prism-build = refl

------------------------------------------------------------------------
-- Affine tests
------------------------------------------------------------------------

test-affine-lens : Affine.preview (lensToAffine fstLens) (1 , 2) ≡ just 1
test-affine-lens = refl

test-affine-set : Affine.set (lensToAffine fstLens) 10 (1 , 2) ≡ (10 , 2)
test-affine-set = refl

------------------------------------------------------------------------
-- Optic tests
------------------------------------------------------------------------

test-optic-peek : peek (fromLens fstLens) (1 , 2) ≡ just 1
test-optic-peek = refl

test-optic-over : over (fromLens fstLens) suc (1 , 2) ≡ (2 , 2)
test-optic-over = refl

-- Composition test: fstLens ∘O fstLens on nested pairs
test-optic-compose :
  peek (fromLens fstLens ∘O fromLens fstLens) ((1 , 2) , 3) ≡ just 1
test-optic-compose = refl

test-optic-compose-over :
  over (fromLens fstLens ∘O fromLens fstLens) suc ((1 , 2) , 3) ≡ ((2 , 2) , 3)
test-optic-compose-over = refl

------------------------------------------------------------------------
-- Indexed access tests
------------------------------------------------------------------------

test-ixList-0 : Affine.preview (ixList 0) (10 ∷ 20 ∷ 30 ∷ []) ≡ just 10
test-ixList-0 = refl

test-ixList-2 : Affine.preview (ixList 2) (10 ∷ 20 ∷ 30 ∷ []) ≡ just 30
test-ixList-2 = refl

test-ixList-oob : Affine.preview (ixList 5) (10 ∷ 20 ∷ []) ≡ nothing
test-ixList-oob = refl

test-ixList-set : Affine.set (ixList 1) 99 (10 ∷ 20 ∷ 30 ∷ []) ≡ (10 ∷ 99 ∷ 30 ∷ [])
test-ixList-set = refl

------------------------------------------------------------------------
-- routeMsg test
------------------------------------------------------------------------

-- Simple model: pair of ℕ
-- Messages: LeftInc / RightInc
data TestMsg : Set where
  LeftInc RightInc : TestMsg

leftPrism : Prism TestMsg ℕ
leftPrism = mkPrism
  (λ { LeftInc → just 0 ; RightInc → nothing })
  (λ _ → LeftInc)

test-route-match : routeMsg leftPrism fstLens (λ _ n → suc n) LeftInc (5 , 10) ≡ (6 , 10)
test-route-match = refl

test-route-miss : routeMsg leftPrism fstLens (λ _ n → suc n) RightInc (5 , 10) ≡ (5 , 10)
test-route-miss = refl
