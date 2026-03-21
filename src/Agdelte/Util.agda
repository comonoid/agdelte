{-# OPTIONS --without-K #-}

-- Common utilities.

module Agdelte.Util where

-- | case_of_ : pattern matching as an expression.
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x
