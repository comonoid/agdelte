{-# OPTIONS --without-K #-}

-- Controls.Util: shared helpers for the Html.Controls library
--
-- Provides eqStr (string equality as Bool) and case_of_ (local case expression)
-- used throughout the control modules.

module Agdelte.Html.Controls.Util where

open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)

open import Data.String using (_≟_)

------------------------------------------------------------------------
-- String equality as Bool
------------------------------------------------------------------------

eqStr : String → String → Bool
eqStr a b with a ≟ b
... | yes _ = true
... | no _  = false

------------------------------------------------------------------------
-- case_of_ (local case expression)
------------------------------------------------------------------------

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x
