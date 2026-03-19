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
open import Function using (case_of_) public

------------------------------------------------------------------------
-- String equality as Bool
------------------------------------------------------------------------

eqStr : String → String → Bool
eqStr a b with a ≟ b
... | yes _ = true
... | no _  = false

------------------------------------------------------------------------
-- Default text constants
------------------------------------------------------------------------

noDataText : String
noDataText = "No data available"
