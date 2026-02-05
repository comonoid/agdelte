{-# OPTIONS --without-K #-}

-- Css.Variables: CSS custom property helpers
--
-- CSS variables already work via raw declarations:
--   "--primary" ∶ "#3b82f6"
-- and via Color.var for typed color references:
--   color' (var "primary")  →  color: var(--primary)
--
-- This module adds thin convenience for non-color uses.

module Agdelte.Css.Variables where

open import Data.String using (String; _++_)

open import Agdelte.Css.Decl using (Decl; _∶_)

------------------------------------------------------------------------
-- Define
------------------------------------------------------------------------

-- Define a CSS custom property on an element
cssVar : String → String → Decl
cssVar name value = ("--" ++ name) ∶ value

------------------------------------------------------------------------
-- Reference
------------------------------------------------------------------------

-- Reference a CSS variable as a raw value string
-- Use with any property: "border-radius" ∶ varRef "radius"
varRef : String → String
varRef name = "var(--" ++ name ++ ")"
