{-# OPTIONS --without-K #-}

-- Css.Properties: typed CSS property constructors
--
-- Each constructor returns a Decl, composable with Style.
-- Typed constructors validate property-value pairing at compile time:
--   padding' (px 16)         ✓  Length → Decl
--   color' (hex "#333")      ✓  Color → Decl
--   padding' (hex "#333")    ✗  type error!
--
-- Raw string escape hatch always works alongside typed:
--   padding' (px 16) ∷ "font-family" ∶ "sans-serif" ∷ []

module Agdelte.Css.Properties where

open import Data.String using (String; _++_)

open import Agdelte.Css.Decl using (Decl; _∶_)
open import Agdelte.Css.Length using (Length; showLength)
open import Agdelte.Css.Color using (Color; showColor)

------------------------------------------------------------------------
-- Box model
------------------------------------------------------------------------

padding' : Length → Decl
padding' l = "padding" ∶ showLength l

padding2 : Length → Length → Decl
padding2 v h = "padding" ∶ (showLength v ++ " " ++ showLength h)

padding4 : Length → Length → Length → Length → Decl
padding4 t r b l = "padding" ∶ (showLength t ++ " " ++ showLength r ++ " " ++ showLength b ++ " " ++ showLength l)

margin' : Length → Decl
margin' l = "margin" ∶ showLength l

margin2 : Length → Length → Decl
margin2 v h = "margin" ∶ (showLength v ++ " " ++ showLength h)

margin4 : Length → Length → Length → Length → Decl
margin4 t r b l = "margin" ∶ (showLength t ++ " " ++ showLength r ++ " " ++ showLength b ++ " " ++ showLength l)

------------------------------------------------------------------------
-- Sizing
------------------------------------------------------------------------

width' : Length → Decl
width' l = "width" ∶ showLength l

height' : Length → Decl
height' l = "height" ∶ showLength l

maxWidth' : Length → Decl
maxWidth' l = "max-width" ∶ showLength l

maxHeight' : Length → Decl
maxHeight' l = "max-height" ∶ showLength l

minWidth' : Length → Decl
minWidth' l = "min-width" ∶ showLength l

minHeight' : Length → Decl
minHeight' l = "min-height" ∶ showLength l

------------------------------------------------------------------------
-- Typography
------------------------------------------------------------------------

fontSize' : Length → Decl
fontSize' l = "font-size" ∶ showLength l

lineHeight' : Length → Decl
lineHeight' l = "line-height" ∶ showLength l

------------------------------------------------------------------------
-- Colors
------------------------------------------------------------------------

color' : Color → Decl
color' c = "color" ∶ showColor c

background' : Color → Decl
background' c = "background" ∶ showColor c

backgroundColor' : Color → Decl
backgroundColor' c = "background-color" ∶ showColor c

borderColor' : Color → Decl
borderColor' c = "border-color" ∶ showColor c

------------------------------------------------------------------------
-- Spacing
------------------------------------------------------------------------

gap' : Length → Decl
gap' l = "gap" ∶ showLength l

------------------------------------------------------------------------
-- Border
------------------------------------------------------------------------

borderRadius' : Length → Decl
borderRadius' l = "border-radius" ∶ showLength l
