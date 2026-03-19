{-# OPTIONS --without-K #-}

-- Shared helpers for SVG chart controls
-- Extracted from Line.agda and Area.agda

module Agdelte.Svg.Controls.Charts.Helpers where

open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- Data point
------------------------------------------------------------------------

record DataPoint : Set where
  constructor mkDataPoint
  field
    dpX : Float
    dpY : Float

open DataPoint public

------------------------------------------------------------------------
-- Extraction
------------------------------------------------------------------------

extractX extractY : List DataPoint → List Float
extractX [] = []
extractX (p ∷ ps) = dpX p ∷ extractX ps
extractY [] = []
extractY (p ∷ ps) = dpY p ∷ extractY ps

------------------------------------------------------------------------
-- Scaling (maps data values to pixel coordinates)
------------------------------------------------------------------------

scaleX : Float → Float → Float → Float → Float → Float
scaleX minX maxX w px vx =
  let range = if (maxX - minX) ≤ᵇ 0.0 then 1.0 else maxX - minX
  in px + ((vx - minX) ÷ range) * w

scaleY : Float → Float → Float → Float → Float → Float
scaleY minY maxY h py vy =
  let range = if (maxY - minY) ≤ᵇ 0.0 then 1.0 else maxY - minY
  in py + h - ((vy - minY) ÷ range) * h
