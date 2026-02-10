{-# OPTIONS --without-K #-}

-- SvgSparkline: mini inline chart
-- Small line chart for showing trends in limited space

module Agdelte.Svg.Controls.Sparkline where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _∸_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (g; circle')
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (cxF to attrCx; cyF to attrCy)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Sparkline Style
------------------------------------------------------------------------

record SparklineStyle : Set where
  constructor mkSparklineStyle
  field
    lineColor   : String
    lineWidth   : Float
    fillColor   : String    -- area fill (or "none")
    dotColor    : String
    dotRadius   : Float

open SparklineStyle public

defaultSparklineStyle : SparklineStyle
defaultSparklineStyle = mkSparklineStyle
  "#3b82f6"      -- blue line
  1.5
  "none"
  "#3b82f6"
  2.0

greenSparklineStyle : SparklineStyle
greenSparklineStyle = mkSparklineStyle "#22c55e" 1.5 "none" "#22c55e" 2.0

redSparklineStyle : SparklineStyle
redSparklineStyle = mkSparklineStyle "#ef4444" 1.5 "none" "#ef4444" 2.0

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : List Float → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  findMin : List Float → Float → Float
  findMin [] acc = acc
  findMin (x ∷ xs) acc = findMin xs (if x <ᵇ acc then x else acc)

  findMax : List Float → Float → Float
  findMax [] acc = acc
  findMax (x ∷ xs) acc = findMax xs (if acc <ᵇ x then x else acc)

  getLast : List Float → Float
  getLast [] = 0.0
  getLast (x ∷ []) = x
  getLast (_ ∷ xs) = getLast xs

------------------------------------------------------------------------
-- Path generation
------------------------------------------------------------------------

private
  buildPath : Float → Float → Float → Float → Float → Float
            → List Float → ℕ → ℕ → String
  buildPath _ _ _ _ _ _ [] _ _ = ""
  buildPath px py w h minV range (v ∷ vs) idx total =
    let totalF = fromℕ total
        stepX = if totalF ≤ᵇ 1.0 then 0.0 else w ÷ (totalF - 1.0)
        xPos = px + fromℕ idx * stepX
        yPos = py + h - ((v - minV) ÷ range) * h
        prefix = if idx ≡ᵇ 0 then "M " else " L "
    in prefix ++ showFloat xPos ++ " " ++ showFloat yPos
       ++ buildPath px py w h minV range vs (suc idx) total
    where
      open import Data.Nat using (_≡ᵇ_)

------------------------------------------------------------------------
-- Sparkline
------------------------------------------------------------------------

svgSparkline : ∀ {M Msg}
             → Float → Float → Float → Float  -- x, y, width, height
             → List Float                     -- data values
             → SparklineStyle
             → Node M Msg
svgSparkline px py w h dataVals sty =
  let total = listLen dataVals
      minV = findMin dataVals 1.0e10
      maxV = findMax dataVals (0.0 - 1.0e10)
      range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
      pathD = buildPath px py w h minV range dataVals 0 total
      lastV = getLast dataVals
      lastY = py + h - ((lastV - minV) ÷ range) * h
  in g ( attr "class" "svg-sparkline" ∷ [] )
       ( elem "path" ( d_ pathD
                     ∷ fill_ "none"
                     ∷ stroke_ (lineColor sty)
                     ∷ strokeWidthF (lineWidth sty)
                     ∷ attr "stroke-linecap" "round"
                     ∷ attr "stroke-linejoin" "round"
                     ∷ [] ) []
       ∷ (if dotRadius sty ≤ᵇ 0.0
          then g [] []
          else circle' ( attrCx (px + w)
                       ∷ attrCy lastY
                       ∷ rF (dotRadius sty)
                       ∷ fill_ (dotColor sty)
                       ∷ [] ) [])
       ∷ [] )

------------------------------------------------------------------------
-- Simple Sparklines
------------------------------------------------------------------------

svgSparklineSimple : ∀ {M Msg}
                   → Float → Float → Float → Float
                   → List Float
                   → Node M Msg
svgSparklineSimple px py w h vals =
  svgSparkline px py w h vals defaultSparklineStyle

svgTrendSparkline : ∀ {M Msg}
                  → Float → Float → Float → Float
                  → List Float
                  → Node M Msg
svgTrendSparkline px py w h vals =
  let trend = calcTrend vals
      sty = if trend then greenSparklineStyle else redSparklineStyle
  in svgSparkline px py w h vals sty
  where
    calcTrend : List Float → Bool
    calcTrend [] = true
    calcTrend (x ∷ []) = true
    calcTrend (first ∷ rest) = first ≤ᵇ getLast rest
