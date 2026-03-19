{-# OPTIONS --without-K #-}

-- SvgRangeSlider: dual-thumb slider for min/max range selection
-- Like a slider but with two handles

module Agdelte.Svg.Controls.RangeSlider where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; circle')
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Svg.Events using (onSvgClick)
open import Agdelte.Svg.Path using (Point; x; y)
open import Agdelte.Svg.Math using (clamp)

------------------------------------------------------------------------
-- Range Slider Style (reusing concepts from Slider)
------------------------------------------------------------------------

record RangeSliderStyle : Set where
  constructor mkRangeSliderStyle
  field
    trackColor     : String
    fillColor      : String    -- selected range color
    thumbColor     : String
    thumbBorder    : String
    thumbRadius    : Float
    trackThickness : Float
    trackRadius    : Float

open RangeSliderStyle public

defaultRangeSliderStyle : RangeSliderStyle
defaultRangeSliderStyle = mkRangeSliderStyle
  "#e5e7eb"    -- light gray track
  "#3b82f6"    -- blue fill
  "#ffffff"    -- white thumb
  "#3b82f6"    -- blue border
  10.0
  6.0
  3.0

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  valueToRatio : Float → Float → Float → Float
  valueToRatio minV maxV val =
    let range = maxV - minV
    in if range ≤ᵇ 0.0 then 0.0
       else clamp 0.0 1.0 ((val - minV) ÷ range)

------------------------------------------------------------------------
-- Range Slider
------------------------------------------------------------------------

svgRangeSlider : ∀ {M Msg}
               → Float → Float → Float     -- x, y, length
               → Float → Float             -- min, max
               → Float → Float             -- low value, high value
               → RangeSliderStyle
               → (Float → Msg) → (Float → Msg)  -- onLowChange(newVal), onHighChange(newVal)
               → Node M Msg
svgRangeSlider px py len minV maxV lowV highV sty onLow onHigh =
  let lowRatio = valueToRatio minV maxV lowV
      highRatio = valueToRatio minV maxV highV
      thick = trackThickness sty
      thumbR = thumbRadius sty
      trackY = py - thick ÷ 2.0
      lowX = px + lowRatio * len
      highX = px + highRatio * len
      fillX = lowX
      fillW = if lowX ≤ᵇ highX then highX - lowX else 0.0
      -- Compute value from click/drag position on the track
      posToVal = λ (pt : Point) → let clickRatio = clamp 0.0 1.0 ((x pt - px) ÷ len)
                                   in minV + clickRatio * (maxV - minV)
      computeLow = λ (pt : Point) → onLow (posToVal pt)
      computeHigh = λ (pt : Point) → onHigh (posToVal pt)
      hitH = if thumbR * 2.0 ≤ᵇ thick then thick else thumbR * 2.0
      hitY = py - hitH ÷ 2.0
  in g ( attr "class" "svg-range-slider" ∷ [] )
       ( -- Track background
         rect' ( attrX px
               ∷ attrY trackY
               ∷ widthF len
               ∷ heightF thick
               ∷ fill_ (trackColor sty)
               ∷ rxF (trackRadius sty)
               ∷ ryF (trackRadius sty)
               ∷ [] ) []
       -- Selected range fill
       ∷ rect' ( attrX fillX
               ∷ attrY trackY
               ∷ widthF fillW
               ∷ heightF thick
               ∷ fill_ (fillColor sty)
               ∷ [] ) []
       -- Low thumb (draggable via click position)
       ∷ circle' ( attrCx lowX
                 ∷ attrCy py
                 ∷ rF thumbR
                 ∷ fill_ (thumbColor sty)
                 ∷ stroke_ (thumbBorder sty)
                 ∷ strokeWidthF 2.0
                 ∷ attr "cursor" "pointer"
                 ∷ onSvgClick computeLow
                 ∷ [] ) []
       -- High thumb (draggable via click position)
       ∷ circle' ( attrCx highX
                 ∷ attrCy py
                 ∷ rF thumbR
                 ∷ fill_ (thumbColor sty)
                 ∷ stroke_ (thumbBorder sty)
                 ∷ strokeWidthF 2.0
                 ∷ attr "cursor" "pointer"
                 ∷ onSvgClick computeHigh
                 ∷ [] ) []
       -- Invisible click target overlay for the full track
       -- Clicks on left half go to low thumb, right half to high thumb
       ∷ rect' ( attrX px
               ∷ attrY hitY
               ∷ widthF len
               ∷ heightF hitH
               ∷ fill_ "transparent"
               ∷ attr "cursor" "pointer"
               ∷ onSvgClick (λ pt →
                   let val = posToVal pt
                       midVal = minV + (lowRatio + highRatio) * 0.5 * (maxV - minV)
                   in if val ≤ᵇ midVal then onLow val else onHigh val)
               ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Simple Range Slider
------------------------------------------------------------------------

svgRangeSliderSimple : ∀ {M Msg}
                     → Float → Float → Float
                     → Float → Float
                     → Float → Float
                     → (Float → Msg) → (Float → Msg)
                     → Node M Msg
svgRangeSliderSimple px py len minV maxV lowV highV onLow onHigh =
  svgRangeSlider px py len minV maxV lowV highV defaultRangeSliderStyle onLow onHigh

-- Price range slider (0-1000)
svgPriceRangeSlider : ∀ {M Msg}
                    → Float → Float → Float
                    → Float → Float
                    → (Float → Msg) → (Float → Msg)
                    → Node M Msg
svgPriceRangeSlider px py len lowV highV onLow onHigh =
  svgRangeSlider px py len 0.0 1000.0 lowV highV defaultRangeSliderStyle onLow onHigh
