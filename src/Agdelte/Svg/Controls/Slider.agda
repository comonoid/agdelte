{-# OPTIONS --without-K #-}

-- SvgSlider: draggable value slider for SVG
-- Horizontal or vertical orientation, customizable track and thumb

module Agdelte.Svg.Controls.Slider where

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

------------------------------------------------------------------------
-- Slider Orientation
------------------------------------------------------------------------

data Orientation : Set where
  Horizontal : Orientation
  Vertical   : Orientation

------------------------------------------------------------------------
-- Slider Style
------------------------------------------------------------------------

record SliderStyle : Set where
  constructor mkSliderStyle
  field
    trackColor     : String    -- track background
    trackFill      : String    -- filled portion color
    thumbColor     : String    -- thumb color
    thumbBorder    : String    -- thumb border
    thumbRadius    : Float     -- thumb size (radius)
    trackThickness : Float     -- track height/width
    trackRadius    : Float     -- track corner radius

open SliderStyle public

-- Default style (blue theme)
defaultSliderStyle : SliderStyle
defaultSliderStyle = mkSliderStyle
  "#e5e7eb"    -- light gray track
  "#3b82f6"    -- blue fill
  "#ffffff"    -- white thumb
  "#3b82f6"    -- blue thumb border
  10.0         -- thumb radius
  6.0          -- track thickness
  3.0          -- track corner radius

-- Dark theme style
darkSliderStyle : SliderStyle
darkSliderStyle = mkSliderStyle
  "#374151"    -- dark gray track
  "#60a5fa"    -- lighter blue fill
  "#1f2937"    -- dark thumb
  "#60a5fa"    -- blue border
  10.0
  6.0
  3.0

-- Minimal style (thin)
minimalSliderStyle : SliderStyle
minimalSliderStyle = mkSliderStyle
  "#d1d5db"
  "#6366f1"    -- indigo
  "#ffffff"
  "#6366f1"
  8.0
  4.0
  2.0

------------------------------------------------------------------------
-- Slider Config
------------------------------------------------------------------------

record SliderConfig (Msg : Set) : Set where
  constructor mkSliderConfig
  field
    sliderX       : Float        -- x position
    sliderY       : Float        -- y position
    sliderLength  : Float        -- track length (width for H, height for V)
    orientation   : Orientation
    minVal        : Float        -- minimum value
    maxVal        : Float        -- maximum value
    sliderStyle   : SliderStyle
    onChange      : Float → Msg  -- callback with new value

open SliderConfig public

------------------------------------------------------------------------
-- Value helpers
------------------------------------------------------------------------

private
  clamp : Float → Float → Float → Float
  clamp lo hi v =
    if v ≤ᵇ lo then lo
    else if hi ≤ᵇ v then hi
    else v

  -- Convert value to position (0-1 range)
  valueToRatio : Float → Float → Float → Float
  valueToRatio minV maxV val =
    let range = maxV - minV
    in if range ≤ᵇ 0.0 then 0.0
       else clamp 0.0 1.0 ((val - minV) ÷ range)

------------------------------------------------------------------------
-- Horizontal Slider
------------------------------------------------------------------------

svgSliderH : ∀ {M Msg}
           → Float → Float → Float  -- x, y, length
           → Float → Float → Float  -- min, max, current value
           → SliderStyle
           → (Float → Msg)          -- onChange(newValue)
           → Node M Msg
svgSliderH px py len minV maxV val sty onChange =
  let ratio = valueToRatio minV maxV val
      thick = trackThickness sty
      thumbR = thumbRadius sty
      trackY = py - thick ÷ 2.0
      fillW = ratio * len
      thumbX = px + ratio * len
  in g ( attr "class" "svg-slider-h" ∷ [] )
       ( -- Track background
         rect' ( attrX px
               ∷ attrY trackY
               ∷ widthF len
               ∷ heightF thick
               ∷ fill_ (trackColor sty)
               ∷ rxF (trackRadius sty)
               ∷ ryF (trackRadius sty)
               ∷ [] ) []
       -- Filled portion
       ∷ rect' ( attrX px
               ∷ attrY trackY
               ∷ widthF fillW
               ∷ heightF thick
               ∷ fill_ (trackFill sty)
               ∷ rxF (trackRadius sty)
               ∷ ryF (trackRadius sty)
               ∷ [] ) []
       -- Thumb
       ∷ circle' ( attrCx thumbX
                 ∷ attrCy py
                 ∷ rF thumbR
                 ∷ fill_ (thumbColor sty)
                 ∷ stroke_ (thumbBorder sty)
                 ∷ strokeWidthF 2.0
                 ∷ attr "cursor" "pointer"
                 ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Vertical Slider
------------------------------------------------------------------------

svgSliderV : ∀ {M Msg}
           → Float → Float → Float  -- x, y, length
           → Float → Float → Float  -- min, max, current value
           → SliderStyle
           → (Float → Msg)
           → Node M Msg
svgSliderV px py len minV maxV val sty onChange =
  let ratio = valueToRatio minV maxV val
      thick = trackThickness sty
      thumbR = thumbRadius sty
      trackX = px - thick ÷ 2.0
      -- Vertical: bottom is min, top is max (invert ratio)
      invRatio = 1.0 - ratio
      fillH = ratio * len
      thumbY = py + invRatio * len
  in g ( attr "class" "svg-slider-v" ∷ [] )
       ( -- Track background
         rect' ( attrX trackX
               ∷ attrY py
               ∷ widthF thick
               ∷ heightF len
               ∷ fill_ (trackColor sty)
               ∷ rxF (trackRadius sty)
               ∷ ryF (trackRadius sty)
               ∷ [] ) []
       -- Filled portion (from bottom)
       ∷ rect' ( attrX trackX
               ∷ attrY (py + invRatio * len)
               ∷ widthF thick
               ∷ heightF fillH
               ∷ fill_ (trackFill sty)
               ∷ rxF (trackRadius sty)
               ∷ ryF (trackRadius sty)
               ∷ [] ) []
       -- Thumb
       ∷ circle' ( attrCx px
                 ∷ attrCy thumbY
                 ∷ rF thumbR
                 ∷ fill_ (thumbColor sty)
                 ∷ stroke_ (thumbBorder sty)
                 ∷ strokeWidthF 2.0
                 ∷ attr "cursor" "pointer"
                 ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Generic Slider (based on orientation)
------------------------------------------------------------------------

svgSlider : ∀ {M Msg}
          → SliderConfig Msg
          → Float                -- current value
          → Node M Msg
svgSlider cfg val with orientation cfg
... | Horizontal = svgSliderH (sliderX cfg) (sliderY cfg) (sliderLength cfg)
                              (minVal cfg) (maxVal cfg) val
                              (sliderStyle cfg) (onChange cfg)
... | Vertical   = svgSliderV (sliderX cfg) (sliderY cfg) (sliderLength cfg)
                              (minVal cfg) (maxVal cfg) val
                              (sliderStyle cfg) (onChange cfg)

------------------------------------------------------------------------
-- Simple Slider (default style)
------------------------------------------------------------------------

svgSliderSimple : ∀ {M Msg}
                → Float → Float → Float  -- x, y, length
                → Float → Float → Float  -- min, max, current
                → (Float → Msg)
                → Node M Msg
svgSliderSimple px py len minV maxV val onChange =
  svgSliderH px py len minV maxV val defaultSliderStyle onChange

------------------------------------------------------------------------
-- Volume Slider (0-100)
------------------------------------------------------------------------

svgVolumeSlider : ∀ {M Msg}
                → Float → Float → Float  -- x, y, length
                → Float                  -- current (0-100)
                → (Float → Msg)
                → Node M Msg
svgVolumeSlider px py len val onChange =
  svgSliderH px py len 0.0 100.0 val defaultSliderStyle onChange

------------------------------------------------------------------------
-- Percentage Slider (0-1)
------------------------------------------------------------------------

svgPercentSlider : ∀ {M Msg}
                 → Float → Float → Float  -- x, y, length
                 → Float                  -- current (0-1)
                 → (Float → Msg)
                 → Node M Msg
svgPercentSlider px py len val onChange =
  svgSliderH px py len 0.0 1.0 val defaultSliderStyle onChange
