{-# OPTIONS --without-K #-}

-- SVG Gauge / Meter
-- Circular and semicircular value displays

module Agdelte.Svg.Controls.Gauges.Gauge where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; svgText; line')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

private
  pi : Float
  pi = 3.14159265359

  sin : Float → Float
  sin x = x - (x * x * x ÷ 6.0)
        + (x * x * x * x * x ÷ 120.0)
        - (x * x * x * x * x * x * x ÷ 5040.0)

  cos : Float → Float
  cos x = 1.0 - (x * x ÷ 2.0)
        + (x * x * x * x ÷ 24.0)
        - (x * x * x * x * x * x ÷ 720.0)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

-- Threshold zones for coloring
record GaugeThreshold : Set where
  constructor mkThreshold
  field
    thresholdValue : Float
    thresholdColor : String

open GaugeThreshold public

record GaugeConfig : Set where
  constructor mkGaugeConfig
  field
    gcMin         : Float
    gcMax         : Float
    gcThresholds  : List GaugeThreshold    -- (value, color) pairs
    gcLabel       : Maybe String
    gcShowValue   : Bool
    gcShowTicks   : Bool
    gcTickCount   : ℕ
    gcNeedleColor : String
    gcBackColor   : String

open GaugeConfig public

defaultGaugeConfig : Float → Float → GaugeConfig
defaultGaugeConfig minV maxV = mkGaugeConfig
  minV maxV
  ( mkThreshold (minV + (maxV - minV) * 0.6) "#22c55e"
  ∷ mkThreshold (minV + (maxV - minV) * 0.8) "#f59e0b"
  ∷ mkThreshold maxV "#ef4444"
  ∷ [] )
  nothing true true 10 "#1e293b" "#e2e8f0"

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  polarToCart : Float → Float → Float → Float → Float × Float
  polarToCart cx cy r angle = (cx + r * cos angle , cy + r * sin angle)

  valueToAngle : Float → Float → Float → Float → Float → Float
  valueToAngle minV maxV startA endA v =
    let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
        norm = (v - minV) ÷ range
    in startA + norm * (endA - startA)

  -- Get color based on value and thresholds
  getColor : Float → List GaugeThreshold → String → String
  getColor _ [] defaultC = defaultC
  getColor v (t ∷ ts) defaultC =
    if v <ᵇ thresholdValue t
    then thresholdColor t
    else getColor v ts defaultC

------------------------------------------------------------------------
-- Arc path building
------------------------------------------------------------------------

private
  arcPath : Float → Float → Float → Float → Float → String
  arcPath cx cy r startA endA =
    let (x1 , y1) = polarToCart cx cy r startA
        (x2 , y2) = polarToCart cx cy r endA
        largeArc = if (endA - startA) <ᵇ pi then "0" else "1"
    in "M " ++ showFloat x1 ++ " " ++ showFloat y1
       ++ " A " ++ showFloat r ++ " " ++ showFloat r
       ++ " 0 " ++ largeArc ++ " 1 "
       ++ showFloat x2 ++ " " ++ showFloat y2

------------------------------------------------------------------------
-- Semicircle Gauge (180 degrees)
------------------------------------------------------------------------

-- | Half-circle gauge (like speedometer)
semicircleGauge : ∀ {M A}
                → Float → Float           -- center x, y
                → Float                   -- radius
                → GaugeConfig
                → Float                   -- current value
                → Node M A
semicircleGauge {M} {A} cx cy radius config value =
  let startAngle = pi            -- left (180 degrees)
      endAngle = 0.0             -- right (0 degrees)
      minV = gcMin config
      maxV = gcMax config
      clampedV = if value <ᵇ minV then minV
                 else if maxV <ᵇ value then maxV else value
      needleAngle = valueToAngle minV maxV startAngle endAngle clampedV
  in g ( attr "class" "svg-semicircle-gauge" ∷ [] )
       ( -- Background arc
         path' ( d_ (arcPath cx cy radius startAngle endAngle)
               ∷ fill_ "none"
               ∷ stroke_ (gcBackColor config)
               ∷ strokeWidthF 12.0
               ∷ attr "stroke-linecap" "round"
               ∷ [] ) []
       -- Colored progress arc
       ∷ path' ( d_ (arcPath cx cy radius startAngle needleAngle)
               ∷ fill_ "none"
               ∷ stroke_ (getColor clampedV (gcThresholds config) "#3b82f6")
               ∷ strokeWidthF 12.0
               ∷ attr "stroke-linecap" "round"
               ∷ [] ) []
       -- Needle
       ∷ renderNeedle cx cy (radius - 20.0) needleAngle (gcNeedleColor config)
       -- Ticks
       ∷ (if gcShowTicks config
          then g [] (renderTicks cx cy radius (gcTickCount config) minV maxV startAngle endAngle)
          else g [] [])
       -- Center dot
       ∷ circle' ( cxF cx ∷ cyF cy
                 ∷ rF 8.0
                 ∷ fill_ (gcNeedleColor config)
                 ∷ [] ) []
       -- Value display
       ∷ (if gcShowValue config
          then svgText ( xF cx ∷ yF (cy + 25.0)
                       ∷ attr "text-anchor" "middle"
                       ∷ attr "font-size" "18"
                       ∷ attr "font-weight" "bold"
                       ∷ fill_ "#1e293b"
                       ∷ [] )
                 ( text (showFloat clampedV) ∷ [] )
          else g [] [])
       -- Label
       ∷ (case gcLabel config of λ where
            nothing → g [] []
            (just lbl) →
              svgText ( xF cx ∷ yF (cy + 45.0)
                      ∷ attr "text-anchor" "middle"
                      ∷ attr "font-size" "12"
                      ∷ fill_ "#64748b"
                      ∷ [] )
                ( text lbl ∷ [] ))
       ∷ [] )
  where
    case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
    case x of f = f x

    renderNeedle : Float → Float → Float → Float → String → Node M A
    renderNeedle ncx ncy length angle color =
      let (tx , ty) = polarToCart ncx ncy length angle
      in line' ( x1F ncx ∷ y1F ncy
               ∷ x2F tx ∷ y2F ty
               ∷ stroke_ color
               ∷ strokeWidthF 3.0
               ∷ attr "stroke-linecap" "round"
               ∷ [] ) []

    renderTicks : Float → Float → Float → ℕ → Float → Float → Float → Float → List (Node M A)
    renderTicks _ _ _ zero _ _ _ _ = []
    renderTicks tcx tcy tr (suc n) minV maxV startA endA = go (suc n) 0
      where
        go : ℕ → ℕ → List (Node M A)
        go 0 _ = []
        go (suc remaining) idx =
          let t = fromℕ idx ÷ fromℕ n
              angle = startA + t * (endA - startA)
              (x1 , y1) = polarToCart tcx tcy (tr + 5.0) angle
              (x2 , y2) = polarToCart tcx tcy (tr + 12.0) angle
          in line' ( x1F x1 ∷ y1F y1
                   ∷ x2F x2 ∷ y2F y2
                   ∷ stroke_ "#94a3b8"
                   ∷ strokeWidthF 1.5
                   ∷ [] ) []
             ∷ go remaining (suc idx)

------------------------------------------------------------------------
-- Full Circle Gauge (270 degrees)
------------------------------------------------------------------------

-- | Full circle gauge (like dashboard meter)
fullGauge : ∀ {M A}
          → Float → Float → Float
          → GaugeConfig
          → Float
          → Node M A
fullGauge {M} {A} cx cy radius config value =
  let startAngle = pi * 0.75     -- 135 degrees (bottom-left)
      endAngle = pi * 2.25       -- 405 degrees (bottom-right)
      minV = gcMin config
      maxV = gcMax config
      clampedV = if value <ᵇ minV then minV
                 else if maxV <ᵇ value then maxV else value
      needleAngle = valueToAngle minV maxV startAngle endAngle clampedV
  in g ( attr "class" "svg-full-gauge" ∷ [] )
       ( -- Background arc
         path' ( d_ (arcPath cx cy radius startAngle endAngle)
               ∷ fill_ "none"
               ∷ stroke_ (gcBackColor config)
               ∷ strokeWidthF 10.0
               ∷ attr "stroke-linecap" "round"
               ∷ [] ) []
       -- Progress arc
       ∷ path' ( d_ (arcPath cx cy radius startAngle needleAngle)
               ∷ fill_ "none"
               ∷ stroke_ (getColor clampedV (gcThresholds config) "#3b82f6")
               ∷ strokeWidthF 10.0
               ∷ attr "stroke-linecap" "round"
               ∷ [] ) []
       -- Center content
       ∷ (if gcShowValue config
          then g []
                 ( svgText ( xF cx ∷ yF cy
                           ∷ attr "text-anchor" "middle"
                           ∷ attr "dominant-baseline" "middle"
                           ∷ attr "font-size" "24"
                           ∷ attr "font-weight" "bold"
                           ∷ fill_ "#1e293b"
                           ∷ [] )
                     ( text (showFloat clampedV) ∷ [] )
                 ∷ [] )
          else g [] [])
       -- Label below value
       ∷ (case gcLabel config of λ where
            nothing → g [] []
            (just lbl) →
              svgText ( xF cx ∷ yF (cy + 20.0)
                      ∷ attr "text-anchor" "middle"
                      ∷ attr "font-size" "12"
                      ∷ fill_ "#64748b"
                      ∷ [] )
                ( text lbl ∷ [] ))
       ∷ [] )
  where
    case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
    case x of f = f x

------------------------------------------------------------------------
-- Linear Gauge (horizontal/vertical bar)
------------------------------------------------------------------------

-- | Linear horizontal gauge
linearGaugeH : ∀ {M A}
             → Float → Float → Float → Float  -- x, y, width, height
             → GaugeConfig
             → Float
             → Node M A
linearGaugeH {M} {A} px py w h config value =
  let minV = gcMin config
      maxV = gcMax config
      clampedV = if value <ᵇ minV then minV
                 else if maxV <ᵇ value then maxV else value
      fillW = ((clampedV - minV) ÷ (maxV - minV)) * w
  in g ( attr "class" "svg-linear-gauge-h" ∷ [] )
       ( -- Background bar
         path' ( d_ (roundedRect px py w h 4.0)
               ∷ fill_ (gcBackColor config)
               ∷ [] ) []
       -- Fill bar
       ∷ path' ( d_ (roundedRect px py fillW h 4.0)
               ∷ fill_ (getColor clampedV (gcThresholds config) "#3b82f6")
               ∷ [] ) []
       -- Value text
       ∷ (if gcShowValue config
          then svgText ( xF (px + w + 10.0) ∷ yF (py + h ÷ 2.0)
                       ∷ attr "dominant-baseline" "middle"
                       ∷ attr "font-size" "14"
                       ∷ fill_ "#1e293b"
                       ∷ [] )
                 ( text (showFloat clampedV) ∷ [] )
          else g [] [])
       ∷ [] )
  where
    roundedRect : Float → Float → Float → Float → Float → String
    roundedRect rx ry rw rh rr =
      "M " ++ showFloat (rx + rr) ++ " " ++ showFloat ry
      ++ " H " ++ showFloat (rx + rw - rr)
      ++ " Q " ++ showFloat (rx + rw) ++ " " ++ showFloat ry ++ " "
              ++ showFloat (rx + rw) ++ " " ++ showFloat (ry + rr)
      ++ " V " ++ showFloat (ry + rh - rr)
      ++ " Q " ++ showFloat (rx + rw) ++ " " ++ showFloat (ry + rh) ++ " "
              ++ showFloat (rx + rw - rr) ++ " " ++ showFloat (ry + rh)
      ++ " H " ++ showFloat (rx + rr)
      ++ " Q " ++ showFloat rx ++ " " ++ showFloat (ry + rh) ++ " "
              ++ showFloat rx ++ " " ++ showFloat (ry + rh - rr)
      ++ " V " ++ showFloat (ry + rr)
      ++ " Q " ++ showFloat rx ++ " " ++ showFloat ry ++ " "
              ++ showFloat (rx + rr) ++ " " ++ showFloat ry
      ++ " Z"

-- | Linear vertical gauge
linearGaugeV : ∀ {M A}
             → Float → Float → Float → Float
             → GaugeConfig
             → Float
             → Node M A
linearGaugeV {M} {A} px py w h config value =
  let minV = gcMin config
      maxV = gcMax config
      clampedV = if value <ᵇ minV then minV
                 else if maxV <ᵇ value then maxV else value
      fillH = ((clampedV - minV) ÷ (maxV - minV)) * h
      fillY = py + h - fillH
  in g ( attr "class" "svg-linear-gauge-v" ∷ [] )
       ( -- Background
         path' ( d_ (roundedRectV px py w h 4.0)
               ∷ fill_ (gcBackColor config)
               ∷ [] ) []
       -- Fill (from bottom)
       ∷ path' ( d_ (roundedRectBottom px fillY w fillH 4.0)
               ∷ fill_ (getColor clampedV (gcThresholds config) "#3b82f6")
               ∷ [] ) []
       ∷ [] )
  where
    roundedRectV : Float → Float → Float → Float → Float → String
    roundedRectV rx ry rw rh rr =
      "M " ++ showFloat (rx + rr) ++ " " ++ showFloat ry
      ++ " H " ++ showFloat (rx + rw - rr)
      ++ " Q " ++ showFloat (rx + rw) ++ " " ++ showFloat ry ++ " "
              ++ showFloat (rx + rw) ++ " " ++ showFloat (ry + rr)
      ++ " V " ++ showFloat (ry + rh - rr)
      ++ " Q " ++ showFloat (rx + rw) ++ " " ++ showFloat (ry + rh) ++ " "
              ++ showFloat (rx + rw - rr) ++ " " ++ showFloat (ry + rh)
      ++ " H " ++ showFloat (rx + rr)
      ++ " Q " ++ showFloat rx ++ " " ++ showFloat (ry + rh) ++ " "
              ++ showFloat rx ++ " " ++ showFloat (ry + rh - rr)
      ++ " V " ++ showFloat (ry + rr)
      ++ " Q " ++ showFloat rx ++ " " ++ showFloat ry ++ " "
              ++ showFloat (rx + rr) ++ " " ++ showFloat ry
      ++ " Z"

    roundedRectBottom : Float → Float → Float → Float → Float → String
    roundedRectBottom rx ry rw rh rr =
      if rh ≤ᵇ 0.0 then ""
      else "M " ++ showFloat rx ++ " " ++ showFloat ry
           ++ " H " ++ showFloat (rx + rw)
           ++ " V " ++ showFloat (ry + rh - rr)
           ++ " Q " ++ showFloat (rx + rw) ++ " " ++ showFloat (ry + rh) ++ " "
                   ++ showFloat (rx + rw - rr) ++ " " ++ showFloat (ry + rh)
           ++ " H " ++ showFloat (rx + rr)
           ++ " Q " ++ showFloat rx ++ " " ++ showFloat (ry + rh) ++ " "
                   ++ showFloat rx ++ " " ++ showFloat (ry + rh - rr)
           ++ " Z"

------------------------------------------------------------------------
-- Simple constructors
------------------------------------------------------------------------

-- | Simple percentage gauge (0-100)
percentGauge : ∀ {M A}
             → Float → Float → Float
             → Float                   -- percentage 0-100
             → Node M A
percentGauge cx cy radius pct =
  semicircleGauge cx cy radius (defaultGaugeConfig 0.0 100.0) pct

-- | Temperature gauge
tempGauge : ∀ {M A}
          → Float → Float → Float
          → Float                      -- temperature
          → Float → Float              -- min, max
          → Node M A
tempGauge cx cy radius temp minT maxT =
  fullGauge cx cy radius config temp
  where
    config = mkGaugeConfig minT maxT
      ( mkThreshold (minT + (maxT - minT) * 0.3) "#3b82f6"
      ∷ mkThreshold (minT + (maxT - minT) * 0.7) "#22c55e"
      ∷ mkThreshold maxT "#ef4444"
      ∷ [] )
      (just "°C") true false 10 "#1e293b" "#e2e8f0"

-- | Speed gauge (0-maxSpeed)
speedGauge : ∀ {M A}
           → Float → Float → Float
           → Float                     -- current speed
           → Float                     -- max speed
           → Node M A
speedGauge cx cy radius speed maxSpeed =
  semicircleGauge cx cy radius config speed
  where
    config = mkGaugeConfig 0.0 maxSpeed
      ( mkThreshold (maxSpeed * 0.5) "#22c55e"
      ∷ mkThreshold (maxSpeed * 0.75) "#f59e0b"
      ∷ mkThreshold maxSpeed "#ef4444"
      ∷ [] )
      (just "km/h") true true 10 "#1e293b" "#e2e8f0"
