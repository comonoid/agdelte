{-# OPTIONS --without-K #-}

-- SVG Radar / Spider Chart
-- Multi-dimensional data comparison

module Agdelte.Svg.Controls.Charts.Radar where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; svgText; line'; polygon')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

private
  pi : Float
  pi = 3.14159265359

  -- Taylor series approximations for sin/cos
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

record RadarAxis : Set where
  constructor mkRadarAxis
  field
    axisName : String
    axisMax  : Float          -- maximum value for this axis

open RadarAxis public

record RadarSeries : Set where
  constructor mkRadarSeries
  field
    radarName   : String
    radarColor  : String
    radarValues : List Float  -- one value per axis (in order)

open RadarSeries public

record RadarConfig : Set where
  constructor mkRadarConfig
  field
    rcRadius     : Float      -- outer radius
    rcShowGrid   : Bool       -- show concentric rings
    rcGridLevels : ℕ          -- number of grid rings
    rcShowLabels : Bool       -- show axis labels
    rcShowDots   : Bool       -- show data points
    rcFillOpacity : Float     -- area fill opacity

open RadarConfig public

defaultRadarConfig : Float → RadarConfig
defaultRadarConfig r = mkRadarConfig r true 5 true true 0.25

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  -- Get angle for axis n of total axes
  axisAngle : ℕ → ℕ → Float
  axisAngle n total =
    let angle = (fromℕ n ÷ fromℕ total) * 2.0 * pi
    in angle - (pi ÷ 2.0)  -- start from top

  -- Convert polar to cartesian
  polarToCart : Float → Float → Float → Float → Float × Float
  polarToCart cx cy r angle = (cx + r * cos angle , cy + r * sin angle)

------------------------------------------------------------------------
-- Grid rendering (concentric polygons)
------------------------------------------------------------------------

private
  renderGridLevel : ∀ {M A} → Float → Float → Float → ℕ → Float → Node M A
  renderGridLevel cx cy radius numAxes levelRadius =
    let points = buildGridPoints numAxes 0 levelRadius
    in polygon' ( attr "points" points
                ∷ fill_ "none"
                ∷ stroke_ "#e5e7eb"
                ∷ strokeWidthF 1.0
                ∷ [] ) []
    where
      buildGridPoints : ℕ → ℕ → Float → String
      buildGridPoints 0 _ _ = ""
      buildGridPoints (suc remaining) idx r' =
        let angle = axisAngle idx numAxes
            (px , py) = polarToCart cx cy r' angle
            sep = if remaining ≡ᵇ 1 then "" else " "
        in showFloat px ++ "," ++ showFloat py ++ sep
           ++ buildGridPoints remaining (suc idx) r'
        where
          open import Data.Nat using (_≡ᵇ_)

  renderGrid : ∀ {M A} → Float → Float → Float → ℕ → ℕ → List (Node M A)
  renderGrid {M} {A} cx cy radius levels numAxes = go levels
    where
      go : ℕ → List (Node M A)
      go 0 = []
      go (suc n) =
        let level = suc n
            levelR = (fromℕ level ÷ fromℕ levels) * radius
        in renderGridLevel cx cy radius numAxes levelR ∷ go n

------------------------------------------------------------------------
-- Axis lines rendering
------------------------------------------------------------------------

private
  renderAxisLines : ∀ {M A} → Float → Float → Float → ℕ → List (Node M A)
  renderAxisLines {M} {A} cx cy radius numAxes = go numAxes 0
    where
      go : ℕ → ℕ → List (Node M A)
      go 0 _ = []
      go (suc remaining) idx =
        let angle = axisAngle idx numAxes
            (px , py) = polarToCart cx cy radius angle
        in line' ( x1F cx ∷ y1F cy
                 ∷ x2F px ∷ y2F py
                 ∷ stroke_ "#cbd5e1"
                 ∷ strokeWidthF 1.0
                 ∷ [] ) []
           ∷ go remaining (suc idx)

------------------------------------------------------------------------
-- Axis labels rendering
------------------------------------------------------------------------

private
  renderAxisLabels : ∀ {M A} → Float → Float → Float → List RadarAxis → List (Node M A)
  renderAxisLabels {M} {A} cx cy radius axes = go axes 0 (listLen axes)
    where
      go : List RadarAxis → ℕ → ℕ → List (Node M A)
      go [] _ _ = []
      go (ax ∷ rest) idx total =
        let angle = axisAngle idx total
            labelR = radius + 15.0
            (lx , ly) = polarToCart cx cy labelR angle
            anchor = if cos angle <ᵇ (0.0 - 0.1) then "end"
                     else if cos angle <ᵇ 0.1 then "middle"
                     else "start"
        in svgText ( xF lx ∷ yF ly
                   ∷ attr "text-anchor" anchor
                   ∷ attr "dominant-baseline" "middle"
                   ∷ attr "font-size" "11"
                   ∷ fill_ "#374151"
                   ∷ [] )
             ( text (axisName ax) ∷ [] )
           ∷ go rest (suc idx) total

------------------------------------------------------------------------
-- Series data polygon
------------------------------------------------------------------------

private
  renderSeriesPolygon : ∀ {M A}
                      → Float → Float → Float
                      → List RadarAxis → RadarSeries
                      → Bool → Float
                      → Node M A
  renderSeriesPolygon {M} {A} cx cy radius axes series showDots opacity =
    let numAxes = listLen axes
        points = buildPoints axes (radarValues series) 0 numAxes
    in g ( attr "class" ("radar-series-" ++ radarName series) ∷ [] )
         ( -- Filled polygon
           polygon' ( attr "points" points
                    ∷ fill_ (radarColor series)
                    ∷ attr "opacity" (showFloat opacity)
                    ∷ stroke_ (radarColor series)
                    ∷ strokeWidthF 2.0
                    ∷ [] ) []
         -- Data dots
         ∷ (if showDots
            then g [] (renderDots cx cy radius axes (radarValues series) (radarColor series) 0 numAxes)
            else g [] [])
         ∷ [] )
    where
      buildPoints : List RadarAxis → List Float → ℕ → ℕ → String
      buildPoints [] _ _ _ = ""
      buildPoints _ [] _ _ = ""
      buildPoints (ax ∷ restAx) (v ∷ restV) idx total =
        let angle = axisAngle idx total
            valueR = (v ÷ axisMax ax) * radius
            (px , py) = polarToCart cx cy valueR angle
            sep = if listLen restAx ≡ᵇ 0 then "" else " "
        in showFloat px ++ "," ++ showFloat py ++ sep
           ++ buildPoints restAx restV (suc idx) total
        where
          open import Data.Nat using (_≡ᵇ_)

      renderDots : Float → Float → Float → List RadarAxis → List Float → String → ℕ → ℕ → List (Node M A)
      renderDots _ _ _ [] _ _ _ _ = []
      renderDots _ _ _ _ [] _ _ _ = []
      renderDots cx' cy' r' (ax ∷ restAx) (v ∷ restV) color idx total =
        let angle = axisAngle idx total
            valueR = (v ÷ axisMax ax) * r'
            (px , py) = polarToCart cx' cy' valueR angle
        in circle' ( cxF px ∷ cyF py
                   ∷ rF 4.0
                   ∷ fill_ color
                   ∷ stroke_ "white"
                   ∷ strokeWidthF 1.5
                   ∷ [] ) []
           ∷ renderDots cx' cy' r' restAx restV color (suc idx) total

------------------------------------------------------------------------
-- Radar Chart
------------------------------------------------------------------------

-- | Full radar chart with multiple series
radarChart : ∀ {M A}
           → Float → Float              -- center x, y
           → RadarConfig
           → List RadarAxis
           → List RadarSeries
           → Node M A
radarChart {M} {A} cx cy config axes series =
  let radius = rcRadius config
      numAxes = listLen axes
  in g ( attr "class" "svg-radar-chart" ∷ [] )
       ( -- Background grid
         (if rcShowGrid config
          then g ( attr "class" "radar-grid" ∷ [] )
                 (renderGrid cx cy radius (rcGridLevels config) numAxes)
          else g [] [])
       -- Axis lines
       ∷ g ( attr "class" "radar-axes" ∷ [] )
           (renderAxisLines cx cy radius numAxes)
       -- All series
       ∷ g ( attr "class" "radar-series-group" ∷ [] )
           (renderAllSeries cx cy radius axes series (rcShowDots config) (rcFillOpacity config))
       -- Labels (on top)
       ∷ (if rcShowLabels config
          then g ( attr "class" "radar-labels" ∷ [] )
                 (renderAxisLabels cx cy radius axes)
          else g [] [])
       ∷ [] )
  where
    renderAllSeries : Float → Float → Float → List RadarAxis → List RadarSeries → Bool → Float → List (Node M A)
    renderAllSeries _ _ _ _ [] _ _ = []
    renderAllSeries cx' cy' r' axes' (s ∷ ss) dots op =
      renderSeriesPolygon cx' cy' r' axes' s dots op
      ∷ renderAllSeries cx' cy' r' axes' ss dots op

------------------------------------------------------------------------
-- Simple Radar Chart
------------------------------------------------------------------------

-- | Simple radar chart from axis names and single series
simpleRadarChart : ∀ {M A}
                 → Float → Float → Float  -- center and radius
                 → List String            -- axis names (all max = 100)
                 → List Float             -- values
                 → String                 -- color
                 → Node M A
simpleRadarChart cx cy radius axisNames values color =
  radarChart cx cy (defaultRadarConfig radius)
    (toAxes axisNames)
    (mkRadarSeries "data" color values ∷ [])
  where
    toAxes : List String → List RadarAxis
    toAxes [] = []
    toAxes (n ∷ ns) = mkRadarAxis n 100.0 ∷ toAxes ns

------------------------------------------------------------------------
-- Comparison Radar Chart
------------------------------------------------------------------------

-- | Radar chart comparing two or more entities
comparisonRadarChart : ∀ {M A}
                     → Float → Float → Float
                     → List RadarAxis
                     → List (String × String × List Float)  -- (name, color, values)
                     → Node M A
comparisonRadarChart cx cy radius axes seriesData =
  radarChart cx cy (defaultRadarConfig radius) axes (toSeries seriesData)
  where
    toSeries : List (String × String × List Float) → List RadarSeries
    toSeries [] = []
    toSeries ((n , c , vs) ∷ rest) =
      mkRadarSeries n c vs ∷ toSeries rest

------------------------------------------------------------------------
-- Radar with legend
------------------------------------------------------------------------

-- | Radar chart with integrated legend
radarChartWithLegend : ∀ {M A}
                     → Float → Float → Float  -- center and radius
                     → Float → Float          -- legend x, y
                     → List RadarAxis
                     → List RadarSeries
                     → Node M A
radarChartWithLegend {M} {A} cx cy radius legendX legendY axes series =
  g ( attr "class" "svg-radar-with-legend" ∷ [] )
    ( radarChart cx cy (defaultRadarConfig radius) axes series
    ∷ g ( attr "class" "radar-legend"
        ∷ attr "transform" ("translate(" ++ showFloat legendX ++ "," ++ showFloat legendY ++ ")") ∷ [] )
        (renderLegend series 0)
    ∷ [] )
  where
    renderLegend : List RadarSeries → ℕ → List (Node M A)
    renderLegend [] _ = []
    renderLegend (s ∷ ss) idx =
      let yOffset = fromℕ idx * 20.0
      in g []
           ( circle' ( cxF 8.0 ∷ cyF (yOffset + 8.0)
                     ∷ rF 6.0
                     ∷ fill_ (radarColor s)
                     ∷ [] ) []
           ∷ svgText ( xF 20.0 ∷ yF (yOffset + 12.0)
                     ∷ attr "font-size" "12"
                     ∷ fill_ "#374151"
                     ∷ [] )
               ( text (radarName s) ∷ [] )
           ∷ [] )
         ∷ renderLegend ss (suc idx)

------------------------------------------------------------------------
-- Performance radar (skills/attributes style)
------------------------------------------------------------------------

-- | Skills/performance radar with percentage values
skillsRadar : ∀ {M A}
            → Float → Float → Float
            → List (String × Float)        -- (skill name, percentage 0-100)
            → String                       -- color
            → Node M A
skillsRadar cx cy radius skills color =
  radarChart cx cy config axes (mkRadarSeries "skills" color values ∷ [])
  where
    config = mkRadarConfig radius true 4 true true 0.3

    axes : List RadarAxis
    axes = map (λ { (n , _) → mkRadarAxis n 100.0 }) skills
      where
        map : ∀ {A B : Set} → (A → B) → List A → List B
        map _ [] = []
        map f (x ∷ xs) = f x ∷ map f xs

    values : List Float
    values = map proj₂ skills
      where
        map : ∀ {A B : Set} → (A → B) → List A → List B
        map _ [] = []
        map f (x ∷ xs) = f x ∷ map f xs
