{-# OPTIONS --without-K #-}

-- SVG Sparkline
-- Tiny inline charts for trends

module Agdelte.Svg.Controls.Gauges.Sparkline where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; rect'; line')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  findMin : List Float → Float → Float
  findMin [] acc = acc
  findMin (v ∷ vs) acc = findMin vs (if v <ᵇ acc then v else acc)

  findMax : List Float → Float → Float
  findMax [] acc = acc
  findMax (v ∷ vs) acc = findMax vs (if acc <ᵇ v then v else acc)

  getLast : List Float → Float
  getLast [] = 0.0
  getLast (v ∷ []) = v
  getLast (_ ∷ vs) = getLast vs

------------------------------------------------------------------------
-- Line Sparkline
------------------------------------------------------------------------

-- | Simple line sparkline
sparkline : ∀ {M A}
          → Float → Float → Float → Float  -- x, y, width, height
          → String                          -- stroke color
          → List Float                      -- values
          → Node M A
sparkline px py w h color values =
  let minV = findMin values 1.0e10
      maxV = findMax values (0.0 - 1.0e10)
      n = listLen values
      pathD = buildPath px py w h minV maxV values 0 n
  in g ( attr "class" "svg-sparkline" ∷ [] )
       ( path' ( d_ pathD
               ∷ fill_ "none"
               ∷ stroke_ color
               ∷ strokeWidthF 1.5
               ∷ attr "stroke-linecap" "round"
               ∷ attr "stroke-linejoin" "round"
               ∷ [] ) []
       ∷ [] )
  where
    buildPath : Float → Float → Float → Float
              → Float → Float
              → List Float → ℕ → ℕ → String
    buildPath _ _ _ _ _ _ [] _ _ = ""
    buildPath px' py' w' h' minV maxV (v ∷ vs) idx total =
      let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
          xPos = if total ≤ᵇᴺ 1 then px' else px' + (fromℕ idx ÷ fromℕ (total ∸ 1)) * w'
          yPos = py' + h' - ((v - minV) ÷ range) * h'
          prefix = if idx ≡ᵇ 0 then "M " else " L "
      in prefix ++ showFloat xPos ++ " " ++ showFloat yPos
         ++ buildPath px' py' w' h' minV maxV vs (suc idx) total
      where
        open import Data.Nat using (_≡ᵇ_; _∸_) renaming (_≤ᵇ_ to _≤ᵇᴺ_)

------------------------------------------------------------------------
-- Area Sparkline (filled)
------------------------------------------------------------------------

-- | Sparkline with filled area
sparklineArea : ∀ {M A}
              → Float → Float → Float → Float
              → String                        -- fill color
              → Float                         -- opacity
              → List Float
              → Node M A
sparklineArea px py w h color opacity [] = g [] []
sparklineArea px py w h color opacity values =
  let minV = findMin values 1.0e10
      maxV = findMax values (0.0 - 1.0e10)
      n = listLen values
      linePath = buildLine px py w h minV maxV values 0 n
      areaPath = linePath
                 ++ " L " ++ showFloat (px + w) ++ " " ++ showFloat (py + h)
                 ++ " L " ++ showFloat px ++ " " ++ showFloat (py + h)
                 ++ " Z"
  in g ( attr "class" "svg-sparkline-area" ∷ [] )
       ( -- Fill
         path' ( d_ areaPath
               ∷ fill_ color
               ∷ attr "opacity" (showFloat opacity)
               ∷ [] ) []
       -- Line
       ∷ path' ( d_ linePath
               ∷ fill_ "none"
               ∷ stroke_ color
               ∷ strokeWidthF 1.5
               ∷ [] ) []
       ∷ [] )
  where
    buildLine : Float → Float → Float → Float
              → Float → Float
              → List Float → ℕ → ℕ → String
    buildLine _ _ _ _ _ _ [] _ _ = ""
    buildLine px' py' w' h' minV maxV (v ∷ vs) idx total =
      let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
          xPos = if total ≤ᵇᴺ 1 then px' else px' + (fromℕ idx ÷ fromℕ (total ∸ 1)) * w'
          yPos = py' + h' - ((v - minV) ÷ range) * h'
          prefix = if idx ≡ᵇ 0 then "M " else " L "
      in prefix ++ showFloat xPos ++ " " ++ showFloat yPos
         ++ buildLine px' py' w' h' minV maxV vs (suc idx) total
      where
        open import Data.Nat using (_≡ᵇ_; _∸_) renaming (_≤ᵇ_ to _≤ᵇᴺ_)

------------------------------------------------------------------------
-- Bar Sparkline
------------------------------------------------------------------------

-- | Bar chart sparkline
sparklineBar : ∀ {M A}
             → Float → Float → Float → Float
             → String                        -- color
             → Float                         -- bar gap
             → List Float
             → Node M A
sparklineBar {M} {A} px py w h color gap values =
  let minV = 0.0  -- bars start from 0
      maxV = findMax values 1.0
      n = listLen values
      barW = if n ≡ᵇ 0 then 0.0 else (w - fromℕ n * gap) ÷ fromℕ n
  in g ( attr "class" "svg-sparkline-bar" ∷ [] )
       (renderBars px py w h minV maxV barW gap values 0)
  where
    open import Data.Nat using (_≡ᵇ_)

    renderBars : Float → Float → Float → Float
               → Float → Float → Float → Float
               → List Float → ℕ → List (Node M A)
    renderBars _ _ _ _ _ _ _ _ [] _ = []
    renderBars bx by bw bh minV maxV barW gp (v ∷ vs) idx =
      let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
          barH = ((v - minV) ÷ range) * bh
          barX = bx + fromℕ idx * (barW + gp)
          barY = by + bh - barH
      in rect' ( xF barX ∷ yF barY
               ∷ widthF barW ∷ heightF barH
               ∷ fill_ color
               ∷ attr "rx" "1"
               ∷ [] ) []
         ∷ renderBars bx by bw bh minV maxV barW gp vs (suc idx)

------------------------------------------------------------------------
-- Sparkline with endpoint dots
------------------------------------------------------------------------

-- | Sparkline with first/last point markers
sparklineWithDots : ∀ {M A}
                  → Float → Float → Float → Float
                  → String                    -- line color
                  → String                    -- start dot color
                  → String                    -- end dot color
                  → List Float
                  → Node M A
sparklineWithDots px py w h lineColor startColor endColor [] = g [] []
sparklineWithDots px py w h lineColor startColor endColor values =
  let minV = findMin values 1.0e10
      maxV = findMax values (0.0 - 1.0e10)
      n = listLen values
      firstY = getFirstY py h minV maxV values
      lastY = getLastY py h minV maxV values n
  in g ( attr "class" "svg-sparkline-dots" ∷ [] )
       ( sparkline px py w h lineColor values
       -- Start dot
       ∷ circle' ( cxF px ∷ cyF firstY
                 ∷ rF 2.5
                 ∷ fill_ startColor
                 ∷ [] ) []
       -- End dot
       ∷ circle' ( cxF (px + w) ∷ cyF lastY
                 ∷ rF 2.5
                 ∷ fill_ endColor
                 ∷ [] ) []
       ∷ [] )
  where
    getFirstY : Float → Float → Float → Float → List Float → Float
    getFirstY py' h' minV maxV [] = py' + h' ÷ 2.0
    getFirstY py' h' minV maxV (v ∷ _) =
      let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
      in py' + h' - ((v - minV) ÷ range) * h'

    getLastY : Float → Float → Float → Float → List Float → ℕ → Float
    getLastY py' h' minV maxV values' n' =
      let v = getLast values'
          range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
      in py' + h' - ((v - minV) ÷ range) * h'

------------------------------------------------------------------------
-- Win/Loss Sparkline
------------------------------------------------------------------------

-- | Win/loss chart (positive/negative only)
sparklineWinLoss : ∀ {M A}
                 → Float → Float → Float → Float
                 → String                    -- win color
                 → String                    -- loss color
                 → List Float                -- positive = win, negative = loss
                 → Node M A
sparklineWinLoss {M} {A} px py w h winColor lossColor values =
  let n = listLen values
      barW = if n ≡ᵇ 0 then 0.0 else w ÷ fromℕ n * 0.8
      gap = w ÷ fromℕ n * 0.2
      halfH = h ÷ 2.0
  in g ( attr "class" "svg-sparkline-winloss" ∷ [] )
       ( -- Center line
         line' ( x1F px ∷ y1F (py + halfH)
               ∷ x2F (px + w) ∷ y2F (py + halfH)
               ∷ stroke_ "#e5e7eb"
               ∷ strokeWidthF 1.0
               ∷ [] ) []
       ∷ g [] (renderBars px py w h barW gap halfH values 0)
       ∷ [] )
  where
    open import Data.Nat using (_≡ᵇ_)

    renderBars : Float → Float → Float → Float
               → Float → Float → Float
               → List Float → ℕ → List (Node M A)
    renderBars _ _ _ _ _ _ _ [] _ = []
    renderBars bx by _ bh barW gp halfH (v ∷ vs) idx =
      let isWin = 0.0 <ᵇ v
          barColor = if isWin then winColor else lossColor
          barH = halfH * 0.8
          barX = bx + fromℕ idx * (barW + gp)
          barY = if isWin then by + halfH - barH else by + halfH
      in rect' ( xF barX ∷ yF barY
               ∷ widthF barW ∷ heightF barH
               ∷ fill_ barColor
               ∷ attr "rx" "1"
               ∷ [] ) []
         ∷ renderBars bx by 0.0 bh barW gp halfH vs (suc idx)

------------------------------------------------------------------------
-- Sparkline with reference line
------------------------------------------------------------------------

-- | Sparkline with horizontal reference line
sparklineWithRef : ∀ {M A}
                 → Float → Float → Float → Float
                 → String                    -- line color
                 → Float                     -- reference value
                 → String                    -- reference line color
                 → List Float
                 → Node M A
sparklineWithRef px py w h color refValue refColor values =
  let minV = findMin values 1.0e10
      maxV = findMax values (0.0 - 1.0e10)
      range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
      refY = py + h - ((refValue - minV) ÷ range) * h
  in g ( attr "class" "svg-sparkline-ref" ∷ [] )
       ( -- Reference line
         line' ( x1F px ∷ y1F refY
               ∷ x2F (px + w) ∷ y2F refY
               ∷ stroke_ refColor
               ∷ strokeWidthF 1.0
               ∷ attr "stroke-dasharray" "3,3"
               ∷ [] ) []
       -- Sparkline
       ∷ sparkline px py w h color values
       ∷ [] )

------------------------------------------------------------------------
-- Quick constructors
------------------------------------------------------------------------

-- | Blue sparkline
blueSparkline : ∀ {M A}
              → Float → Float → Float → Float
              → List Float
              → Node M A
blueSparkline px py w h = sparkline px py w h "#3b82f6"

-- | Green trend sparkline
greenTrendSparkline : ∀ {M A}
                    → Float → Float → Float → Float
                    → List Float
                    → Node M A
greenTrendSparkline px py w h = sparklineWithDots px py w h "#22c55e" "#94a3b8" "#22c55e"

-- | Red/green performance sparkline
performanceSparkline : ∀ {M A}
                     → Float → Float → Float → Float
                     → List Float
                     → Node M A
performanceSparkline px py w h values =
  let lastV = getLast values
      firstV = getFirst values
      color = if lastV <ᵇ firstV then "#ef4444" else "#22c55e"
  in sparklineArea px py w h color 0.3 values
  where
    getFirst : List Float → Float
    getFirst [] = 0.0
    getFirst (v ∷ _) = v
