{-# OPTIONS --without-K #-}

-- SVG Bar Chart
-- Categorical data comparison

module Agdelte.Svg.Controls.Charts.Bar where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record BarData (A : Set) : Set where
  constructor mkBarData
  field
    barLabel   : String
    barValue   : Float
    barColor   : String
    barOnClick : Maybe A

open BarData public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findMaxValue : ∀ {A} → List (BarData A) → Float → Float
  findMaxValue [] acc = acc
  findMaxValue (b ∷ bs) acc =
    findMaxValue bs (if acc <ᵇ barValue b then barValue b else acc)

  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

------------------------------------------------------------------------
-- Bar Chart (Vertical)
------------------------------------------------------------------------

-- | Vertical bar chart
barChart : ∀ {M A}
         → Float → Float → Float → Float  -- x, y, width, height
         → Float                           -- bar gap
         → List (BarData A)
         → Node M A
barChart {M} {A} px py w h gap bars =
  let count = listLen bars
      maxVal = findMaxValue bars 0.0
      barW = if count ≡ᵇ 0 then 0.0 else (w - fromℕ count * gap) ÷ fromℕ count
  in g ( attr "class" "svg-bar-chart" ∷ [] )
       (renderBars px py barW h maxVal gap bars 0)
  where
    open import Data.Nat using (_≡ᵇ_)

    renderBars : Float → Float → Float → Float → Float → Float
               → List (BarData A) → ℕ → List (Node M A)
    renderBars _ _ _ _ _ _ [] _ = []
    renderBars bx by barW' h' maxV gp (b ∷ bs) idx =
      let barH = if maxV ≤ᵇ 0.0 then 0.0 else (barValue b ÷ maxV) * h'
          barX = bx + fromℕ idx * (barW' + gp)
          barY = by + h' - barH
      in (case barOnClick b of λ where
            nothing →
              rect' ( xF barX ∷ yF barY
                    ∷ widthF barW' ∷ heightF barH
                    ∷ fill_ (barColor b)
                    ∷ attr "class" "bar"
                    ∷ [] ) []
            (just msg) →
              rect' ( xF barX ∷ yF barY
                    ∷ widthF barW' ∷ heightF barH
                    ∷ fill_ (barColor b)
                    ∷ attr "class" "bar bar--clickable"
                    ∷ attr "style" "cursor: pointer"
                    ∷ on "click" msg
                    ∷ [] ) [])
         ∷ renderBars bx by barW' h' maxV gp bs (suc idx)
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

------------------------------------------------------------------------
-- Simple bar chart
------------------------------------------------------------------------

-- | Simple bar chart with default styling
simpleBarChart : ∀ {M A}
               → Float → Float → Float → Float
               → List (String × Float)        -- (label, value) pairs
               → Node M A
simpleBarChart {M} {A} px py w h pairs =
  barChart px py w h 4.0 (toBars pairs)
  where
    colors : List String
    colors = "#3b82f6" ∷ "#22c55e" ∷ "#f59e0b" ∷ "#ef4444" ∷ "#8b5cf6" ∷ []

    getColor : ℕ → String
    getColor n = go colors n
      where
        go : List String → ℕ → String
        go [] _ = "#3b82f6"
        go (c ∷ _) zero = c
        go (_ ∷ cs) (suc m) = go cs m

    toBars : List (String × Float) → List (BarData A)
    toBars xs = go xs 0
      where
        go : List (String × Float) → ℕ → List (BarData A)
        go [] _ = []
        go ((lbl , val) ∷ rest) idx =
          mkBarData lbl val (getColor idx) nothing
          ∷ go rest (suc idx)

------------------------------------------------------------------------
-- Horizontal bar chart
------------------------------------------------------------------------

-- | Horizontal bar chart
horizontalBarChart : ∀ {M A}
                   → Float → Float → Float → Float
                   → Float
                   → List (BarData A)
                   → Node M A
horizontalBarChart {M} {A} px py w h gap bars =
  let count = listLen bars
      maxVal = findMaxValue bars 0.0
      barH = if count ≡ᵇ 0 then 0.0 else (h - fromℕ count * gap) ÷ fromℕ count
  in g ( attr "class" "svg-bar-chart-h" ∷ [] )
       (renderBarsH px py w barH maxVal gap bars 0)
  where
    open import Data.Nat using (_≡ᵇ_)

    renderBarsH : Float → Float → Float → Float → Float → Float
                → List (BarData A) → ℕ → List (Node M A)
    renderBarsH _ _ _ _ _ _ [] _ = []
    renderBarsH bx by w' barH' maxV gp (b ∷ bs) idx =
      let barW = if maxV ≤ᵇ 0.0 then 0.0 else (barValue b ÷ maxV) * w'
          barY = by + fromℕ idx * (barH' + gp)
      in rect' ( xF bx ∷ yF barY
               ∷ widthF barW ∷ heightF barH'
               ∷ fill_ (barColor b)
               ∷ attr "class" "bar"
               ∷ [] ) []
         ∷ renderBarsH bx by w' barH' maxV gp bs (suc idx)

------------------------------------------------------------------------
-- Stacked bar chart
------------------------------------------------------------------------

-- | Stacked bar chart
stackedBarChart : ∀ {M A}
                → Float → Float → Float → Float
                → List String                    -- series names
                → List String                    -- series colors
                → List (List Float)              -- data[category][series]
                → Node M A
stackedBarChart {M} {A} px py w h names colors dataRows =
  let count = listLen dataRows
      barW = if count ≡ᵇ 0 then 0.0 else w ÷ fromℕ count
      maxStack = findMaxStack dataRows
  in g ( attr "class" "svg-stacked-bar-chart" ∷ [] )
       (renderStacks px py barW h maxStack colors dataRows 0)
  where
    open import Data.Nat using (_≡ᵇ_)

    sumList : List Float → Float
    sumList [] = 0.0
    sumList (v ∷ vs) = v + sumList vs

    findMaxStack : List (List Float) → Float
    findMaxStack [] = 0.0
    findMaxStack (row ∷ rows) =
      let s = sumList row
          m = findMaxStack rows
      in if m <ᵇ s then s else m

    renderStack : Float → Float → Float → Float → Float
                → List String → List Float → Float → List (Node M A)
    renderStack _ _ _ _ _ _ [] _ = []
    renderStack _ _ _ _ _ [] _ _ = []
    renderStack bx by barW' h' maxV (c ∷ cs) (v ∷ vs) offset =
      let segH = if maxV ≤ᵇ 0.0 then 0.0 else (v ÷ maxV) * h'
          segY = by + h' - offset - segH
      in rect' ( xF bx ∷ yF segY
               ∷ widthF (barW' * 0.8) ∷ heightF segH
               ∷ fill_ c
               ∷ [] ) []
         ∷ renderStack bx by barW' h' maxV cs vs (offset + segH)

    renderStacks : Float → Float → Float → Float → Float
                 → List String → List (List Float) → ℕ → List (Node M A)
    renderStacks _ _ _ _ _ _ [] _ = []
    renderStacks bx by barW' h' maxV cols (row ∷ rows) idx =
      let barX = bx + fromℕ idx * barW'
      in g [] (renderStack barX by barW' h' maxV cols row 0.0)
         ∷ renderStacks bx by barW' h' maxV cols rows (suc idx)
