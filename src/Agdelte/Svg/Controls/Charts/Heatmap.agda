{-# OPTIONS --without-K #-}

-- SVG Heatmap
-- 2D density/intensity visualization

module Agdelte.Svg.Controls.Charts.Heatmap where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Color interpolation
------------------------------------------------------------------------

private
  -- Simple blue-red color scale
  -- Takes min value, max value, and current value
  valueToColor : Float → Float → Float → String
  valueToColor minV maxV v =
    let norm = if (maxV - minV) ≤ᵇ 0.0
               then 0.5
               else (v - minV) ÷ (maxV - minV)
        -- Blue (cold) to Red (hot) - simple linear interpolation
        -- We use a simplified approach without actual floor
        intensity = norm * 255.0
    in if norm <ᵇ 0.25
       then "#3b82f6"  -- blue
       else if norm <ᵇ 0.5
            then "#22c55e"  -- green
            else if norm <ᵇ 0.75
                 then "#f59e0b"  -- orange
                 else "#ef4444"  -- red

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  findMinMaxList : List Float → Float → Float → Float × Float
  findMinMaxList [] minA maxA = (minA , maxA)
  findMinMaxList (v ∷ vs) minA maxA =
    findMinMaxList vs
      (if v <ᵇ minA then v else minA)
      (if maxA <ᵇ v then v else maxA)

  findMinMaxGrid : List (List Float) → Float → Float → Float × Float
  findMinMaxGrid [] minA maxA = (minA , maxA)
  findMinMaxGrid (row ∷ rows) minA maxA =
    let (minR , maxR) = findMinMaxList row minA maxA
    in findMinMaxGrid rows minR maxR

------------------------------------------------------------------------
-- Heatmap
------------------------------------------------------------------------

-- | Heatmap visualization
heatmap : ∀ {M A}
        → Float → Float → Float → Float  -- x, y, width, height
        → (Float → Float → Float → String)  -- value to color function (min, max, value)
        → List (List Float)              -- data[row][col]
        → Maybe (ℕ → ℕ → A)              -- onClick (row, col)
        → Node M A
heatmap {M} {A} px py w h colorFn grid onClick' =
  let numRows = listLen grid
      (minV , maxV) = findMinMaxGrid grid 1.0e10 (0.0 - 1.0e10)
  in g ( attr "class" "svg-heatmap" ∷ [] )
       (renderRows px py w h minV maxV colorFn grid 0 numRows onClick')
  where
    renderCells : Float → Float → Float → Float
                → Float → Float
                → (Float → Float → Float → String)
                → List Float → ℕ → ℕ → ℕ
                → Maybe (ℕ → ℕ → A)
                → List (Node M A)
    renderCells _ _ _ _ _ _ _ [] _ _ _ _ = []
    renderCells cx cy cellW cellH minV maxV colFn (v ∷ vs) colIdx rowIdx numCols onClick'' =
      let color = colFn minV maxV v
      in (case onClick'' of λ where
            nothing →
              rect' ( xF cx ∷ yF cy
                    ∷ widthF cellW ∷ heightF cellH
                    ∷ fill_ color
                    ∷ attr "class" "heatmap-cell"
                    ∷ [] ) []
            (just handler) →
              rect' ( xF cx ∷ yF cy
                    ∷ widthF cellW ∷ heightF cellH
                    ∷ fill_ color
                    ∷ attr "class" "heatmap-cell heatmap-cell--clickable"
                    ∷ attr "style" "cursor: pointer"
                    ∷ on "click" (handler rowIdx colIdx)
                    ∷ [] ) [])
         ∷ renderCells (cx + cellW) cy cellW cellH minV maxV colFn vs (suc colIdx) rowIdx numCols onClick''
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

    renderRows : Float → Float → Float → Float
               → Float → Float
               → (Float → Float → Float → String)
               → List (List Float) → ℕ → ℕ
               → Maybe (ℕ → ℕ → A)
               → List (Node M A)
    renderRows _ _ _ _ _ _ _ [] _ _ _ = []
    renderRows rx ry w' h' minV maxV colFn (row ∷ rows) rowIdx numRows onClick'' =
      let numCols = listLen row
          cellW = if numCols ≡ᵇ 0 then 0.0 else w' ÷ fromℕ numCols
          cellH = if numRows ≡ᵇ 0 then 0.0 else h' ÷ fromℕ numRows
          rowY = ry + fromℕ rowIdx * cellH
      in g [] (renderCells rx rowY cellW cellH minV maxV colFn row 0 rowIdx numCols onClick'')
         ∷ renderRows rx ry w' h' minV maxV colFn rows (suc rowIdx) numRows onClick''
      where
        open import Data.Nat using (_≡ᵇ_)

------------------------------------------------------------------------
-- Simple heatmap
------------------------------------------------------------------------

-- | Simple heatmap with blue-red color scale
simpleHeatmap : ∀ {M A}
              → Float → Float → Float → Float
              → List (List Float)
              → Node M A
simpleHeatmap {M} {A} px py w h grid =
  heatmap px py w h valueToColor grid nothing

------------------------------------------------------------------------
-- Heatmap with labels
------------------------------------------------------------------------

-- | Heatmap with row and column labels
labeledHeatmap : ∀ {M A}
               → Float → Float → Float → Float
               → List String              -- column labels
               → List String              -- row labels
               → List (List Float)
               → Node M A
labeledHeatmap {M} {A} px py w h colLabels rowLabels grid =
  let labelSpace = 40.0
      chartX = px + labelSpace
      chartY = py + labelSpace
      chartW = w - labelSpace
      chartH = h - labelSpace
  in g ( attr "class" "svg-labeled-heatmap" ∷ [] )
       ( -- Column labels
         renderColLabels chartX py (chartW ÷ fromℕ (listLen colLabels)) colLabels 0
       -- Row labels
       ∷ renderRowLabels px chartY (chartH ÷ fromℕ (listLen rowLabels)) rowLabels 0
       -- Heatmap
       ∷ heatmap chartX chartY chartW chartH valueToColor grid nothing
       ∷ [] )
  where
    renderColLabels : Float → Float → Float → List String → ℕ → Node M A
    renderColLabels _ _ _ [] _ = g [] []
    renderColLabels lx ly cellW (lbl ∷ lbls) idx =
      g []
        ( svgText ( xF (lx + fromℕ idx * cellW + cellW ÷ 2.0)
                  ∷ yF (ly + 15.0)
                  ∷ attr "text-anchor" "middle"
                  ∷ attr "font-size" "10"
                  ∷ [] )
            ( text lbl ∷ [] )
        ∷ renderColLabels lx ly cellW lbls (suc idx)
        ∷ [] )

    renderRowLabels : Float → Float → Float → List String → ℕ → Node M A
    renderRowLabels _ _ _ [] _ = g [] []
    renderRowLabels lx ly cellH (lbl ∷ lbls) idx =
      g []
        ( svgText ( xF (lx + 35.0)
                  ∷ yF (ly + fromℕ idx * cellH + cellH ÷ 2.0)
                  ∷ attr "text-anchor" "end"
                  ∷ attr "dominant-baseline" "middle"
                  ∷ attr "font-size" "10"
                  ∷ [] )
            ( text lbl ∷ [] )
        ∷ renderRowLabels lx ly cellH lbls (suc idx)
        ∷ [] )
