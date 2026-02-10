{-# OPTIONS --without-K #-}

-- SVG Treemap
-- Hierarchical data as nested rectangles

module Agdelte.Svg.Controls.Charts.Treemap where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; map; foldr)
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

-- Treemap node (hierarchical)
record TreemapNode (A : Set) : Set where
  inductive
  constructor mkTreemapNode
  field
    tmLabel    : String
    tmValue    : Float               -- size/weight
    tmColor    : Maybe String        -- if Nothing, auto-color
    tmChildren : List (TreemapNode A)
    tmOnClick  : Maybe A

open TreemapNode public

-- Flattened rectangle for rendering
record TreemapRect (A : Set) : Set where
  constructor mkTreemapRect
  field
    trX       : Float
    trY       : Float
    trWidth   : Float
    trHeight  : Float
    trLabel   : String
    trValue   : Float
    trColor   : String
    trDepth   : ℕ
    trOnClick : Maybe A

open TreemapRect public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  sumValues : ∀ {A} → List (TreemapNode A) → Float
  sumValues [] = 0.0
  sumValues (n ∷ ns) = tmValue n + sumValues ns

  -- Default color palette
  colors : List String
  colors = "#3b82f6" ∷ "#22c55e" ∷ "#f59e0b" ∷ "#ef4444" ∷ "#8b5cf6"
         ∷ "#ec4899" ∷ "#14b8a6" ∷ "#f97316" ∷ "#84cc16" ∷ "#06b6d4"
         ∷ []

  getColor : ℕ → String
  getColor n = go colors n
    where
      go : List String → ℕ → String
      go [] _ = "#3b82f6"
      go (c ∷ _) zero = c
      go (_ ∷ cs) (suc m) = go cs m

  -- Lighten color for nested items (simplified - just add alpha)
  lightenColor : String → ℕ → String
  lightenColor c depth = c  -- In real impl, would adjust brightness

------------------------------------------------------------------------
-- Squarified Treemap Layout
------------------------------------------------------------------------

-- Simplified squarified layout algorithm
-- Real implementation would use proper squarify algorithm
private
  layoutChildren : ∀ {A}
                 → Float → Float → Float → Float  -- available area
                 → Float                           -- total value
                 → ℕ                               -- color index
                 → ℕ                               -- depth
                 → List (TreemapNode A)
                 → List (TreemapRect A)
  layoutChildren _ _ _ _ _ _ _ [] = []
  layoutChildren {A} px py w h total colorIdx depth nodes =
    if w <ᵇ h
    then layoutVertical px py w h total colorIdx depth nodes
    else layoutHorizontal px py w h total colorIdx depth nodes
    where
      layoutHorizontal : Float → Float → Float → Float → Float → ℕ → ℕ → List (TreemapNode A) → List (TreemapRect A)
      layoutHorizontal _ _ _ _ _ _ _ [] = []
      layoutHorizontal px' py' w' h' tot' cidx dep (n ∷ ns) =
        let ratio = if tot' ≤ᵇ 0.0 then 0.0 else tmValue n ÷ tot'
            nodeW = ratio * w'
            nodeColor = case tmColor n of λ where
              nothing → getColor cidx
              (just c) → c
            rect = mkTreemapRect px' py' nodeW h' (tmLabel n) (tmValue n) nodeColor dep (tmOnClick n)
            -- Recurse into children if any
            childRects = if listLen (tmChildren n) ≡ᵇ 0
                         then []
                         else layoutChildren (px' + 2.0) (py' + 2.0) (nodeW - 4.0) (h' - 4.0)
                                (sumValues (tmChildren n)) 0 (suc dep) (tmChildren n)
        in rect ∷ childRects ++ᴸ layoutHorizontal (px' + nodeW) py' (w' - nodeW) h' (tot' - tmValue n) (suc cidx) dep ns
        where
          open import Data.Nat using (_≡ᵇ_)
          open import Data.List renaming (_++_ to _++ᴸ_)
          case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
          case x of f = f x

      layoutVertical : Float → Float → Float → Float → Float → ℕ → ℕ → List (TreemapNode A) → List (TreemapRect A)
      layoutVertical _ _ _ _ _ _ _ [] = []
      layoutVertical px' py' w' h' tot' cidx dep (n ∷ ns) =
        let ratio = if tot' ≤ᵇ 0.0 then 0.0 else tmValue n ÷ tot'
            nodeH = ratio * h'
            nodeColor = case tmColor n of λ where
              nothing → getColor cidx
              (just c) → c
            rect = mkTreemapRect px' py' w' nodeH (tmLabel n) (tmValue n) nodeColor dep (tmOnClick n)
            childRects = if listLen (tmChildren n) ≡ᵇ 0
                         then []
                         else layoutChildren (px' + 2.0) (py' + 2.0) (w' - 4.0) (nodeH - 4.0)
                                (sumValues (tmChildren n)) 0 (suc dep) (tmChildren n)
        in rect ∷ childRects ++ᴸ layoutVertical px' (py' + nodeH) w' (h' - nodeH) (tot' - tmValue n) (suc cidx) dep ns
        where
          open import Data.Nat using (_≡ᵇ_)
          open import Data.List renaming (_++_ to _++ᴸ_)
          case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
          case x of f = f x

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

private
  renderRect : ∀ {M A} → TreemapRect A → Bool → Node M A
  renderRect r showLabels =
    let minDim = if trWidth r <ᵇ trHeight r then trWidth r else trHeight r
        showLabel = showLabels ∧ᵇ (20.0 <ᵇ minDim)
    in case trOnClick r of λ where
         nothing →
           g ( attr "class" "treemap-node" ∷ [] )
             ( rect' ( xF (trX r) ∷ yF (trY r)
                     ∷ widthF (trWidth r) ∷ heightF (trHeight r)
                     ∷ fill_ (trColor r)
                     ∷ stroke_ "white"
                     ∷ strokeWidthF 1.0
                     ∷ [] ) []
             ∷ (if showLabel
                then svgText ( xF (trX r + 4.0) ∷ yF (trY r + 14.0)
                             ∷ attr "font-size" "11"
                             ∷ fill_ "white"
                             ∷ attr "class" "treemap-label"
                             ∷ [] )
                       ( text (trLabel r) ∷ [] )
                else g [] [])
             ∷ [] )
         (just msg) →
           g ( attr "class" "treemap-node treemap-node--clickable"
             ∷ attr "style" "cursor: pointer"
             ∷ on "click" msg
             ∷ [] )
             ( rect' ( xF (trX r) ∷ yF (trY r)
                     ∷ widthF (trWidth r) ∷ heightF (trHeight r)
                     ∷ fill_ (trColor r)
                     ∷ stroke_ "white"
                     ∷ strokeWidthF 1.0
                     ∷ [] ) []
             ∷ (if showLabel
                then svgText ( xF (trX r + 4.0) ∷ yF (trY r + 14.0)
                             ∷ attr "font-size" "11"
                             ∷ fill_ "white"
                             ∷ [] )
                       ( text (trLabel r) ∷ [] )
                else g [] [])
             ∷ [] )
    where
      open import Data.Bool renaming (_∧_ to _∧ᵇ_)
      case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
      case x of f = f x

  renderRects : ∀ {M A} → List (TreemapRect A) → Bool → List (Node M A)
  renderRects [] _ = []
  renderRects (r ∷ rs) showLabels = renderRect r showLabels ∷ renderRects rs showLabels

------------------------------------------------------------------------
-- Treemap
------------------------------------------------------------------------

-- | Full treemap visualization
treemap : ∀ {M A}
        → Float → Float → Float → Float  -- x, y, width, height
        → Bool                            -- show labels
        → List (TreemapNode A)
        → Node M A
treemap {M} {A} px py w h showLabels nodes =
  let total = sumValues nodes
      rects = layoutChildren px py w h total 0 0 nodes
  in g ( attr "class" "svg-treemap" ∷ [] )
       (renderRects rects showLabels)

------------------------------------------------------------------------
-- Simple Treemap (flat data)
------------------------------------------------------------------------

-- | Simple treemap from label/value pairs
simpleTreemap : ∀ {M A}
              → Float → Float → Float → Float
              → List (String × Float)
              → Node M A
simpleTreemap {M} {A} px py w h pairs =
  treemap px py w h true (toNodes pairs)
  where
    toNodes : List (String × Float) → List (TreemapNode A)
    toNodes [] = []
    toNodes ((lbl , val) ∷ rest) =
      mkTreemapNode lbl val nothing [] nothing
      ∷ toNodes rest

------------------------------------------------------------------------
-- Treemap with custom colors
------------------------------------------------------------------------

-- | Treemap with explicit colors
coloredTreemap : ∀ {M A}
               → Float → Float → Float → Float
               → List (String × Float × String)  -- (label, value, color)
               → Node M A
coloredTreemap {M} {A} px py w h items =
  treemap px py w h true (toNodes items)
  where
    toNodes : List (String × Float × String) → List (TreemapNode A)
    toNodes [] = []
    toNodes ((lbl , val , col) ∷ rest) =
      mkTreemapNode lbl val (just col) [] nothing
      ∷ toNodes rest

------------------------------------------------------------------------
-- Clickable Treemap
------------------------------------------------------------------------

-- | Treemap with click handlers
clickableTreemap : ∀ {M A}
                 → Float → Float → Float → Float
                 → (String → A)              -- onClick handler
                 → List (String × Float)
                 → Node M A
clickableTreemap {M} {A} px py w h onClick pairs =
  treemap px py w h true (toNodes pairs)
  where
    toNodes : List (String × Float) → List (TreemapNode A)
    toNodes [] = []
    toNodes ((lbl , val) ∷ rest) =
      mkTreemapNode lbl val nothing [] (just (onClick lbl))
      ∷ toNodes rest

------------------------------------------------------------------------
-- Hierarchical Treemap
------------------------------------------------------------------------

-- | Nested treemap for hierarchical data
hierarchicalTreemap : ∀ {M A}
                    → Float → Float → Float → Float
                    → TreemapNode A            -- root node
                    → Node M A
hierarchicalTreemap {M} {A} px py w h root =
  treemap px py w h true (tmChildren root)

------------------------------------------------------------------------
-- Disk Usage Style Treemap
------------------------------------------------------------------------

-- | Treemap styled like disk usage visualization
diskUsageTreemap : ∀ {M A}
                 → Float → Float → Float → Float
                 → List (String × Float)     -- (path, size in bytes)
                 → Node M A
diskUsageTreemap {M} {A} px py w h items =
  let total = sumItems items
  in g ( attr "class" "svg-disk-treemap" ∷ [] )
       ( treemap px py w h true (toNodes items)
       ∷ [] )
  where
    sumItems : List (String × Float) → Float
    sumItems [] = 0.0
    sumItems ((_ , v) ∷ rest) = v + sumItems rest

    toNodes : List (String × Float) → List (TreemapNode A)
    toNodes [] = []
    toNodes ((path , size) ∷ rest) =
      mkTreemapNode path size nothing [] nothing
      ∷ toNodes rest
