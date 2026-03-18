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

-- JS-compiled helpers for squarified algorithm
private
  postulate absFloat : Float → Float
  {-# COMPILE JS absFloat = Math.abs #-}

  postulate maxFloat : Float → Float → Float
  {-# COMPILE JS maxFloat = x => y => Math.max(x, y) #-}

  postulate sortDescFloat : ∀ {A : Set} → (A → Float) → List A → List A
  {-# COMPILE JS sortDescFloat = f => xs => [...xs].sort((a, b) => f(b) - f(a)) #-}

private
  open import Data.List renaming (_++_ to _++ᴸ_)
  open import Data.Nat using (_≡ᵇ_) renaming (_+_ to _+ᴺ_)

  case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
  case x of f = f x

  -- Filter out nodes with non-positive values
  positiveNodes : ∀ {A} → List (TreemapNode A) → List (TreemapNode A)
  positiveNodes [] = []
  positiveNodes (n ∷ ns) =
    if 0.0 <ᵇ tmValue n then n ∷ positiveNodes ns else positiveNodes ns

  -- Maximum fuel for squarify iterations (safety net against infinite loops)
  maxFuel : ℕ
  maxFuel = 1000

  -- Sum float values in a list
  sumFloats : List Float → Float
  sumFloats [] = 0.0
  sumFloats (v ∷ vs) = v + sumFloats vs

  -- Compute worst aspect ratio for a row of areas laid out along a side of length `side`
  -- Each item's area is given; the row's total area determines the row thickness.
  worstRatio : List Float → Float → Float
  worstRatio [] _ = 0.0
  worstRatio areas side =
    let s = sumFloats areas
        -- row thickness = totalArea / side
        -- for each item: itemWidth = itemArea / thickness = itemArea * side / totalArea
        -- aspect ratio = max(w/thickness, thickness/w)
    in go areas s side
    where
      ratioOf : Float → Float → Float → Float
      ratioOf area total sideLen =
        if total ≤ᵇ 0.0 then 1.0e10
        else let thickness = total ÷ sideLen
                 w = area ÷ thickness
                 r1 = w ÷ thickness
                 r2 = thickness ÷ w
             in maxFloat r1 r2

      go : List Float → Float → Float → Float
      go [] _ _ = 0.0
      go (a ∷ []) total sideLen = ratioOf a total sideLen
      go (a ∷ rest) total sideLen = maxFloat (ratioOf a total sideLen) (go rest total sideLen)

  -- Squarified layout: recursively partition nodes into rows with good aspect ratios.
  -- Uses a fuel parameter as a safety net against infinite loops (e.g. from
  -- zero-valued nodes that don't shrink the remaining rectangle).
  -- Nodes with value ≤ 0 are filtered out before processing.
  {-# TERMINATING #-}
  layoutChildren : ∀ {A}
                 → Float → Float → Float → Float  -- available area
                 → Float                           -- total value
                 → ℕ                               -- color index
                 → ℕ                               -- depth
                 → List (TreemapNode A)
                 → List (TreemapRect A)
  layoutChildren _ _ _ _ _ _ _ [] = []
  layoutChildren {A} px py w h total colorIdx depth nodes =
    let filtered = positiveNodes nodes
        filteredTotal = sumValues filtered
        sorted = sortDescFloat (λ n → tmValue n) filtered
    in squarify maxFuel sorted [] px py w h filteredTotal colorIdx depth
    where
      -- Lay out a finalized row of nodes along the short side of the remaining rectangle
      -- When w < h (tall), the row goes horizontally (fixed height strip at top)
      -- When w >= h (wide), the row goes vertically (fixed width strip at left)
      layoutRow : List (TreemapNode A) → Float → Float → Float → Float → Float → ℕ → ℕ
                → List (TreemapRect A) × Float × Float × Float × Float × ℕ
      layoutRow [] px' py' w' h' _ cidx _ = ([] , px' , py' , w' , h' , cidx)
      layoutRow row px' py' w' h' tot cidx dep =
        let rowSum = sumFloats (Data.List.map (λ n → tmValue n) row)
        in if w' <ᵇ h'
           then -- Tall: lay row as horizontal strip at top, height = rowSum/total * h
             let stripH = if tot ≤ᵇ 0.0 then 0.0 else (rowSum ÷ tot) * h'
             in (layHoriz row px' py' w' stripH rowSum cidx dep
                , px' , py' + stripH , w' , h' - stripH , cidx)
           else -- Wide: lay row as vertical strip at left, width = rowSum/total * w
             let stripW = if tot ≤ᵇ 0.0 then 0.0 else (rowSum ÷ tot) * w'
             in (layVert row px' py' stripW h' rowSum cidx dep
                , px' + stripW , py' , w' - stripW , h' , cidx)
        where
          layHoriz : List (TreemapNode A) → Float → Float → Float → Float → Float → ℕ → ℕ → List (TreemapRect A)
          layHoriz [] _ _ _ _ _ _ _ = []
          layHoriz (n ∷ ns) lx ly lw lh rowTotal ci dp =
            let frac = if rowTotal ≤ᵇ 0.0 then 0.0 else tmValue n ÷ rowTotal
                nodeW = frac * lw
                nodeColor = case tmColor n of λ where
                  nothing → getColor ci
                  (just c) → c
                rect = mkTreemapRect lx ly nodeW lh (tmLabel n) (tmValue n) nodeColor dp (tmOnClick n)
                kids = positiveNodes (tmChildren n)
                childRects = if listLen kids ≡ᵇ 0 then []
                             else if (nodeW ≤ᵇ 4.0) then []
                             else if (lh ≤ᵇ 4.0) then []
                             else layoutChildren (lx + 2.0) (ly + 2.0) (nodeW - 4.0) (lh - 4.0)
                                    (sumValues kids) 0 (suc dp) kids
            in rect ∷ childRects ++ᴸ layHoriz ns (lx + nodeW) ly (lw - nodeW) lh (rowTotal - tmValue n) (suc ci) dp

          layVert : List (TreemapNode A) → Float → Float → Float → Float → Float → ℕ → ℕ → List (TreemapRect A)
          layVert [] _ _ _ _ _ _ _ = []
          layVert (n ∷ ns) lx ly lw lh rowTotal ci dp =
            let frac = if rowTotal ≤ᵇ 0.0 then 0.0 else tmValue n ÷ rowTotal
                nodeH = frac * lh
                nodeColor = case tmColor n of λ where
                  nothing → getColor ci
                  (just c) → c
                rect = mkTreemapRect lx ly lw nodeH (tmLabel n) (tmValue n) nodeColor dp (tmOnClick n)
                kids = positiveNodes (tmChildren n)
                childRects = if listLen kids ≡ᵇ 0 then []
                             else if (lw ≤ᵇ 4.0) then []
                             else if (nodeH ≤ᵇ 4.0) then []
                             else layoutChildren (lx + 2.0) (ly + 2.0) (lw - 4.0) (nodeH - 4.0)
                                    (sumValues kids) 0 (suc dp) kids
            in rect ∷ childRects ++ᴸ layVert ns lx (ly + nodeH) lw (lh - nodeH) (rowTotal - tmValue n) (suc ci) dp

      -- The short side of the remaining rectangle
      shortSide : Float → Float → Float
      shortSide w' h' = if w' <ᵇ h' then w' else h'

      -- Squarify: greedily build rows by checking aspect ratios.
      -- fuel parameter prevents infinite loops when values don't shrink the rectangle.
      squarify : ℕ → List (TreemapNode A) → List (TreemapNode A)
               → Float → Float → Float → Float → Float → ℕ → ℕ
               → List (TreemapRect A)
      -- Fuel exhausted: finalize whatever row we have and stop
      squarify zero [] _ _ _ _ _ _ _ _ = []
      squarify zero _ row px' py' w' h' tot cidx dep =
        let (rects , _ , _ , _ , _ , _) = layoutRow row px' py' w' h' tot cidx dep
        in rects
      squarify _ [] [] _ _ _ _ _ _ _ = []
      squarify fuel [] row px' py' w' h' tot cidx dep =
        -- No more items, finalize current row
        let (rects , _ , _ , _ , _ , _) = layoutRow row px' py' w' h' tot cidx dep
        in rects
      squarify (suc fuel') (n ∷ rest) [] px' py' w' h' tot cidx dep =
        -- Empty row, always add first item
        squarify fuel' rest (n ∷ []) px' py' w' h' tot cidx dep
      squarify (suc fuel') (n ∷ rest) row px' py' w' h' tot cidx dep =
        let side = shortSide w' h'
            -- Scale node values to pixel areas for ratio computation
            areaScale = if tot ≤ᵇ 0.0 then 0.0 else (w' * h') ÷ tot
            rowAreas = Data.List.map (λ nd → tmValue nd * areaScale) row
            candArea = tmValue n * areaScale
            worstWithout = worstRatio rowAreas side
            worstWith    = worstRatio (rowAreas ++ᴸ (candArea ∷ [])) side
        in if worstWith ≤ᵇ worstWithout
           then -- Adding candidate improves or maintains ratio, add it
             squarify fuel' rest (row ++ᴸ (n ∷ [])) px' py' w' h' tot cidx dep
           else -- Adding candidate worsens ratio, finalize row and start new one
             let (rects , px'' , py'' , w'' , h'' , cidx') = layoutRow row px' py' w' h' tot cidx dep
                 newCidx = cidx +ᴺ listLen row
             in rects ++ᴸ squarify fuel' (n ∷ rest) [] px'' py'' w'' h'' (tot - sumValues row) newCidx dep

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
