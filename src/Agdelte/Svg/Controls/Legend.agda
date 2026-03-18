{-# OPTIONS --without-K #-}

-- SvgLegend: chart legend component
-- Shows color/symbol mapping for data series

module Agdelte.Svg.Controls.Legend where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤ᵇ_)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (g; rect'; circle'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Legend Item Shape
------------------------------------------------------------------------

data LegendShape : Set where
  Square  : LegendShape
  Circle  : LegendShape
  Line    : LegendShape

------------------------------------------------------------------------
-- Legend Style
------------------------------------------------------------------------

record LegendStyle : Set where
  constructor mkLegendStyle
  field
    itemSize      : Float     -- size of color indicator
    itemGap       : Float     -- gap between indicator and label
    rowGap        : Float     -- gap between rows
    labelColor    : String
    labelSize     : String
    labelFamily   : String

open LegendStyle public

defaultLegendStyle : LegendStyle
defaultLegendStyle = mkLegendStyle
  12.0         -- item size
  8.0          -- item gap
  20.0         -- row gap
  "#374151"    -- dark label
  "12px"
  "system-ui, sans-serif"

darkLegendStyle : LegendStyle
darkLegendStyle = mkLegendStyle
  12.0
  8.0
  20.0
  "#e5e7eb"    -- light label
  "12px"
  "system-ui, sans-serif"

------------------------------------------------------------------------
-- Legend Item
------------------------------------------------------------------------

record LegendItem : Set where
  constructor mkLegendItem
  field
    itemLabel : String
    itemColor : String
    itemShape : LegendShape

open LegendItem public

------------------------------------------------------------------------
-- Single Legend Item
------------------------------------------------------------------------

svgLegendItem : ∀ {M Msg}
              → Float → Float      -- x, y
              → LegendItem
              → LegendStyle
              → Node M Msg
svgLegendItem px py item sty =
  let size = itemSize sty
      labelX = px + size + itemGap sty
      cy = py + size ÷ 2.0
  in g ( attr "class" "svg-legend-item" ∷ [] )
       ( renderShape (itemShape item) px py size (itemColor item)
       ∷ svgText ( attrX labelX
                 ∷ attrY cy
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily (labelFamily sty)
                 ∷ dominantBaseline_ "central"
                 ∷ [] ) ( text (itemLabel item) ∷ [] )
       ∷ [] )
  where
    renderShape : LegendShape → Float → Float → Float → String → Node _ _
    renderShape Square px' py' s c =
      rect' ( attrX px'
            ∷ attrY py'
            ∷ widthF s
            ∷ heightF s
            ∷ fill_ c
            ∷ rxF 2.0
            ∷ ryF 2.0
            ∷ [] ) []
    renderShape Circle px' py' s c =
      circle' ( attrCx (px' + s ÷ 2.0)
              ∷ attrCy (py' + s ÷ 2.0)
              ∷ rF (s ÷ 2.0)
              ∷ fill_ c
              ∷ [] ) []
    renderShape Line px' py' s c =
      elem "line" ( attr "x1" (showFloat px')
                  ∷ attr "y1" (showFloat (py' + s ÷ 2.0))
                  ∷ attr "x2" (showFloat (px' + s))
                  ∷ attr "y2" (showFloat (py' + s ÷ 2.0))
                  ∷ stroke_ c
                  ∷ strokeWidthF 2.0
                  ∷ attr "stroke-linecap" "round"
                  ∷ [] ) []

------------------------------------------------------------------------
-- Vertical Legend
------------------------------------------------------------------------

svgLegendV : ∀ {M Msg}
           → Float → Float        -- x, y
           → List LegendItem
           → LegendStyle
           → Node M Msg
svgLegendV {M} {Msg} px py items sty =
  g ( attr "class" "svg-legend-v" ∷ [] )
    (renderItems py items)
  where
    renderItems : Float → List LegendItem → List (Node M Msg)
    renderItems _ [] = []
    renderItems currentY (item ∷ rest) =
      svgLegendItem px currentY item sty
      ∷ renderItems (currentY + rowGap sty) rest

------------------------------------------------------------------------
-- Horizontal Legend
------------------------------------------------------------------------

svgLegendH : ∀ {M Msg}
           → Float → Float        -- x, y
           → List LegendItem
           → Float                -- item width (for spacing)
           → LegendStyle
           → Node M Msg
svgLegendH {M} {Msg} px py items itemW sty =
  g ( attr "class" "svg-legend-h" ∷ [] )
    (renderItems px items)
  where
    renderItems : Float → List LegendItem → List (Node M Msg)
    renderItems _ [] = []
    renderItems currentX (item ∷ rest) =
      svgLegendItem currentX py item sty
      ∷ renderItems (currentX + itemW) rest

------------------------------------------------------------------------
-- Simple Legends
------------------------------------------------------------------------

-- Create a simple colored square legend
svgLegendSimple : ∀ {M Msg}
                → Float → Float
                → List (String × String)  -- (label, color) pairs
                → Node M Msg
svgLegendSimple {M} {Msg} px py pairs =
  svgLegendV px py (toItems pairs) defaultLegendStyle
  where
    toItems : List (String × String) → List LegendItem
    toItems [] = []
    toItems ((lbl , clr) ∷ rest) =
      mkLegendItem lbl clr Square ∷ toItems rest

------------------------------------------------------------------------
-- Chart Color Palette
------------------------------------------------------------------------

-- Common chart colors
chartColors : List String
chartColors =
    "#3b82f6"    -- blue
  ∷ "#22c55e"    -- green
  ∷ "#f59e0b"    -- amber
  ∷ "#ef4444"    -- red
  ∷ "#8b5cf6"    -- purple
  ∷ "#06b6d4"    -- cyan
  ∷ "#ec4899"    -- pink
  ∷ "#84cc16"    -- lime
  ∷ []

------------------------------------------------------------------------
-- Legend item with textLength (truncates long labels)
------------------------------------------------------------------------

-- | Render a legend item with a maximum label width (SVG textLength).
-- | Long labels are compressed to fit within the given width.
svgLegendItemTrunc : ∀ {M Msg}
                   → Float → Float      -- x, y
                   → Float              -- max label width
                   → LegendItem
                   → LegendStyle
                   → Node M Msg
svgLegendItemTrunc px py maxLabelW item sty =
  let size = itemSize sty
      labelX = px + size + itemGap sty
      cy = py + size ÷ 2.0
  in g ( attr "class" "svg-legend-item" ∷ [] )
       ( renderShape (itemShape item) px py size (itemColor item)
       ∷ svgText ( attrX labelX
                 ∷ attrY cy
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily (labelFamily sty)
                 ∷ dominantBaseline_ "central"
                 ∷ attr "textLength" (showFloat maxLabelW)
                 ∷ attr "lengthAdjust" "spacingAndGlyphs"
                 ∷ [] ) ( text (itemLabel item) ∷ [] )
       ∷ [] )
  where
    renderShape : LegendShape → Float → Float → Float → String → Node _ _
    renderShape Square px' py' s c =
      rect' ( attrX px'
            ∷ attrY py'
            ∷ widthF s
            ∷ heightF s
            ∷ fill_ c
            ∷ rxF 2.0
            ∷ ryF 2.0
            ∷ [] ) []
    renderShape Circle px' py' s c =
      circle' ( attrCx (px' + s ÷ 2.0)
              ∷ attrCy (py' + s ÷ 2.0)
              ∷ rF (s ÷ 2.0)
              ∷ fill_ c
              ∷ [] ) []
    renderShape Line px' py' s c =
      elem "line" ( attr "x1" (showFloat px')
                  ∷ attr "y1" (showFloat (py' + s ÷ 2.0))
                  ∷ attr "x2" (showFloat (px' + s))
                  ∷ attr "y2" (showFloat (py' + s ÷ 2.0))
                  ∷ stroke_ c
                  ∷ strokeWidthF 2.0
                  ∷ attr "stroke-linecap" "round"
                  ∷ [] ) []

------------------------------------------------------------------------
-- Vertical Legend with maxItems (truncation + "... and N more")
------------------------------------------------------------------------

-- | Vertical legend that truncates after maxItems.
-- | Shows "... and N more" when items exceed maxItems.
svgLegendVMax : ∀ {M Msg}
              → Float → Float        -- x, y
              → ℕ                    -- maxItems
              → List LegendItem
              → LegendStyle
              → Node M Msg
svgLegendVMax {M} {Msg} px py maxN items sty =
  let total   = length items
      shown   = take maxN items
      overflow = total ∸ maxN
  in g ( attr "class" "svg-legend-v" ∷ [] )
       ( renderItems py shown
         ++ overflowLabel py (length shown) overflow )
  where
    renderItems : Float → List LegendItem → List (Node M Msg)
    renderItems _ [] = []
    renderItems currentY (item ∷ rest) =
      svgLegendItem px currentY item sty
      ∷ renderItems (currentY + rowGap sty) rest

    overflowLabel : Float → ℕ → ℕ → List (Node M Msg)
    overflowLabel _ _ zero = []
    overflowLabel baseY nShown (suc n) =
      let labelY = baseY + (rowGap sty * showNatF nShown)
      in svgText ( attrX px
                 ∷ attrY labelY
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily (labelFamily sty)
                 ∷ dominantBaseline_ "central"
                 ∷ attr "font-style" "italic"
                 ∷ [] )
           ( text ("… and " ++ˢ showNat (suc n) ++ˢ " more") ∷ [] )
         ∷ []

    showNatF : ℕ → Float
    showNatF zero = 0.0
    showNatF (suc n) = 1.0 + showNatF n

-- | Horizontal legend that truncates after maxItems.
svgLegendHMax : ∀ {M Msg}
              → Float → Float        -- x, y
              → ℕ                    -- maxItems
              → List LegendItem
              → Float                -- item width
              → LegendStyle
              → Node M Msg
svgLegendHMax {M} {Msg} px py maxN items itemW sty =
  let total   = length items
      shown   = take maxN items
      overflow = total ∸ maxN
  in g ( attr "class" "svg-legend-h" ∷ [] )
       ( renderItems px shown
         ++ overflowLabel px (length shown) overflow )
  where
    renderItems : Float → List LegendItem → List (Node M Msg)
    renderItems _ [] = []
    renderItems currentX (item ∷ rest) =
      svgLegendItem currentX py item sty
      ∷ renderItems (currentX + itemW) rest

    overflowLabel : Float → ℕ → ℕ → List (Node M Msg)
    overflowLabel _ _ zero = []
    overflowLabel baseX nShown (suc n) =
      let labelX = baseX + (itemW * showNatF nShown)
      in svgText ( attrX labelX
                 ∷ attrY py
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily (labelFamily sty)
                 ∷ dominantBaseline_ "central"
                 ∷ attr "font-style" "italic"
                 ∷ [] )
           ( text ("… and " ++ˢ showNat (suc n) ++ˢ " more") ∷ [] )
         ∷ []

    showNatF : ℕ → Float
    showNatF zero = 0.0
    showNatF (suc n) = 1.0 + showNatF n
