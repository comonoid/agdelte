{-# OPTIONS --without-K #-}

-- SVG Sankey Diagram
-- Flow/transfer between nodes visualization

module Agdelte.Svg.Controls.Charts.Sankey where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; map; filter)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; path'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record SankeyNode : Set where
  constructor mkSankeyNode
  field
    snId    : String
    snLabel : String
    snColor : Maybe String

open SankeyNode public

record SankeyLink : Set where
  constructor mkSankeyLink
  field
    slSource : String        -- source node id
    slTarget : String        -- target node id
    slValue  : Float         -- flow value
    slColor  : Maybe String  -- optional link color

open SankeyLink public

-- Internal positioned node
record PositionedNode : Set where
  constructor mkPosNode
  field
    pnId     : String
    pnLabel  : String
    pnColor  : String
    pnX      : Float
    pnY      : Float
    pnWidth  : Float
    pnHeight : Float

open PositionedNode public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  -- String equality check
  open import Data.String using (_≟_)
  open import Relation.Nullary using (yes; no)

  _≡ˢ_ : String → String → Bool
  s ≡ˢ t with s ≟ t
  ... | yes _ = true
  ... | no _ = false

  findNode : String → List PositionedNode → Maybe PositionedNode
  findNode _ [] = nothing
  findNode id' (n ∷ ns) = if pnId n ≡ˢ id' then just n else findNode id' ns

  -- Sum outgoing links from a node
  sumOutgoing : String → List SankeyLink → Float
  sumOutgoing _ [] = 0.0
  sumOutgoing nodeId (l ∷ ls) =
    (if slSource l ≡ˢ nodeId then slValue l else 0.0) + sumOutgoing nodeId ls

  -- Sum incoming links to a node
  sumIncoming : String → List SankeyLink → Float
  sumIncoming _ [] = 0.0
  sumIncoming nodeId (l ∷ ls) =
    (if slTarget l ≡ˢ nodeId then slValue l else 0.0) + sumIncoming nodeId ls

  -- Get node value (max of in/out)
  nodeValue : String → List SankeyLink → Float
  nodeValue nodeId links =
    let out' = sumOutgoing nodeId links
        in' = sumIncoming nodeId links
    in if out' <ᵇ in' then in' else out'

  -- Default colors
  defaultColors : List String
  defaultColors = "#3b82f6" ∷ "#22c55e" ∷ "#f59e0b" ∷ "#ef4444" ∷ "#8b5cf6"
                ∷ "#ec4899" ∷ "#14b8a6" ∷ "#f97316" ∷ []

  getDefaultColor : ℕ → String
  getDefaultColor n = go defaultColors n
    where
      go : List String → ℕ → String
      go [] _ = "#3b82f6"
      go (c ∷ _) zero = c
      go (_ ∷ cs) (suc m) = go cs m

------------------------------------------------------------------------
-- Layout calculation
------------------------------------------------------------------------

private
  -- Determine node columns (0 = source only, 1+ = has incoming)
  getNodeColumn : String → List SankeyLink → ℕ
  getNodeColumn nodeId links =
    if hasIncoming nodeId links then 1 else 0
    where
      hasIncoming : String → List SankeyLink → Bool
      hasIncoming _ [] = false
      hasIncoming nid (l ∷ ls) = if slTarget l ≡ˢ nid then true else hasIncoming nid ls

  -- Simple 2-column layout
  layoutNodes : Float → Float → Float → Float → Float
              → List SankeyNode → List SankeyLink → List PositionedNode
  layoutNodes px py w h nodeWidth nodes links =
    let leftNodes = filterLeft nodes links
        rightNodes = filterRight nodes links
        leftTotal = sumNodeValues leftNodes links
        rightTotal = sumNodeValues rightNodes links
    in positionColumn px py h nodeWidth leftTotal leftNodes links 0.0 0
       ++ᴸ positionColumn (px + w - nodeWidth) py h nodeWidth rightTotal rightNodes links 0.0 (listLen leftNodes)
    where
      open import Data.List renaming (_++_ to _++ᴸ_)

      filterLeft : List SankeyNode → List SankeyLink → List SankeyNode
      filterLeft [] _ = []
      filterLeft (n ∷ ns) ls =
        if getNodeColumn (snId n) ls ≡ᵇ 0
        then n ∷ filterLeft ns ls
        else filterLeft ns ls
        where
          open import Data.Nat using (_≡ᵇ_)

      filterRight : List SankeyNode → List SankeyLink → List SankeyNode
      filterRight [] _ = []
      filterRight (n ∷ ns) ls =
        if getNodeColumn (snId n) ls ≡ᵇ 1
        then n ∷ filterRight ns ls
        else filterRight ns ls
        where
          open import Data.Nat using (_≡ᵇ_)

      sumNodeValues : List SankeyNode → List SankeyLink → Float
      sumNodeValues [] _ = 0.0
      sumNodeValues (n ∷ ns) ls = nodeValue (snId n) ls + sumNodeValues ns ls

      positionColumn : Float → Float → Float → Float → Float
                     → List SankeyNode → List SankeyLink → Float → ℕ
                     → List PositionedNode
      positionColumn _ _ _ _ _ [] _ _ _ = []
      positionColumn colX colY colH nw total (n ∷ ns) ls yOffset colorIdx =
        let val = nodeValue (snId n) ls
            nodeH = if total ≤ᵇ 0.0 then 20.0 else (val ÷ total) * (colH * 0.8)
            nodeY = colY + yOffset
            color = case snColor n of λ where
              nothing → getDefaultColor colorIdx
              (just c) → c
        in mkPosNode (snId n) (snLabel n) color colX nodeY nw nodeH
           ∷ positionColumn colX colY colH nw total ns ls (yOffset + nodeH + 10.0) (suc colorIdx)
        where
          case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
          case x of f = f x

------------------------------------------------------------------------
-- Link rendering (curved paths)
------------------------------------------------------------------------

private
  renderLink : ∀ {M A} → List PositionedNode → SankeyLink → Float → Float → Node M A
  renderLink nodes link totalOut sourceYOffset =
    case (findNode (slSource link) nodes , findNode (slTarget link) nodes) of λ where
      (just src , just tgt) →
        let linkHeight = slValue link
            -- Source point
            sx = pnX src + pnWidth src
            sy = pnY src + sourceYOffset + linkHeight ÷ 2.0
            -- Target point (find position based on incoming offset)
            tx = pnX tgt
            ty = pnY tgt + linkHeight ÷ 2.0
            -- Control points for bezier curve
            cx1 = sx + (tx - sx) ÷ 3.0
            cx2 = tx - (tx - sx) ÷ 3.0
            -- Build path for flow band
            pathD = buildFlowPath sx sy tx ty linkHeight cx1 cx2
            color = case slColor link of λ where
              nothing → pnColor src
              (just c) → c
        in path' ( d_ pathD
                 ∷ fill_ color
                 ∷ attr "opacity" "0.5"
                 ∷ [] ) []
      _ → g [] []
    where
      case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
      case x of f = f x

      buildFlowPath : Float → Float → Float → Float → Float → Float → Float → String
      buildFlowPath sx sy tx ty lh cx1 cx2 =
        let topSy = sy - lh ÷ 2.0
            botSy = sy + lh ÷ 2.0
            topTy = ty - lh ÷ 2.0
            botTy = ty + lh ÷ 2.0
        in "M " ++ showFloat sx ++ " " ++ showFloat topSy
           ++ " C " ++ showFloat cx1 ++ " " ++ showFloat topSy
                    ++ " " ++ showFloat cx2 ++ " " ++ showFloat topTy
                    ++ " " ++ showFloat tx ++ " " ++ showFloat topTy
           ++ " L " ++ showFloat tx ++ " " ++ showFloat botTy
           ++ " C " ++ showFloat cx2 ++ " " ++ showFloat botTy
                    ++ " " ++ showFloat cx1 ++ " " ++ showFloat botSy
                    ++ " " ++ showFloat sx ++ " " ++ showFloat botSy
           ++ " Z"

  renderLinks : ∀ {M A} → List PositionedNode → List SankeyLink → List (Node M A)
  renderLinks _ [] = []
  renderLinks nodes (l ∷ ls) =
    renderLink nodes l 0.0 0.0
    ∷ renderLinks nodes ls

------------------------------------------------------------------------
-- Node rendering
------------------------------------------------------------------------

private
  renderNode : ∀ {M A} → PositionedNode → Node M A
  renderNode n =
    g ( attr "class" "sankey-node" ∷ [] )
      ( rect' ( xF (pnX n) ∷ yF (pnY n)
              ∷ widthF (pnWidth n) ∷ heightF (pnHeight n)
              ∷ fill_ (pnColor n)
              ∷ [] ) []
      ∷ svgText ( xF (pnX n + pnWidth n + 5.0) ∷ yF (pnY n + pnHeight n ÷ 2.0)
                ∷ attr "dominant-baseline" "middle"
                ∷ attr "font-size" "11"
                ∷ fill_ "#374151"
                ∷ [] )
          ( text (pnLabel n) ∷ [] )
      ∷ [] )

  renderNodes : ∀ {M A} → List PositionedNode → List (Node M A)
  renderNodes [] = []
  renderNodes (n ∷ ns) = renderNode n ∷ renderNodes ns

------------------------------------------------------------------------
-- Sankey Diagram
------------------------------------------------------------------------

-- | Full Sankey diagram
sankeyDiagram : ∀ {M A}
              → Float → Float → Float → Float  -- x, y, width, height
              → Float                           -- node width
              → List SankeyNode
              → List SankeyLink
              → Node M A
sankeyDiagram {M} {A} px py w h nodeWidth nodes links =
  let posNodes = layoutNodes px py w h nodeWidth nodes links
  in g ( attr "class" "svg-sankey-diagram" ∷ [] )
       ( g ( attr "class" "sankey-links" ∷ [] )
           (renderLinks posNodes links)
       ∷ g ( attr "class" "sankey-nodes" ∷ [] )
           (renderNodes posNodes)
       ∷ [] )

------------------------------------------------------------------------
-- Simple Sankey
------------------------------------------------------------------------

-- | Simple sankey from flow data
simpleSankey : ∀ {M A}
             → Float → Float → Float → Float
             → List (String × String × Float)  -- (from, to, value)
             → Node M A
simpleSankey {M} {A} px py w h flows =
  sankeyDiagram px py w h 20.0 (extractNodes flows) (toLinks flows)
  where
    extractNodes : List (String × String × Float) → List SankeyNode
    extractNodes [] = []
    extractNodes ((from' , to' , _) ∷ rest) =
      mkSankeyNode from' from' nothing
      ∷ mkSankeyNode to' to' nothing
      ∷ extractNodes rest

    toLinks : List (String × String × Float) → List SankeyLink
    toLinks [] = []
    toLinks ((from' , to' , val) ∷ rest) =
      mkSankeyLink from' to' val nothing
      ∷ toLinks rest

------------------------------------------------------------------------
-- Energy Flow Sankey
------------------------------------------------------------------------

-- | Energy flow visualization style
energyFlowSankey : ∀ {M A}
                 → Float → Float → Float → Float
                 → List SankeyNode
                 → List SankeyLink
                 → Node M A
energyFlowSankey px py w h nodes links =
  sankeyDiagram px py w h 25.0 nodes links

------------------------------------------------------------------------
-- Budget Sankey
------------------------------------------------------------------------

-- | Budget/money flow visualization
budgetSankey : ∀ {M A}
             → Float → Float → Float → Float
             → List (String × Float)           -- income sources
             → List (String × Float)           -- expense categories
             → Node M A
budgetSankey {M} {A} px py w h incomes expenses =
  sankeyDiagram px py w h 20.0 nodes links
  where
    open import Data.Nat.Show using (show)
    showℕ : ℕ → String
    showℕ = show

    incomeNodes : List SankeyNode
    incomeNodes = go incomes 0
      where
        go : List (String × Float) → ℕ → List SankeyNode
        go [] _ = []
        go ((name , _) ∷ rest) idx =
          mkSankeyNode ("in" ++ showℕ idx) name (just "#22c55e")
          ∷ go rest (suc idx)

    expenseNodes : List SankeyNode
    expenseNodes = go expenses 0
      where
        go : List (String × Float) → ℕ → List SankeyNode
        go [] _ = []
        go ((name , _) ∷ rest) idx =
          mkSankeyNode ("out" ++ showℕ idx) name (just "#ef4444")
          ∷ go rest (suc idx)

    nodes : List SankeyNode
    nodes = incomeNodes ++ᴸ expenseNodes
      where
        open import Data.List renaming (_++_ to _++ᴸ_)

    incomeLinks : List SankeyLink
    incomeLinks = go incomes 0
      where
        go : List (String × Float) → ℕ → List SankeyLink
        go [] _ = []
        go ((_ , val) ∷ rest) idx =
          mkSankeyLink ("in" ++ showℕ idx) ("out0") val nothing
          ∷ go rest (suc idx)

    -- Simplified: all income flows to first expense
    links : List SankeyLink
    links = incomeLinks
