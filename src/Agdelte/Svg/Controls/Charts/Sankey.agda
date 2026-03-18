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
  -- Column assignment as association list (node id → column)
  ColumnMap : Set
  ColumnMap = List (String × ℕ)

  lookupCol : String → ColumnMap → ℕ
  lookupCol _ [] = 0
  lookupCol nid ((k , v) ∷ rest) = if k ≡ˢ nid then v else lookupCol nid rest

  updateCol : String → ℕ → ColumnMap → ColumnMap
  updateCol nid col [] = (nid , col) ∷ []
  updateCol nid col ((k , v) ∷ rest) =
    if k ≡ˢ nid then (k , col) ∷ rest
    else (k , v) ∷ updateCol nid col rest

  -- Initialize column map: nodes with no incoming links = 0, others = 0 (to be updated)
  initColumnMap : List SankeyNode → ColumnMap
  initColumnMap [] = []
  initColumnMap (n ∷ ns) = (snId n , 0) ∷ initColumnMap ns

  -- Single pass over links: for each link, set target col = max(target col, source col + 1)
  propagateLinks : List SankeyLink → ColumnMap → ColumnMap
  propagateLinks [] cm = cm
  propagateLinks (l ∷ ls) cm =
    let srcCol = lookupCol (slSource l) cm
        tgtCol = lookupCol (slTarget l) cm
        newCol = suc srcCol
        cm' = if tgtCol <ᵇ newCol then updateCol (slTarget l) newCol cm else cm
    in propagateLinks ls cm'
    where
      open import Data.Nat using (_<ᵇ_)

  -- Iterate propagation (repeat as many times as there are nodes for convergence)
  iteratePropagate : ℕ → List SankeyLink → ColumnMap → ColumnMap
  iteratePropagate zero _ cm = cm
  iteratePropagate (suc n) links' cm = iteratePropagate n links' (propagateLinks links' cm)

  -- Compute column assignments for all nodes
  computeColumns : List SankeyNode → List SankeyLink → ColumnMap
  computeColumns nodes links' =
    let cm0 = initColumnMap nodes
    in iteratePropagate (listLen nodes) links' cm0

  -- Find the maximum column number
  maxColumn : ColumnMap → ℕ
  maxColumn [] = 0
  maxColumn ((_ , c) ∷ rest) = if c <ᵇ maxColumn rest then maxColumn rest else c
    where
      open import Data.Nat using (_<ᵇ_)

  -- Determine node columns using iterative propagation
  getNodeColumn : String → ColumnMap → ℕ
  getNodeColumn = lookupCol

  -- Filter nodes by column
  filterByColumn : ℕ → List SankeyNode → ColumnMap → List SankeyNode
  filterByColumn _ [] _ = []
  filterByColumn col (n ∷ ns) cm =
    if getNodeColumn (snId n) cm ≡ᵇ col
    then n ∷ filterByColumn col ns cm
    else filterByColumn col ns cm
    where
      open import Data.Nat using (_≡ᵇ_)

  -- Multi-column layout
  layoutNodes : Float → Float → Float → Float → Float
              → List SankeyNode → List SankeyLink → List PositionedNode
  layoutNodes px py w h nodeWidth nodes links =
    let cm = computeColumns nodes links
        numCols = suc (maxColumn cm)
        colSpan = if numCols ≡ᵇ 1 then 0.0 else (w - nodeWidth) ÷ fromℕ (numCols ∸ 1)
    in layoutAllColumns 0 numCols px py w h nodeWidth colSpan nodes links cm 0
    where
      open import Data.Nat using (_≡ᵇ_; _∸_; _<ᵇ_) renaming (_+_ to _+ℕ_)
      open import Data.List renaming (_++_ to _++ᴸ_)

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

      layoutAllColumns : ℕ → ℕ → Float → Float → Float → Float → Float → Float
                       → List SankeyNode → List SankeyLink → ColumnMap → ℕ
                       → List PositionedNode
      layoutAllColumns col numCols px' py' w' h' nw colW nodes' links' cm colorIdx =
        if numCols ≡ᵇ 0 then []
        else if col <ᵇ numCols
        then let colNodes = filterByColumn col nodes' cm
                 colTotal = sumNodeValues colNodes links'
                 colX = px' + fromℕ col * colW
                 positioned = positionColumn colX py' h' nw colTotal colNodes links' 0.0 colorIdx
             in positioned ++ᴸ layoutAllColumns (suc col) numCols px' py' w' h' nw colW nodes' links' cm (colorIdx +ℕ listLen colNodes)
        else []

------------------------------------------------------------------------
-- Link rendering (curved paths)
------------------------------------------------------------------------

private
  renderLink : ∀ {M A} → List PositionedNode → SankeyLink → Float → Float → Node M A
  renderLink nodes link totalOut sourceYOffset =
    case (findNode (slSource link) nodes , findNode (slTarget link) nodes) of λ where
      (just src , just tgt) →
        let linkHeight = if totalOut ≤ᵇ 0.0 then 2.0
                         else (slValue link ÷ totalOut) * pnHeight src
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
  renderLinks nodes allLinks = go nodes allLinks allLinks []
    where
      go : List PositionedNode → List SankeyLink → List SankeyLink → List SankeyLink → List (Node M A)
      go _ _ [] _ = []
      go ns all' (l ∷ ls) prev =
        let srcId = slSource l
            totalOut = sumOutgoing srcId all'
            -- Sum heights of previous links with same source
            prevOffset = sumPrevOffset srcId prev ns all'
        in renderLink ns l totalOut prevOffset
           ∷ go ns all' ls (prev ++ᴸ (l ∷ []))
        where
          open import Data.List renaming (_++_ to _++ᴸ_)

          sumPrevOffset : String → List SankeyLink → List PositionedNode → List SankeyLink → Float
          sumPrevOffset _ [] _ _ = 0.0
          sumPrevOffset sid (p ∷ ps) posNodes all' =
            (if slSource p ≡ˢ sid
             then let tot = sumOutgoing sid all'
                  in case findNode sid posNodes of λ where
                       (just src) → if tot ≤ᵇ 0.0 then 2.0
                                    else (slValue p ÷ tot) * pnHeight src
                       nothing → 0.0
             else 0.0)
            + sumPrevOffset sid ps posNodes all'
            where
              case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
              case x of f = f x

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
    extractNodes flows' = dedup (collectAll flows')
      where
        collectAll : List (String × String × Float) → List SankeyNode
        collectAll [] = []
        collectAll ((from' , to' , _) ∷ rest) =
          mkSankeyNode from' from' nothing
          ∷ mkSankeyNode to' to' nothing
          ∷ collectAll rest

        -- Remove duplicate nodes by ID
        hasId : String → List SankeyNode → Bool
        hasId _ [] = false
        hasId id' (n ∷ ns) = if snId n ≡ˢ id' then true else hasId id' ns
          where
            open import Data.String using (_≟_)
            open import Relation.Nullary using (yes; no)
            _≡ˢ_ : String → String → Bool
            s ≡ˢ t with s ≟ t
            ... | yes _ = true
            ... | no _ = false

        dedup : List SankeyNode → List SankeyNode
        dedup [] = []
        dedup (n ∷ ns) =
          if hasId (snId n) ns
          then dedup ns
          else n ∷ dedup ns

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

    -- Sum all expense values
    totalExpenses : Float
    totalExpenses = sumExpenses expenses
      where
        sumExpenses : List (String × Float) → Float
        sumExpenses [] = 0.0
        sumExpenses ((_ , v) ∷ rest) = v + sumExpenses rest

    -- For each income source, create links to ALL expenses proportionally
    incomeLinks : List SankeyLink
    incomeLinks = goIncomes incomes 0
      where
        -- Generate links from one income source to all expenses
        linksForIncome : String → Float → List (String × Float) → ℕ → List SankeyLink
        linksForIncome _ _ [] _ = []
        linksForIncome srcId incomeVal ((_ , expVal) ∷ rest) expIdx =
          let linkVal = if totalExpenses ≤ᵇ 0.0 then 0.0
                        else incomeVal * (expVal ÷ totalExpenses)
          in mkSankeyLink srcId ("out" ++ showℕ expIdx) linkVal nothing
             ∷ linksForIncome srcId incomeVal rest (suc expIdx)

        goIncomes : List (String × Float) → ℕ → List SankeyLink
        goIncomes [] _ = []
        goIncomes ((_ , val) ∷ rest) idx =
          linksForIncome ("in" ++ showℕ idx) val expenses 0
          ++ᴸ goIncomes rest (suc idx)
          where
            open import Data.List renaming (_++_ to _++ᴸ_)

    -- Distribute income proportionally across all expenses
    links : List SankeyLink
    links = incomeLinks
