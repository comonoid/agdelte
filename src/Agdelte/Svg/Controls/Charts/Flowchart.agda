{-# OPTIONS --without-K #-}

-- SVG Flowchart
-- Process flow diagrams with shaped nodes

module Agdelte.Svg.Controls.Charts.Flowchart where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; path'; circle'; svgText; line'; polygon')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

-- Shape types for flowchart nodes
data FlowShape : Set where
  Rectangle   : FlowShape    -- Process/action
  Rounded     : FlowShape    -- Start/End (terminal)
  Diamond     : FlowShape    -- Decision
  Parallelogram : FlowShape  -- Input/Output
  Circle      : FlowShape    -- Connector

record FlowNode (A : Set) : Set where
  constructor mkFlowNode
  field
    fnId      : String
    fnLabel   : String
    fnShape   : FlowShape
    fnX       : Float
    fnY       : Float
    fnWidth   : Float
    fnHeight  : Float
    fnColor   : String
    fnOnClick : Maybe A

open FlowNode public

record FlowEdge : Set where
  constructor mkFlowEdge
  field
    feSource    : String
    feTarget    : String
    feLabel     : Maybe String
    feDirection : String        -- "down", "right", "left", "up"

open FlowEdge public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findNode : ∀ {A} → String → List (FlowNode A) → Maybe (FlowNode A)
  findNode _ [] = nothing
  findNode id' (n ∷ ns) =
    if fnId n ≡ˢ id'
    then just n
    else findNode id' ns
    where
      open import Data.String using (_≟_)
      open import Relation.Nullary using (yes; no)
      _≡ˢ_ : String → String → Bool
      s ≡ˢ t with s ≟ t
      ... | yes _ = true
      ... | no _ = false

  -- Get connection points for nodes
  getConnectionPoint : ∀ {A} → FlowNode A → String → Float × Float
  getConnectionPoint n dir =
    let cx = fnX n + fnWidth n ÷ 2.0
        cy = fnY n + fnHeight n ÷ 2.0
    in if dir ≡ˢ "top"    then (cx , fnY n)
       else if dir ≡ˢ "bottom" then (cx , fnY n + fnHeight n)
       else if dir ≡ˢ "left"   then (fnX n , cy)
       else (fnX n + fnWidth n , cy)  -- right
    where
      open import Data.String using (_≟_)
      open import Relation.Nullary using (yes; no)
      _≡ˢ_ : String → String → Bool
      s ≡ˢ t with s ≟ t
      ... | yes _ = true
      ... | no _ = false

------------------------------------------------------------------------
-- Shape Rendering
------------------------------------------------------------------------

private
  case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
  case x of f = f x

  renderShape : ∀ {M A} → FlowNode A → Node M A
  renderShape n = case fnShape n of λ where
    Rectangle →
      rect' ( xF (fnX n) ∷ yF (fnY n)
            ∷ widthF (fnWidth n) ∷ heightF (fnHeight n)
            ∷ fill_ (fnColor n)
            ∷ stroke_ "#374151"
            ∷ strokeWidthF 2.0
            ∷ [] ) []

    Rounded →
      rect' ( xF (fnX n) ∷ yF (fnY n)
            ∷ widthF (fnWidth n) ∷ heightF (fnHeight n)
            ∷ attr "rx" "20"
            ∷ attr "ry" "20"
            ∷ fill_ (fnColor n)
            ∷ stroke_ "#374151"
            ∷ strokeWidthF 2.0
            ∷ [] ) []

    Diamond →
      let cx = fnX n + fnWidth n ÷ 2.0
          cy = fnY n + fnHeight n ÷ 2.0
          w2 = fnWidth n ÷ 2.0
          h2 = fnHeight n ÷ 2.0
          points = showFloat cx ++ "," ++ showFloat (fnY n) ++ " "
                 ++ showFloat (fnX n + fnWidth n) ++ "," ++ showFloat cy ++ " "
                 ++ showFloat cx ++ "," ++ showFloat (fnY n + fnHeight n) ++ " "
                 ++ showFloat (fnX n) ++ "," ++ showFloat cy
      in polygon' ( attr "points" points
                  ∷ fill_ (fnColor n)
                  ∷ stroke_ "#374151"
                  ∷ strokeWidthF 2.0
                  ∷ [] ) []

    Parallelogram →
      let skew = fnHeight n * 0.2
          d = "M " ++ showFloat (fnX n + skew) ++ " " ++ showFloat (fnY n)
            ++ " L " ++ showFloat (fnX n + fnWidth n) ++ " " ++ showFloat (fnY n)
            ++ " L " ++ showFloat (fnX n + fnWidth n - skew) ++ " " ++ showFloat (fnY n + fnHeight n)
            ++ " L " ++ showFloat (fnX n) ++ " " ++ showFloat (fnY n + fnHeight n)
            ++ " Z"
      in path' ( d_ d
               ∷ fill_ (fnColor n)
               ∷ stroke_ "#374151"
               ∷ strokeWidthF 2.0
               ∷ [] ) []

    Circle →
      let r = if fnWidth n <ᵇ fnHeight n then fnWidth n ÷ 2.0 else fnHeight n ÷ 2.0
      in circle' ( cxF (fnX n + fnWidth n ÷ 2.0)
                 ∷ cyF (fnY n + fnHeight n ÷ 2.0)
                 ∷ rF r
                 ∷ fill_ (fnColor n)
                 ∷ stroke_ "#374151"
                 ∷ strokeWidthF 2.0
                 ∷ [] ) []

  renderLabel : ∀ {M A} → FlowNode A → Node M A
  renderLabel n =
    svgText ( xF (fnX n + fnWidth n ÷ 2.0)
            ∷ yF (fnY n + fnHeight n ÷ 2.0)
            ∷ attr "text-anchor" "middle"
            ∷ attr "dominant-baseline" "middle"
            ∷ attr "font-size" "12"
            ∷ fill_ "#1e293b"
            ∷ [] )
      ( text (fnLabel n) ∷ [] )

  renderNode : ∀ {M A'} → FlowNode A' → Node M A'
  renderNode n =
    case fnOnClick n of λ where
      nothing →
        g ( attr "class" "flowchart-node" ∷ [] )
          ( renderShape n
          ∷ renderLabel n
          ∷ [] )
      (just msg) →
        g ( attr "class" "flowchart-node flowchart-node--clickable"
          ∷ attr "style" "cursor: pointer"
          ∷ on "click" msg
          ∷ [] )
          ( renderShape n
          ∷ renderLabel n
          ∷ [] )

------------------------------------------------------------------------
-- Edge Rendering
------------------------------------------------------------------------

private
  renderArrowHead : ∀ {M A} → Float → Float → String → Node M A
  renderArrowHead tx ty dir =
    let size = 8.0
        points = if dir ≡ˢ "down"
                 then showFloat (tx - size) ++ "," ++ showFloat (ty - size * 1.5) ++ " "
                    ++ showFloat tx ++ "," ++ showFloat ty ++ " "
                    ++ showFloat (tx + size) ++ "," ++ showFloat (ty - size * 1.5)
                 else if dir ≡ˢ "up"
                 then showFloat (tx - size) ++ "," ++ showFloat (ty + size * 1.5) ++ " "
                    ++ showFloat tx ++ "," ++ showFloat ty ++ " "
                    ++ showFloat (tx + size) ++ "," ++ showFloat (ty + size * 1.5)
                 else if dir ≡ˢ "right"
                 then showFloat (tx - size * 1.5) ++ "," ++ showFloat (ty - size) ++ " "
                    ++ showFloat tx ++ "," ++ showFloat ty ++ " "
                    ++ showFloat (tx - size * 1.5) ++ "," ++ showFloat (ty + size)
                 else -- left
                      showFloat (tx + size * 1.5) ++ "," ++ showFloat (ty - size) ++ " "
                    ++ showFloat tx ++ "," ++ showFloat ty ++ " "
                    ++ showFloat (tx + size * 1.5) ++ "," ++ showFloat (ty + size)
    in polygon' ( attr "points" points
                ∷ fill_ "#374151"
                ∷ [] ) []
    where
      open import Data.String using (_≟_)
      open import Relation.Nullary using (yes; no)
      _≡ˢ_ : String → String → Bool
      s ≡ˢ t with s ≟ t
      ... | yes _ = true
      ... | no _ = false

  renderEdge : ∀ {M A} → List (FlowNode A) → FlowEdge → Node M A
  renderEdge {_} {A} nodes e =
    case (findNode (feSource e) nodes , findNode (feTarget e) nodes) of λ where
      (just src , just tgt) →
        let (sx , sy) = getSourcePoint src (feDirection e)
            (tx , ty) = getTargetPoint tgt (feDirection e)
            pathD = buildPath sx sy tx ty (feDirection e)
        in g ( attr "class" "flowchart-edge" ∷ [] )
             ( path' ( d_ pathD
                     ∷ fill_ "none"
                     ∷ stroke_ "#374151"
                     ∷ strokeWidthF 2.0
                     ∷ [] ) []
             ∷ renderArrowHead tx ty (feDirection e)
             ∷ (case feLabel e of λ where
                  nothing → g [] []
                  (just lbl) →
                    svgText ( xF ((sx + tx) ÷ 2.0)
                            ∷ yF ((sy + ty) ÷ 2.0 - 5.0)
                            ∷ attr "text-anchor" "middle"
                            ∷ attr "font-size" "10"
                            ∷ fill_ "#64748b"
                            ∷ [] )
                      ( text lbl ∷ [] ))
             ∷ [] )
      _ → g [] []
    where
      getSourcePoint : FlowNode A → String → Float × Float
      getSourcePoint n dir =
        if dir ≡ˢ "down"  then (fnX n + fnWidth n ÷ 2.0 , fnY n + fnHeight n)
        else if dir ≡ˢ "up"    then (fnX n + fnWidth n ÷ 2.0 , fnY n)
        else if dir ≡ˢ "right" then (fnX n + fnWidth n , fnY n + fnHeight n ÷ 2.0)
        else (fnX n , fnY n + fnHeight n ÷ 2.0)
        where
          open import Data.String using (_≟_)
          open import Relation.Nullary using (yes; no)
          _≡ˢ_ : String → String → Bool
          s ≡ˢ t with s ≟ t
          ... | yes _ = true
          ... | no _ = false

      getTargetPoint : FlowNode A → String → Float × Float
      getTargetPoint n dir =
        if dir ≡ˢ "down"  then (fnX n + fnWidth n ÷ 2.0 , fnY n)
        else if dir ≡ˢ "up"    then (fnX n + fnWidth n ÷ 2.0 , fnY n + fnHeight n)
        else if dir ≡ˢ "right" then (fnX n , fnY n + fnHeight n ÷ 2.0)
        else (fnX n + fnWidth n , fnY n + fnHeight n ÷ 2.0)
        where
          open import Data.String using (_≟_)
          open import Relation.Nullary using (yes; no)
          _≡ˢ_ : String → String → Bool
          s ≡ˢ t with s ≟ t
          ... | yes _ = true
          ... | no _ = false

      buildPath : Float → Float → Float → Float → String → String
      buildPath sx sy tx ty dir =
        "M " ++ showFloat sx ++ " " ++ showFloat sy
        ++ " L " ++ showFloat tx ++ " " ++ showFloat ty
        where
          open import Data.String using (_≟_)
          open import Relation.Nullary using (yes; no)
          _≡ˢ_ : String → String → Bool
          s ≡ˢ t with s ≟ t
          ... | yes _ = true
          ... | no _ = false

------------------------------------------------------------------------
-- Flowchart
------------------------------------------------------------------------

-- | Full flowchart with nodes and edges
flowchart : ∀ {M A}
          → Float → Float → Float → Float  -- viewbox
          → List (FlowNode A)
          → List FlowEdge
          → Node M A
flowchart {M} {A} px py w h nodes edges =
  g ( attr "class" "svg-flowchart" ∷ [] )
    ( -- Edges first (behind nodes)
      g ( attr "class" "flowchart-edges" ∷ [] )
        (renderAllEdges nodes edges)
    -- Nodes
    ∷ g ( attr "class" "flowchart-nodes" ∷ [] )
        (renderAllNodes nodes)
    ∷ [] )
  where
    renderAllEdges : List (FlowNode A) → List FlowEdge → List (Node M A)
    renderAllEdges _ [] = []
    renderAllEdges ns (e ∷ es) = renderEdge ns e ∷ renderAllEdges ns es

    renderAllNodes : List (FlowNode A) → List (Node M A)
    renderAllNodes [] = []
    renderAllNodes (n ∷ ns) = renderNode n ∷ renderAllNodes ns

------------------------------------------------------------------------
-- Simple Flowchart (linear process)
------------------------------------------------------------------------

-- | Simple linear flowchart
simpleFlowchart : ∀ {M A}
                → Float → Float            -- start x, y
                → Float → Float            -- node width, height
                → Float                    -- vertical gap
                → List String              -- steps (labels)
                → Node M A
simpleFlowchart {M} {A} startX startY nodeW nodeH gap steps =
  flowchart startX startY 300.0 400.0 (toNodes steps 0) (toEdges steps 0)
  where
    open import Agda.Builtin.String using (primShowNat)
    showℕ : ℕ → String
    showℕ = primShowNat

    toNodes : List String → ℕ → List (FlowNode A)
    toNodes [] _ = []
    toNodes (lbl ∷ []) idx =
      mkFlowNode ("node" ++ showℕ idx) lbl Rounded
        startX (startY + fromℕ idx * (nodeH + gap)) nodeW nodeH "#e0f2fe" nothing
      ∷ []
    toNodes (lbl ∷ rest@(_ ∷ _)) idx =
      let shape = if idx ≡ᵇ 0 then Rounded else Rectangle
          color = if idx ≡ᵇ 0 then "#dcfce7" else "#e0f2fe"
      in mkFlowNode ("node" ++ showℕ idx) lbl shape
           startX (startY + fromℕ idx * (nodeH + gap)) nodeW nodeH color nothing
         ∷ toNodes rest (suc idx)
      where
        open import Data.Nat using (_≡ᵇ_)

    toEdges : List String → ℕ → List FlowEdge
    toEdges [] _ = []
    toEdges (_ ∷ []) _ = []
    toEdges (_ ∷ rest@(_ ∷ _)) idx =
      mkFlowEdge ("node" ++ showℕ idx) ("node" ++ showℕ (suc idx)) nothing "down"
      ∷ toEdges rest (suc idx)

------------------------------------------------------------------------
-- Decision Flowchart
------------------------------------------------------------------------

-- | Flowchart with decision point
decisionFlowchart : ∀ {M A}
                  → Float → Float
                  → String                 -- question
                  → String                 -- yes branch label
                  → String                 -- no branch label
                  → Node M A
decisionFlowchart {M} {A} cx cy question yesLabel noLabel =
  flowchart cx cy 400.0 300.0 nodes edges
  where
    nodes : List (FlowNode A)
    nodes = mkFlowNode "start" "Start" Rounded cx cy 100.0 40.0 "#dcfce7" nothing
          ∷ mkFlowNode "decision" question Diamond (cx - 10.0) (cy + 60.0) 120.0 80.0 "#fef3c7" nothing
          ∷ mkFlowNode "yes" yesLabel Rectangle (cx - 80.0) (cy + 180.0) 80.0 40.0 "#e0f2fe" nothing
          ∷ mkFlowNode "no" noLabel Rectangle (cx + 60.0) (cy + 180.0) 80.0 40.0 "#fee2e2" nothing
          ∷ []

    edges : List FlowEdge
    edges = mkFlowEdge "start" "decision" nothing "down"
          ∷ mkFlowEdge "decision" "yes" (just "Yes") "down"
          ∷ mkFlowEdge "decision" "no" (just "No") "right"
          ∷ []
