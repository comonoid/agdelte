{-# OPTIONS --without-K #-}

-- SVG Network Graph
-- Nodes and edges visualization

module Agdelte.Svg.Controls.Charts.Network where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; circle'; line'; svgText; path')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record GraphNode (A : Set) : Set where
  constructor mkGraphNode
  field
    nodeId      : String
    nodeLabel   : String
    nodeX       : Float
    nodeY       : Float
    nodeColor   : String
    nodeSize    : Float
    nodeOnClick : Maybe A

open GraphNode public

record GraphEdge : Set where
  constructor mkGraphEdge
  field
    edgeSource   : String
    edgeTarget   : String
    edgeLabel    : Maybe String
    edgeDirected : Bool
    edgeWeight   : Float      -- affects line thickness

open GraphEdge public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findNode : ∀ {A} → String → List (GraphNode A) → Maybe (GraphNode A)
  findNode _ [] = nothing
  findNode id' (n ∷ ns) =
    if nodeId n ≡ˢ id'
    then just n
    else findNode id' ns
    where
      open import Data.String using (_≟_)
      open import Relation.Nullary using (yes; no)
      _≡ˢ_ : String → String → Bool
      s ≡ˢ t with s ≟ t
      ... | yes _ = true
      ... | no _ = false

------------------------------------------------------------------------
-- Network Graph
------------------------------------------------------------------------

-- | Network graph with nodes and edges
networkGraph : ∀ {M A}
             → Float → Float → Float → Float  -- x, y, width, height
             → List (GraphNode A)
             → List GraphEdge
             → Node M A
networkGraph {M} {A} px py w h nodes edges =
  g ( attr "class" "svg-network-graph" ∷ [] )
    ( -- Edges first (behind nodes)
      g ( attr "class" "network-edges" ∷ [] )
        (renderEdges nodes edges)
    -- Nodes
    ∷ g ( attr "class" "network-nodes" ∷ [] )
        (renderNodes nodes)
    ∷ [] )
  where
    renderEdge : List (GraphNode A) → GraphEdge → Node M A
    renderEdge allNodes e =
      case (findNode (edgeSource e) allNodes , findNode (edgeTarget e) allNodes) of λ where
        (just src , just tgt) →
          g []
            ( line' ( x1F (px + nodeX src)
                    ∷ y1F (py + nodeY src)
                    ∷ x2F (px + nodeX tgt)
                    ∷ y2F (py + nodeY tgt)
                    ∷ stroke_ "#94a3b8"
                    ∷ strokeWidthF (edgeWeight e)
                    ∷ attr "class" "network-edge"
                    ∷ [] ) []
            -- Arrow marker if directed
            ∷ (if edgeDirected e
               then renderArrow (px + nodeX src) (py + nodeY src)
                                (px + nodeX tgt) (py + nodeY tgt)
               else g [] [])
            ∷ [] )
        _ → g [] []
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

        -- Simple arrow head
        renderArrow : Float → Float → Float → Float → Node M A
        renderArrow x1 y1 x2 y2 =
          let dx = x2 - x1
              dy = y2 - y1
              -- Simplified - just a small triangle at end
          in circle' ( cxF x2 ∷ cyF y2
                     ∷ rF 4.0
                     ∷ fill_ "#94a3b8"
                     ∷ [] ) []

    renderEdges : List (GraphNode A) → List GraphEdge → List (Node M A)
    renderEdges _ [] = []
    renderEdges allNodes (e ∷ es) =
      renderEdge allNodes e ∷ renderEdges allNodes es

    renderNode : GraphNode A → Node M A
    renderNode n =
      let nodeCircle = case nodeOnClick n of λ where
            nothing →
              circle' ( cxF 0.0 ∷ cyF 0.0
                      ∷ rF (nodeSize n)
                      ∷ fill_ (nodeColor n)
                      ∷ stroke_ "white"
                      ∷ strokeWidthF 2.0
                      ∷ attr "class" "network-node"
                      ∷ [] ) []
            (just msg) →
              circle' ( cxF 0.0 ∷ cyF 0.0
                      ∷ rF (nodeSize n)
                      ∷ fill_ (nodeColor n)
                      ∷ stroke_ "white"
                      ∷ strokeWidthF 2.0
                      ∷ attr "class" "network-node network-node--clickable"
                      ∷ attr "style" "cursor: pointer"
                      ∷ on "click" msg
                      ∷ [] ) []
      in g ( attr "transform" ("translate(" ++ showFloat (px + nodeX n) ++ ","
                              ++ showFloat (py + nodeY n) ++ ")") ∷ [] )
           ( nodeCircle
           -- Label
           ∷ svgText ( xF 0.0
                     ∷ yF (nodeSize n + 15.0)
                     ∷ attr "text-anchor" "middle"
                     ∷ attr "font-size" "11"
                     ∷ fill_ "#374151"
                     ∷ [] )
               ( text (nodeLabel n) ∷ [] )
           ∷ [] )
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

    renderNodes : List (GraphNode A) → List (Node M A)
    renderNodes [] = []
    renderNodes (n ∷ ns) = renderNode n ∷ renderNodes ns

------------------------------------------------------------------------
-- Simple constructors
------------------------------------------------------------------------

-- | Simple graph from node list and edge pairs
simpleGraph : ∀ {M A}
            → Float → Float → Float → Float
            → List (String × Float × Float)          -- (id, x, y)
            → List (String × String)                 -- (source, target)
            → Node M A
simpleGraph {M} {A} px py w h nodeSpecs edgeSpecs =
  networkGraph px py w h (toNodes nodeSpecs) (toEdges edgeSpecs)
  where
    toNodes : List (String × Float × Float) → List (GraphNode A)
    toNodes [] = []
    toNodes ((id' , nx , ny) ∷ rest) =
      mkGraphNode id' id' nx ny "#3b82f6" 20.0 nothing
      ∷ toNodes rest

    toEdges : List (String × String) → List GraphEdge
    toEdges [] = []
    toEdges ((src , tgt) ∷ rest) =
      mkGraphEdge src tgt nothing false 1.5
      ∷ toEdges rest

------------------------------------------------------------------------
-- Directed graph
------------------------------------------------------------------------

-- | Directed graph with arrows
directedGraph : ∀ {M A}
              → Float → Float → Float → Float
              → List (GraphNode A)
              → List GraphEdge
              → Node M A
directedGraph px py w h nodes edges =
  networkGraph px py w h nodes (markDirected edges)
  where
    markDirected : List GraphEdge → List GraphEdge
    markDirected [] = []
    markDirected (e ∷ es) =
      mkGraphEdge (edgeSource e) (edgeTarget e) (edgeLabel e) true (edgeWeight e)
      ∷ markDirected es
