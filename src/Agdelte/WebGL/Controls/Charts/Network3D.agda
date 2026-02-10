{-# OPTIONS --without-K #-}

-- WebGL Controls Charts Network3D
--
-- 3D network/graph visualization.
-- Shows nodes as spheres and edges as connections.

module Agdelte.WebGL.Controls.Charts.Network3D where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String; _==_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float
  sqrtF : Float → Float
  stringEq : String → String → Bool

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS sqrtF = x => Math.sqrt(x) #-}
{-# COMPILE JS stringEq = a => b => a === b #-}

------------------------------------------------------------------------
-- Module-level helpers
------------------------------------------------------------------------

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

infixr 5 _++L_
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Network data types
------------------------------------------------------------------------

record NodeData : Set where
  constructor mkNodeData
  field
    nodeId       : String
    nodePosition : Vec3
    nodeSize     : Float
    nodeColor    : GlColor
    nodeLabel    : Maybe String

simpleNode : String → Vec3 → GlColor → NodeData
simpleNode id pos c = mkNodeData id pos 0.03 c nothing

labeledNode : String → Vec3 → GlColor → String → NodeData
labeledNode id pos c lbl = mkNodeData id pos 0.03 c (just lbl)

record EdgeData : Set where
  constructor mkEdgeData
  field
    edgeFrom   : String
    edgeTo     : String
    edgeWeight : Float
    edgeColor  : Maybe GlColor

simpleEdge : String → String → EdgeData
simpleEdge from to = mkEdgeData from to 1.0 nothing

weightedEdge : String → String → Float → EdgeData
weightedEdge from to w = mkEdgeData from to w nothing

coloredEdge : String → String → GlColor → EdgeData
coloredEdge from to c = mkEdgeData from to 1.0 (just c)

------------------------------------------------------------------------
-- Network configuration
------------------------------------------------------------------------

record NetworkConfig : Set where
  constructor mkNetworkConfig
  field
    defaultNodeSize  : Float
    defaultEdgeWidth : Float
    defaultNodeColor : GlColor
    defaultEdgeColor : GlColor
    showLabels       : Bool
    labelSize        : Float

defaultNetworkConfig : NetworkConfig
defaultNetworkConfig = mkNetworkConfig
  0.03                            -- defaultNodeSize
  0.005                           -- defaultEdgeWidth
  (rgba 0.3 0.6 0.9 1.0)         -- defaultNodeColor
  (rgba 0.5 0.5 0.5 0.8)         -- defaultEdgeColor
  true                            -- showLabels
  0.02                            -- labelSize

------------------------------------------------------------------------
-- Network graph implementation
------------------------------------------------------------------------

-- 3D network graph
networkGraph3D : ∀ {M Msg}
               → ControlTheme
               → NetworkConfig
               → (M → List NodeData)         -- Nodes accessor
               → (M → List EdgeData)         -- Edges accessor
               → Maybe (String → Msg)        -- Optional node click handler
               → Transform
               → SceneNode M Msg
networkGraph3D {M} {Msg} theme config getNodes getEdges clickHandler t =
  group t
    ( bindChildren buildEdges identityTransform
    ∷ bindChildren buildNodes identityTransform
    ∷ [])
  where
    defNodeSize = NetworkConfig.defaultNodeSize config
    defEdgeWidth = NetworkConfig.defaultEdgeWidth config
    defNodeColor = NetworkConfig.defaultNodeColor config
    defEdgeColor = NetworkConfig.defaultEdgeColor config
    showLbls = NetworkConfig.showLabels config
    lblSize = NetworkConfig.labelSize config

    -- Find node position by ID
    findNodePos : String → List NodeData → Maybe Vec3
    findNodePos _ [] = nothing
    findNodePos id (n ∷ ns) =
      if stringEq id (NodeData.nodeId n)
        then just (NodeData.nodePosition n)
        else findNodePos id ns

    -- Build node spheres
    buildNodes : M → List (SceneNode M Msg)
    buildNodes m = buildNodeList (getNodes m)
      where
        buildNodeList : List NodeData → List (SceneNode M Msg)
        buildNodeList [] = []
        buildNodeList (n ∷ ns) =
          let id = NodeData.nodeId n
              pos = NodeData.nodePosition n
              sz = NodeData.nodeSize n
              c = NodeData.nodeColor n
              lbl = NodeData.nodeLabel n
              nodeT = mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
              nodeGeom = sphere sz
              nodeMat = phong c 64.0
              attrs = case clickHandler of λ where
                nothing → []
                (just handler) → onClick (handler id) ∷ []
              -- Build node with optional label
              nodeWithLabel = case lbl of λ where
                nothing →
                  interactiveGroup attrs nodeT
                    (mesh nodeGeom nodeMat [] identityTransform ∷ [])
                (just l) →
                  let labelT = mkTransform (vec3 0.0 (sz + 0.02) 0.0) identityQuat (vec3 1.0 1.0 1.0)
                  in interactiveGroup attrs nodeT
                       ( mesh nodeGeom nodeMat [] identityTransform
                       ∷ (if showLbls then sizedLabel theme lblSize l labelT ∷ [] else []))
          in nodeWithLabel ∷ buildNodeList ns

    -- Build edge cylinders
    buildEdges : M → List (SceneNode M Msg)
    buildEdges m =
      let nodes = getNodes m
          edges = getEdges m
      in buildEdgeList nodes edges
      where
        buildEdgeList : List NodeData → List EdgeData → List (SceneNode M Msg)
        buildEdgeList _ [] = []
        buildEdgeList nodes (e ∷ es) =
          let fromId = EdgeData.edgeFrom e
              toId = EdgeData.edgeTo e
              weight = EdgeData.edgeWeight e
              edgeC = case EdgeData.edgeColor e of λ where
                nothing → defEdgeColor
                (just c) → c
              -- Find node positions
              maybeEdge = case findNodePos fromId nodes of λ where
                nothing → nothing
                (just fromPos) → case findNodePos toId nodes of λ where
                  nothing → nothing
                  (just toPos) → just (fromPos , toPos)
              edgeNode = case maybeEdge of λ where
                nothing → []
                (just (fromPos , toPos)) →
                  let -- Calculate midpoint
                      mx = (vec3X fromPos + vec3X toPos) * 0.5
                      my = (vec3Y fromPos + vec3Y toPos) * 0.5
                      mz = (vec3Z fromPos + vec3Z toPos) * 0.5
                      -- Calculate distance
                      dx = vec3X toPos - vec3X fromPos
                      dy = vec3Y toPos - vec3Y fromPos
                      dz = vec3Z toPos - vec3Z fromPos
                      dist = sqrtF (dx * dx + dy * dy + dz * dz)
                      -- Edge geometry
                      edgeWidth = defEdgeWidth * weight
                      edgeGeom = cylinder edgeWidth dist
                      edgeMat = phong edgeC 32.0
                      -- Orientation (simplified - point toward toPos)
                      edgeT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
                  in mesh edgeGeom edgeMat [] edgeT ∷ []
          in edgeNode ++L buildEdgeList nodes es

-- Simple network graph
networkGraph : ∀ {M Msg}
             → ControlTheme
             → (M → List NodeData)
             → (M → List EdgeData)
             → Transform
             → SceneNode M Msg
networkGraph theme getNodes getEdges =
  networkGraph3D theme defaultNetworkConfig getNodes getEdges nothing

------------------------------------------------------------------------
-- Force-directed graph (layout computed dynamically)
------------------------------------------------------------------------

record ForceConfig : Set where
  constructor mkForceConfig
  field
    repulsion   : Float          -- Node repulsion strength
    attraction  : Float          -- Edge attraction strength
    damping     : Float          -- Velocity damping
    centerForce : Float          -- Force toward center

defaultForceConfig : ForceConfig
defaultForceConfig = mkForceConfig
  0.1                             -- repulsion
  0.05                            -- attraction
  0.9                             -- damping
  0.01                            -- centerForce

-- Force-directed graph (positions stored in model)
forceGraph3D : ∀ {M Msg}
             → ControlTheme
             → NetworkConfig
             → ForceConfig
             → (M → List (String × GlColor))    -- Node IDs and colors
             → (M → List (String × String))   -- Edges as (from, to) pairs
             → (M → List Vec3)                -- Current positions
             → (List Vec3 → Msg)              -- Update positions
             → Maybe (String → Msg)           -- Click handler
             → Transform
             → SceneNode M Msg
forceGraph3D {M} {Msg} theme netConfig forceConfig getNodeDefs getEdgeDefs getPositions updatePositions clickHandler t =
  bindChildren buildGraph t
  where
    buildGraph : M → List (SceneNode M Msg)
    buildGraph m =
      let nodeDefs = getNodeDefs m
          edgeDefs = getEdgeDefs m
          positions = getPositions m
          nodes = zipWithPos nodeDefs positions 0
          edges = buildEdgeDefs edgeDefs
      in buildNodeList nodes ++L buildEdgeList nodes edges
      where
        zipWithPos : List (String × GlColor) → List Vec3 → ℕ → List NodeData
        zipWithPos [] _ _ = []
        zipWithPos _ [] _ = []
        zipWithPos ((id , c) ∷ defs) (pos ∷ poss) idx =
          mkNodeData id pos (NetworkConfig.defaultNodeSize netConfig) c (just id)
          ∷ zipWithPos defs poss (suc idx)

        buildEdgeDefs : List (String × String) → List EdgeData
        buildEdgeDefs [] = []
        buildEdgeDefs ((from , to) ∷ es) = simpleEdge from to ∷ buildEdgeDefs es

        -- Reuse node/edge rendering from networkGraph
        buildNodeList : List NodeData → List (SceneNode M Msg)
        buildNodeList [] = []
        buildNodeList (n ∷ ns) =
          let pos = NodeData.nodePosition n
              sz = NodeData.nodeSize n
              c = NodeData.nodeColor n
              nodeT = mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
              nodeGeom = sphere sz
              nodeMat = phong c 64.0
          in mesh nodeGeom nodeMat [] nodeT ∷ buildNodeList ns

        buildEdgeList : List NodeData → List EdgeData → List (SceneNode M Msg)
        buildEdgeList _ [] = []
        buildEdgeList nodes (e ∷ es) =
          let fromId = EdgeData.edgeFrom e
              toId = EdgeData.edgeTo e
          in case findPos fromId nodes of λ where
               nothing → buildEdgeList nodes es
               (just fromPos) → case findPos toId nodes of λ where
                 nothing → buildEdgeList nodes es
                 (just toPos) →
                   let mx = (vec3X fromPos + vec3X toPos) * 0.5
                       my = (vec3Y fromPos + vec3Y toPos) * 0.5
                       mz = (vec3Z fromPos + vec3Z toPos) * 0.5
                       dx = vec3X toPos - vec3X fromPos
                       dy = vec3Y toPos - vec3Y fromPos
                       dz = vec3Z toPos - vec3Z fromPos
                       dist = sqrtF (dx * dx + dy * dy + dz * dz)
                       edgeGeom = cylinder (NetworkConfig.defaultEdgeWidth netConfig) dist
                       edgeMat = phong (NetworkConfig.defaultEdgeColor netConfig) 32.0
                       edgeT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
                   in mesh edgeGeom edgeMat [] edgeT ∷ buildEdgeList nodes es
          where
            findPos : String → List NodeData → Maybe Vec3
            findPos _ [] = nothing
            findPos id (n ∷ ns) =
              if stringEq id (NodeData.nodeId n)
                then just (NodeData.nodePosition n)
                else findPos id ns

