{-# OPTIONS --without-K #-}

-- SVG Org Chart
-- Hierarchical organization/tree structure

module Agdelte.Svg.Controls.Charts.OrgChart where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; path'; circle'; svgText; line')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record OrgNode (A : Set) : Set where
  inductive
  constructor mkOrgNode
  field
    orgId       : String
    orgLabel    : String
    orgSublabel : Maybe String      -- e.g., job title
    orgAvatar   : Maybe String      -- image URL or initials
    orgColor    : String
    orgChildren : List (OrgNode A)
    orgOnClick  : Maybe A

open OrgNode public

record OrgConfig : Set where
  constructor mkOrgConfig
  field
    ocNodeWidth   : Float
    ocNodeHeight  : Float
    ocHGap        : Float           -- horizontal gap between siblings
    ocVGap        : Float           -- vertical gap between levels
    ocShowLines   : Bool
    ocCardStyle   : Bool            -- card vs simple box

open OrgConfig public

defaultOrgConfig : OrgConfig
defaultOrgConfig = mkOrgConfig 120.0 60.0 30.0 50.0 true true

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  listLen : ∀ {A : Set} → List A → ℕ
  listLen [] = 0
  listLen (_ ∷ xs) = suc (listLen xs)

  -- Calculate subtree width
  subtreeWidth : ∀ {A} → OrgConfig → OrgNode A → Float
  subtreeWidth cfg node =
    let childCount = listLen (orgChildren node)
    in if childCount ≡ᵇ 0
       then ocNodeWidth cfg
       else sumChildWidths cfg (orgChildren node) + fromℕ (childCount ∸ 1) * ocHGap cfg
    where
      open import Data.Nat using (_≡ᵇ_; _∸_)

      sumChildWidths : ∀ {A} → OrgConfig → List (OrgNode A) → Float
      sumChildWidths _ [] = 0.0
      sumChildWidths cfg' (c ∷ cs) = subtreeWidth cfg' c + sumChildWidths cfg' cs

------------------------------------------------------------------------
-- Node Rendering
------------------------------------------------------------------------

private
  renderOrgNode : ∀ {M A} → OrgConfig → Float → Float → OrgNode A → Node M A
  renderOrgNode cfg nx ny node =
    let w = ocNodeWidth cfg
        h = ocNodeHeight cfg
    in case orgOnClick node of λ where
         nothing →
           g ( attr "class" "orgchart-node" ∷ [] )
             ( -- Card background
               rect' ( xF nx ∷ yF ny
                     ∷ widthF w ∷ heightF h
                     ∷ fill_ "white"
                     ∷ stroke_ (orgColor node)
                     ∷ strokeWidthF 2.0
                     ∷ attr "rx" "6"
                     ∷ [] ) []
             -- Color bar at top
             ∷ rect' ( xF nx ∷ yF ny
                     ∷ widthF w ∷ heightF 4.0
                     ∷ fill_ (orgColor node)
                     ∷ attr "rx" "6"
                     ∷ [] ) []
             -- Avatar or initials
             ∷ (case orgAvatar node of λ where
                  nothing →
                    circle' ( cxF (nx + 20.0) ∷ cyF (ny + h ÷ 2.0 + 2.0)
                            ∷ rF 12.0
                            ∷ fill_ (orgColor node)
                            ∷ [] ) []
                  (just _) →
                    circle' ( cxF (nx + 20.0) ∷ cyF (ny + h ÷ 2.0 + 2.0)
                            ∷ rF 12.0
                            ∷ fill_ "#e5e7eb"
                            ∷ [] ) [])
             -- Main label
             ∷ svgText ( xF (nx + 38.0) ∷ yF (ny + h ÷ 2.0)
                       ∷ attr "font-size" "11"
                       ∷ attr "font-weight" "bold"
                       ∷ fill_ "#1e293b"
                       ∷ [] )
                 ( text (orgLabel node) ∷ [] )
             -- Sublabel
             ∷ (case orgSublabel node of λ where
                  nothing → g [] []
                  (just sub) →
                    svgText ( xF (nx + 38.0) ∷ yF (ny + h ÷ 2.0 + 12.0)
                            ∷ attr "font-size" "9"
                            ∷ fill_ "#64748b"
                            ∷ [] )
                      ( text sub ∷ [] ))
             ∷ [] )
         (just msg) →
           g ( attr "class" "orgchart-node orgchart-node--clickable"
             ∷ attr "style" "cursor: pointer"
             ∷ on "click" msg
             ∷ [] )
             ( rect' ( xF nx ∷ yF ny
                     ∷ widthF w ∷ heightF h
                     ∷ fill_ "white"
                     ∷ stroke_ (orgColor node)
                     ∷ strokeWidthF 2.0
                     ∷ attr "rx" "6"
                     ∷ [] ) []
             ∷ rect' ( xF nx ∷ yF ny
                     ∷ widthF w ∷ heightF 4.0
                     ∷ fill_ (orgColor node)
                     ∷ attr "rx" "6"
                     ∷ [] ) []
             ∷ svgText ( xF (nx + w ÷ 2.0) ∷ yF (ny + h ÷ 2.0)
                       ∷ attr "text-anchor" "middle"
                       ∷ attr "dominant-baseline" "middle"
                       ∷ attr "font-size" "11"
                       ∷ attr "font-weight" "bold"
                       ∷ fill_ "#1e293b"
                       ∷ [] )
                 ( text (orgLabel node) ∷ [] )
             ∷ (case orgSublabel node of λ where
                  nothing → g [] []
                  (just sub) →
                    svgText ( xF (nx + w ÷ 2.0) ∷ yF (ny + h ÷ 2.0 + 14.0)
                            ∷ attr "text-anchor" "middle"
                            ∷ attr "font-size" "9"
                            ∷ fill_ "#64748b"
                            ∷ [] )
                      ( text sub ∷ [] ))
             ∷ [] )
    where
      case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
      case x of f = f x

------------------------------------------------------------------------
-- Connection Lines
------------------------------------------------------------------------

private
  renderConnector : ∀ {M A} → Float → Float → Float → Float → Float → Node M A
  renderConnector parentX parentY parentH childX childY =
    let midY = parentY + parentH + (childY - parentY - parentH) ÷ 2.0
    in path' ( d_ ( "M " ++ showFloat parentX ++ " " ++ showFloat (parentY + parentH)
                  ++ " L " ++ showFloat parentX ++ " " ++ showFloat midY
                  ++ " L " ++ showFloat childX ++ " " ++ showFloat midY
                  ++ " L " ++ showFloat childX ++ " " ++ showFloat childY )
             ∷ fill_ "none"
             ∷ stroke_ "#94a3b8"
             ∷ strokeWidthF 1.5
             ∷ [] ) []

------------------------------------------------------------------------
-- Tree Layout
------------------------------------------------------------------------

private
  layoutTree : ∀ {M A}
             → OrgConfig
             → Float → Float              -- center X, Y for this node
             → OrgNode A
             → List (Node M A)
  layoutTree cfg cx cy node =
    let w = ocNodeWidth cfg
        h = ocNodeHeight cfg
        nodeX = cx - w ÷ 2.0
        childY = cy + h + ocVGap cfg
        children = orgChildren node
        childCount = listLen children
        totalChildWidth = getTotalChildWidth cfg children
        startX = cx - totalChildWidth ÷ 2.0
    in renderOrgNode cfg nodeX cy node
       ∷ layoutChildren cfg cx cy h startX childY children
    where
      getTotalChildWidth : ∀ {A} → OrgConfig → List (OrgNode A) → Float
      getTotalChildWidth _ [] = 0.0
      getTotalChildWidth cfg' (c ∷ []) = subtreeWidth cfg' c
      getTotalChildWidth cfg' (c ∷ cs) =
        subtreeWidth cfg' c + ocHGap cfg' + getTotalChildWidth cfg' cs

      layoutChildren : ∀ {M A} → OrgConfig → Float → Float → Float → Float → Float → List (OrgNode A) → List (Node M A)
      layoutChildren _ _ _ _ _ _ [] = []
      layoutChildren cfg' parentCx parentY parentH startX' childY' (c ∷ cs) =
        let childW = subtreeWidth cfg' c
            childCx = startX' + childW ÷ 2.0
            connector = if ocShowLines cfg'
                        then renderConnector parentCx parentY parentH childCx childY'
                        else g [] []
        in connector
           ∷ layoutTree cfg' childCx childY' c
           ++ᴸ layoutChildren cfg' parentCx parentY parentH (startX' + childW + ocHGap cfg') childY' cs
        where
          open import Data.List renaming (_++_ to _++ᴸ_)

------------------------------------------------------------------------
-- Org Chart
------------------------------------------------------------------------

-- | Full org chart from root node
orgChart : ∀ {M A}
         → Float → Float              -- root center position
         → OrgConfig
         → OrgNode A
         → Node M A
orgChart {M} {A} cx cy cfg root =
  g ( attr "class" "svg-orgchart" ∷ [] )
    (layoutTree cfg cx cy root)

------------------------------------------------------------------------
-- Simple Org Chart
------------------------------------------------------------------------

-- | Simple org chart from hierarchy data
simpleOrgChart : ∀ {M A}
               → Float → Float
               → OrgNode A
               → Node M A
simpleOrgChart cx cy root =
  orgChart cx cy defaultOrgConfig root

------------------------------------------------------------------------
-- Flat Org Chart (single level)
------------------------------------------------------------------------

-- | Single-level org chart (boss + direct reports)
flatOrgChart : ∀ {M A}
             → Float → Float
             → String                    -- boss name
             → String                    -- boss title
             → List (String × String)    -- (name, title) pairs
             → Node M A
flatOrgChart {M} {A} cx cy bossName bossTitle reports =
  orgChart cx cy defaultOrgConfig root
  where
    open import Data.Nat.Show using (show)
    showℕ : ℕ → String
    showℕ = show

    toChildren : List (String × String) → ℕ → List (OrgNode A)
    toChildren [] _ = []
    toChildren ((n , t) ∷ rest) idx =
      mkOrgNode ("emp" ++ showℕ idx) n (just t) nothing "#22c55e" [] nothing
      ∷ toChildren rest (suc idx)

    root : OrgNode A
    root = mkOrgNode "boss" bossName (just bossTitle) nothing "#3b82f6"
           (toChildren reports 0) nothing

------------------------------------------------------------------------
-- Compact Org Chart
------------------------------------------------------------------------

-- | Compact style org chart (smaller nodes)
compactOrgChart : ∀ {M A}
                → Float → Float
                → OrgNode A
                → Node M A
compactOrgChart cx cy root =
  orgChart cx cy compactConfig root
  where
    compactConfig : OrgConfig
    compactConfig = mkOrgConfig 80.0 40.0 20.0 30.0 true false

------------------------------------------------------------------------
-- Department Org Chart
------------------------------------------------------------------------

-- | Multi-department org chart
departmentOrgChart : ∀ {M A}
                   → Float → Float
                   → String                              -- CEO name
                   → List (String × String × List (String × String))  -- (dept head, title, [(name, title)])
                   → Node M A
departmentOrgChart {M} {A} cx cy ceoName departments =
  orgChart cx cy defaultOrgConfig root
  where
    open import Data.Nat.Show using (show)
    showℕ : ℕ → String
    showℕ = show

    deptColors : List String
    deptColors = "#3b82f6" ∷ "#22c55e" ∷ "#f59e0b" ∷ "#ef4444" ∷ "#8b5cf6" ∷ []

    getColor : ℕ → String
    getColor n = go deptColors n
      where
        go : List String → ℕ → String
        go [] _ = "#3b82f6"
        go (c ∷ _) zero = c
        go (_ ∷ cs) (suc m) = go cs m

    buildMembers : List (String × String) → String → ℕ → List (OrgNode A)
    buildMembers [] _ _ = []
    buildMembers ((n , t) ∷ rest) color idx =
      mkOrgNode ("mem" ++ showℕ idx) n (just t) nothing color [] nothing
      ∷ buildMembers rest color (suc idx)

    buildDept : (String × String × List (String × String)) → ℕ → OrgNode A
    buildDept (head' , title , members) idx =
      let color = getColor idx
      in mkOrgNode ("dept" ++ showℕ idx) head' (just title) nothing color
           (buildMembers members color 0) nothing

    buildDepts : List (String × String × List (String × String)) → ℕ → List (OrgNode A)
    buildDepts [] _ = []
    buildDepts (d ∷ ds) idx = buildDept d idx ∷ buildDepts ds (suc idx)

    root : OrgNode A
    root = mkOrgNode "ceo" ceoName (just "CEO") nothing "#1e293b"
           (buildDepts departments 0) nothing
