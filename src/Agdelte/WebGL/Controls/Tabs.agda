{-# OPTIONS --without-K #-}

-- WebGL Controls Tabs
--
-- Tab bar and carousel components for navigation between panels.

module Agdelte.WebGL.Controls.Tabs where

open import Data.Nat using (ℕ; zero; suc; _≟_) renaming (_+_ to _ℕ+_)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Tab bar configuration
------------------------------------------------------------------------

record TabBarConfig : Set where
  constructor mkTabBarConfig
  field
    tabWidth   : Float
    tabHeight  : Float
    tabDepth   : Float
    spacing    : Float
    horizontal : Bool       -- true = horizontal, false = vertical

defaultTabBarConfig : TabBarConfig
defaultTabBarConfig = mkTabBarConfig 0.2 0.08 0.02 0.01 true

verticalTabBarConfig : TabBarConfig
verticalTabBarConfig = mkTabBarConfig 0.15 0.06 0.02 0.01 false

------------------------------------------------------------------------
-- Tab bar
------------------------------------------------------------------------

-- Tab bar with clickable tabs
tabBar3D : ∀ {M Msg}
         → ControlTheme
         → TabBarConfig
         → (M → ℕ)                   -- Active tab index
         → (ℕ → Msg)                 -- Select tab handler
         → List String               -- Tab labels
         → Transform
         → SceneNode M Msg
tabBar3D {M} {Msg} theme config getActive selectTab labels t =
  let tw = TabBarConfig.tabWidth config
      th = TabBarConfig.tabHeight config
      td = TabBarConfig.tabDepth config
      sp = TabBarConfig.spacing config
      horiz = TabBarConfig.horizontal config
  in group t (buildTabs theme tw th td sp horiz getActive selectTab 0 labels)
  where
    postulate natToFloat : ℕ → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}

    natEq : ℕ → ℕ → Bool
    natEq m n with m ≟ n
    ... | yes _ = true
    ... | no _ = false

    buildTabs : ControlTheme → Float → Float → Float → Float → Bool
              → (M → ℕ) → (ℕ → Msg) → ℕ → List String
              → List (SceneNode M Msg)
    buildTabs _ _ _ _ _ _ _ _ _ [] = []
    buildTabs th tw tht td sp horiz getAct select idx (lbl ∷ rest) =
      let offset = natToFloat idx * (tw + sp)
          pos = if horiz
            then vec3 offset 0.0 0.0
            else vec3 0.0 (- offset) 0.0
          tabT = mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
          -- Active tab styling
          isActive = λ m → natEq (getAct m) idx
          activeMat = phong (ControlTheme.primaryColor th) 48.0
          inactiveMat = ControlTheme.surfaceMaterial th
          getTabMat = λ m → if isActive m then activeMat else inactiveMat
          -- Active tab is slightly elevated
          activeZ = td * 0.3
          getTabZ = λ m →
            if isActive m
              then mkTransform (vec3 0.0 0.0 activeZ) identityQuat (vec3 1.0 1.0 1.0)
              else identityTransform
          tabGeom = roundedBox (vec3 tw tht td) (tht * 0.2) 4
          textT = mkTransform (vec3 0.0 0.0 (td * 0.5 + 0.001)) identityQuat (vec3 1.0 1.0 1.0)
      in bindTransform getTabZ
           (interactiveGroup
             (onClick (select idx) ∷ transition (ms 150) easeOut ∷ [])
             tabT
             ( bindMaterial getTabMat tabGeom [] identityTransform
             ∷ sizedLabel th 0.05 lbl textT
             ∷ []))
         ∷ buildTabs th tw tht td sp horiz getAct select (suc idx) rest

-- Simple horizontal tab bar
tabBar : ∀ {M Msg}
       → ControlTheme
       → (M → ℕ)
       → (ℕ → Msg)
       → List String
       → Transform
       → SceneNode M Msg
tabBar theme = tabBar3D theme defaultTabBarConfig

-- Vertical tab bar (sidebar style)
verticalTabBar : ∀ {M Msg}
               → ControlTheme
               → (M → ℕ)
               → (ℕ → Msg)
               → List String
               → Transform
               → SceneNode M Msg
verticalTabBar theme = tabBar3D theme verticalTabBarConfig

------------------------------------------------------------------------
-- Tab panel (content area that shows active content)
------------------------------------------------------------------------

-- Tab panel that renders only the active content
-- Takes a list of (label, content) pairs
tabPanel : ∀ {M Msg}
         → ControlTheme
         → (M → ℕ)                             -- Active index
         → (ℕ → Msg)                           -- Select handler
         → List (String × SceneNode M Msg)      -- (label, content) pairs
         → Transform
         → SceneNode M Msg
tabPanel {M} {Msg} theme getActive selectTab panels t =
  let labels = extractLabels panels
      tabBarT = mkTransform (vec3 0.0 0.3 0.0) identityQuat (vec3 1.0 1.0 1.0)
      contentT = mkTransform (vec3 0.0 -0.1 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( tabBar theme getActive selectTab labels tabBarT
       ∷ renderActiveContent getActive 0 panels contentT
       ∷ [])
  where
    extractLabels : List (String × SceneNode M Msg) → List String
    extractLabels [] = []
    extractLabels ((lbl , _) ∷ rest) = lbl ∷ extractLabels rest

    natEq : ℕ → ℕ → Bool
    natEq m n with m ≟ n
    ... | yes _ = true
    ... | no _ = false

    -- Only render active content (scale others to 0)
    renderActiveContent : (M → ℕ) → ℕ → List (String × SceneNode M Msg)
                        → Transform → SceneNode M Msg
    renderActiveContent _ _ [] contentT =
      group contentT []
    renderActiveContent getAct idx ((lbl , content) ∷ rest) contentT =
      let isActive = λ m → natEq (getAct m) idx
          getScale = λ m →
            if isActive m
              then mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
              else mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 0.0 0.0 0.0)
      in group contentT
           ( bindTransform getScale content
           ∷ renderRest getAct (suc idx) rest
           ∷ [])
      where
        renderRest : (M → ℕ) → ℕ → List (String × SceneNode M Msg) → SceneNode M Msg
        renderRest _ _ [] = group identityTransform []
        renderRest gA i ((l , c) ∷ rs) =
          let isAct = λ m → natEq (gA m) i
              getS = λ m →
                if isAct m
                  then mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
                  else mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 0.0 0.0 0.0)
          in group identityTransform
               ( bindTransform getS c
               ∷ renderRest gA (suc i) rs
               ∷ [])

------------------------------------------------------------------------
-- Segmented control (iOS style)
------------------------------------------------------------------------

segmentedControl : ∀ {M Msg}
                 → ControlTheme
                 → (M → ℕ)
                 → (ℕ → Msg)
                 → List String
                 → Transform
                 → SceneNode M Msg
segmentedControl {M} {Msg} theme getSelected selectHandler options t =
  let n = length options
      totalWidth = 0.4
      segWidth = totalWidth * recip (natToFloat n)
      segHeight = 0.08
      -- Background
      bgGeom = roundedBox (vec3 totalWidth segHeight 0.015) 0.02 4
      bgMat = phong (ControlTheme.backgroundColor theme) 24.0
  in group t
       ( mesh bgGeom bgMat [] identityTransform
       ∷ buildSegments theme segWidth segHeight getSelected selectHandler 0 options )
  where
    postulate natToFloat : ℕ → Float
    postulate recip : Float → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}
    {-# COMPILE JS recip = x => 1 / x #-}

    natEq : ℕ → ℕ → Bool
    natEq m n with m ≟ n
    ... | yes _ = true
    ... | no _ = false

    totalWidth = 0.4

    buildSegments : ControlTheme → Float → Float → (M → ℕ) → (ℕ → Msg) → ℕ
                  → List String → List (SceneNode M Msg)
    buildSegments _ _ _ _ _ _ [] = []
    buildSegments th sw sh getSel sel idx (lbl ∷ rest) =
      let n = length (lbl ∷ rest) ℕ+ idx
          x = (natToFloat idx - (natToFloat n - 1.0) * 0.5) * sw
          segT = mkTransform (vec3 x 0.0 0.01) identityQuat (vec3 1.0 1.0 1.0)
          isSelected = λ m → natEq (getSel m) idx
          selectedMat = phong (ControlTheme.primaryColor th) 48.0
          normalMat = phong (ControlTheme.backgroundColor th) 24.0
          getSegMat = λ m → if isSelected m then selectedMat else normalMat
          segGeom = roundedBox (vec3 (sw * 0.95) (sh * 0.85) 0.01) 0.015 4
          textT = mkTransform (vec3 0.0 0.0 0.008) identityQuat (vec3 1.0 1.0 1.0)
      in interactiveGroup
           (onClick (sel idx) ∷ transition (ms 100) easeOut ∷ [])
           segT
           ( bindMaterial getSegMat segGeom [] identityTransform
           ∷ sizedLabel th 0.04 lbl textT
           ∷ [])
         ∷ buildSegments th sw sh getSel sel (suc idx) rest

------------------------------------------------------------------------
-- Pagination dots
------------------------------------------------------------------------

paginationDots : ∀ {M Msg}
               → ControlTheme
               → ℕ                    -- Total count
               → (M → ℕ)              -- Current index
               → (ℕ → Msg)            -- Select handler
               → Transform
               → SceneNode M Msg
paginationDots {M} {Msg} theme total getCurrent selectHandler t =
  let spacing = 0.04
      dotR = 0.012
  in group t (buildDots theme spacing dotR getCurrent selectHandler 0 total)
  where
    postulate natToFloat : ℕ → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}

    natEq : ℕ → ℕ → Bool
    natEq m n with m ≟ n
    ... | yes _ = true
    ... | no _ = false

    buildDots : ControlTheme → Float → Float → (M → ℕ) → (ℕ → Msg) → ℕ → ℕ
              → List (SceneNode M Msg)
    buildDots _ _ _ _ _ _ zero = []
    buildDots th sp r getCur sel idx (suc remaining) =
      let x = (natToFloat idx - natToFloat (idx ℕ+ remaining) * 0.5) * sp
          dotT = mkTransform (vec3 x 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
          isCurrent = λ m → natEq (getCur m) idx
          currentMat = phong (ControlTheme.primaryColor th) 64.0
          otherMat = phong (ControlTheme.disabledColor th) 32.0
          getDotMat = λ m → if isCurrent m then currentMat else otherMat
          dotGeom = sphere r
      in interactiveGroup
           (onClick (sel idx) ∷ [])
           dotT
           (bindMaterial getDotMat dotGeom [] identityTransform ∷ [])
         ∷ buildDots th sp r getCur sel (suc idx) remaining
