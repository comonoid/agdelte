{-# OPTIONS --without-K #-}

-- WebGL Controls Menus
--
-- Menu components: dropdown menus, context menus, and radial menus.
-- Provide selection from multiple options in 3D space.

module Agdelte.WebGL.Controls.Menus where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Buttons
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Menu item
------------------------------------------------------------------------

record MenuItem (Msg : Set) : Set where
  constructor menuItem
  field
    itemLabel   : String
    itemAction  : Msg
    itemEnabled : Bool

enabledItem : ∀ {Msg} → String → Msg → MenuItem Msg
enabledItem lbl action = menuItem lbl action true

disabledItem : ∀ {Msg} → String → MenuItem Msg
disabledItem lbl = menuItem lbl undefined false
  where
    postulate undefined : ∀ {A : Set} → A
    {-# COMPILE JS undefined = undefined #-}

------------------------------------------------------------------------
-- Dropdown menu
------------------------------------------------------------------------

record DropdownConfig : Set where
  constructor mkDropdownConfig
  field
    buttonWidth  : Float
    buttonHeight : Float
    itemHeight   : Float
    itemWidth    : Float

defaultDropdownConfig : DropdownConfig
defaultDropdownConfig = mkDropdownConfig 0.35 0.1 0.08 0.35

-- Dropdown button + expandable menu
dropdown3D : ∀ {M Msg}
           → ControlTheme
           → DropdownConfig
           → String                  -- Button label
           → (M → Bool)              -- Is open?
           → Msg                     -- Toggle open
           → List (MenuItem Msg)     -- Menu items
           → Transform
           → SceneNode M Msg
dropdown3D {M} {Msg} theme config btnLabel isOpen toggleOpen items t =
  let bw = DropdownConfig.buttonWidth config
      bh = DropdownConfig.buttonHeight config
      ih = DropdownConfig.itemHeight config
      iw = DropdownConfig.itemWidth config
      bd = 0.03
      -- Main button
      btnConfig = mkButtonConfig bw bh bd 0.02
      -- Menu panel (visible when open)
      menuItems = buildMenuItems theme ih iw 0 items
      menuHeight = natToFloat (length items) * ih
      -- Menu visibility
      getMenuScale = λ m →
        if isOpen m
          then mkTransform (vec3 0.0 (- (bh * 0.5 + menuHeight * 0.5)) 0.05)
                 identityQuat (vec3 1.0 1.0 1.0)
          else mkTransform (vec3 0.0 (- (bh * 0.5)) 0.05)
                 identityQuat (vec3 1.0 0.0 1.0)  -- Scale Y to 0 hides
  in group t
       ( button3D theme btnConfig btnLabel toggleOpen identityTransform
       ∷ bindTransform getMenuScale
           (group identityTransform
             ( menuBackground theme iw menuHeight
             ∷ menuItems ))
       ∷ [])
  where
    postulate natToFloat : ℕ → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}

    menuBackground : ControlTheme → Float → Float → SceneNode M Msg
    menuBackground th w h =
      mesh (roundedBox (vec3 w h 0.02) 0.01 4)
           (phong (ControlTheme.backgroundColor th) 24.0)
           []
           identityTransform

    buildMenuItems : ControlTheme → Float → Float → ℕ → List (MenuItem Msg) → List (SceneNode M Msg)
    buildMenuItems _ _ _ _ [] = []
    buildMenuItems th ih iw idx (menuItem lbl action enabled ∷ rest) =
      let y = - (natToFloat idx * ih)
          itemT = mkTransform (vec3 0.0 y 0.01) identityQuat (vec3 1.0 1.0 1.0)
          itemGeom = roundedBox (vec3 (iw * 0.95) (ih * 0.85) 0.015) 0.01 4
          itemMat = if enabled
            then ControlTheme.surfaceMaterial th
            else disabledMaterial th
          textT = mkTransform (vec3 0.0 0.0 0.01) identityQuat (vec3 1.0 1.0 1.0)
          attrs = if enabled then onClick action ∷ [] else []
      in interactiveGroup attrs itemT
           ( mesh itemGeom itemMat [] identityTransform
           ∷ label th lbl textT
           ∷ [])
         ∷ buildMenuItems th ih iw (suc idx) rest

-- Simple dropdown
dropdown : ∀ {M Msg}
         → ControlTheme
         → String
         → (M → Bool)
         → Msg
         → List (MenuItem Msg)
         → Transform
         → SceneNode M Msg
dropdown theme = dropdown3D theme defaultDropdownConfig

------------------------------------------------------------------------
-- Selection dropdown (shows selected value)
------------------------------------------------------------------------

selectionDropdown : ∀ {M Msg}
                  → ControlTheme
                  → (M → ℕ)              -- Selected index
                  → (M → Bool)           -- Is open?
                  → Msg                  -- Toggle
                  → (ℕ → Msg)            -- Select handler
                  → List String          -- Options
                  → Transform
                  → SceneNode M Msg
selectionDropdown {M} {Msg} theme getSelected isOpen toggleOpen selectHandler options t =
  let items = buildItems 0 options
      getLabel = λ m → getOptionAt (getSelected m) options
  in group t
       ( dynamicLabel theme getLabel
           (mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0))
       ∷ dropdown theme "▼" isOpen toggleOpen items
           (mkTransform (vec3 0.2 0.0 0.0) identityQuat (vec3 0.5 1.0 1.0))
       ∷ [])
  where
    buildItems : ℕ → List String → List (MenuItem Msg)
    buildItems _ [] = []
    buildItems idx (opt ∷ rest) =
      enabledItem opt (selectHandler idx) ∷ buildItems (suc idx) rest

    getOptionAt : ℕ → List String → String
    getOptionAt _ [] = ""
    getOptionAt zero (x ∷ _) = x
    getOptionAt (suc n) (_ ∷ rest) = getOptionAt n rest

------------------------------------------------------------------------
-- Radial menu (pie menu)
------------------------------------------------------------------------

record RadialConfig : Set where
  constructor mkRadialConfig
  field
    innerRadius : Float
    outerRadius : Float
    startAngle  : Float    -- radians
    sweepAngle  : Float    -- radians (2π for full circle)

defaultRadialConfig : RadialConfig
defaultRadialConfig = mkRadialConfig 0.1 0.3 0.0 6.283  -- Full circle

-- Radial/pie menu
radialMenu3D : ∀ {M Msg}
             → ControlTheme
             → RadialConfig
             → (M → Bool)              -- Is open?
             → List (MenuItem Msg)
             → Transform
             → SceneNode M Msg
radialMenu3D {M} {Msg} theme config isOpen items t =
  let ir = RadialConfig.innerRadius config
      or = RadialConfig.outerRadius config
      startA = RadialConfig.startAngle config
      sweep = RadialConfig.sweepAngle config
      n = length items
      sliceAngle = sweep * recip (natToFloat n)
      -- Build pie slices
      slices = buildSlices theme ir or startA sliceAngle 0 items
      -- Menu visibility
      getMenuScale = λ m →
        if isOpen m
          then mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
          else mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 0.0 0.0 0.0)
  in bindTransform getMenuScale
       (group t slices)
  where
    postulate natToFloat : ℕ → Float
    postulate recip : Float → Float
    postulate sinF : Float → Float
    postulate cosF : Float → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}
    {-# COMPILE JS recip = x => 1 / x #-}
    {-# COMPILE JS sinF = x => Math.sin(x) #-}
    {-# COMPILE JS cosF = x => Math.cos(x) #-}

    buildSlices : ControlTheme → Float → Float → Float → Float → ℕ
                → List (MenuItem Msg) → List (SceneNode M Msg)
    buildSlices _ _ _ _ _ _ [] = []
    buildSlices th ir or startA sliceA idx (menuItem lbl action enabled ∷ rest) =
      let angle = startA + natToFloat idx * sliceA + sliceA * 0.5
          midR = (ir + or) * 0.5
          x = midR * cosF angle
          y = midR * sinF angle
          itemT = mkTransform (vec3 x y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          -- Use simple box for slice (proper pie slice would need custom geometry)
          sliceGeom = roundedBox (vec3 0.08 0.04 0.02) 0.01 4
          sliceMat = if enabled
            then ControlTheme.surfaceMaterial th
            else disabledMaterial th
          textT = mkTransform (vec3 0.0 0.0 0.015) identityQuat (vec3 1.0 1.0 1.0)
          attrs = if enabled then onClick action ∷ [] else []
      in interactiveGroup attrs itemT
           ( mesh sliceGeom sliceMat [] identityTransform
           ∷ sizedLabel th 0.03 lbl textT
           ∷ [])
         ∷ buildSlices th ir or startA sliceA (suc idx) rest

-- Simple radial menu
radialMenu : ∀ {M Msg}
           → ControlTheme
           → (M → Bool)
           → List (MenuItem Msg)
           → Transform
           → SceneNode M Msg
radialMenu theme = radialMenu3D theme defaultRadialConfig

------------------------------------------------------------------------
-- Context menu (appears at position)
------------------------------------------------------------------------

contextMenu3D : ∀ {M Msg}
              → ControlTheme
              → (M → Maybe Vec3)        -- Position (Nothing = hidden)
              → List (MenuItem Msg)
              → SceneNode M Msg
contextMenu3D {M} {Msg} theme getPosition items =
  let ih = 0.07
      iw = 0.25
      menuHeight = natToFloat (length items) * ih
      getTransform = λ m → case getPosition m of λ where
        nothing → mkTransform (vec3 0.0 0.0 -100.0) identityQuat (vec3 0.0 0.0 0.0)
        (just pos) → mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
  in bindTransform getTransform
       (group identityTransform
         ( menuBackground iw menuHeight
         ∷ buildMenuItems 0 items ))
  where
    postulate natToFloat : ℕ → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}

    ih = 0.07
    iw = 0.25

    menuBackground : Float → Float → SceneNode M Msg
    menuBackground w h =
      mesh (roundedBox (vec3 w h 0.02) 0.015 4)
           (phong (ControlTheme.backgroundColor theme) 24.0)
           []
           identityTransform

    buildMenuItems : ℕ → List (MenuItem Msg) → List (SceneNode M Msg)
    buildMenuItems _ [] = []
    buildMenuItems idx (menuItem lbl action enabled ∷ rest) =
      let y = - (natToFloat idx * ih)
          itemT = mkTransform (vec3 0.0 y 0.01) identityQuat (vec3 1.0 1.0 1.0)
          itemGeom = roundedBox (vec3 (iw * 0.95) (ih * 0.85) 0.01) 0.008 4
          itemMat = if enabled
            then ControlTheme.surfaceMaterial theme
            else disabledMaterial theme
          textT = mkTransform (vec3 0.0 0.0 0.008) identityQuat (vec3 1.0 1.0 1.0)
          attrs = if enabled then onClick action ∷ [] else []
      in interactiveGroup attrs itemT
           ( mesh itemGeom itemMat [] identityTransform
           ∷ sizedLabel theme 0.04 lbl textT
           ∷ [])
         ∷ buildMenuItems (suc idx) rest

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x
