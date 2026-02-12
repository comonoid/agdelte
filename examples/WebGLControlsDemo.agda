{-# OPTIONS --without-K #-}

-- WebGLControlsDemo: demonstrates the WebGL Controls library
--
-- Shows themed buttons with different sizes, toggle buttons,
-- and text components in a 3D scene.

module WebGLControlsDemo where

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Show using (show)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; [_])
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node
open import Agdelte.WebGL.Types
  renaming (onClick to glClick; onHover to glHover; onLeave to glLeave)
open import Agdelte.WebGL.Controls

------------------------------------------------------------------------
-- Model / Msg / Update
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    counter    : ℕ
    darkMode   : Bool
    option1    : Bool
    option2    : Bool

open Model public

initModel : Model
initModel = mkModel 0 false false false

data Msg : Set where
  Increment   : Msg
  Decrement   : Msg
  ToggleDark  : Msg
  ToggleOpt1  : Msg
  ToggleOpt2  : Msg
  Reset       : Msg

updateModel : Msg → Model → Model
updateModel Increment   m = mkModel (suc (counter m)) (darkMode m) (option1 m) (option2 m)
updateModel Decrement   m = mkModel (pred (counter m)) (darkMode m) (option1 m) (option2 m)
updateModel ToggleDark  m = mkModel (counter m) (if darkMode m then false else true) (option1 m) (option2 m)
updateModel ToggleOpt1  m = mkModel (counter m) (darkMode m) (if option1 m then false else true) (option2 m)
updateModel ToggleOpt2  m = mkModel (counter m) (darkMode m) (option1 m) (if option2 m then false else true)
updateModel Reset       m = mkModel 0 (darkMode m) false false

------------------------------------------------------------------------
-- Theme selection based on model
------------------------------------------------------------------------

getTheme : Model → ControlTheme
getTheme m = if darkMode m then darkTheme else defaultTheme

------------------------------------------------------------------------
-- 3D Scene with Controls
------------------------------------------------------------------------

scene : Scene Model Msg
scene = mkScene
  (fixed (perspective 1.0 0.1 100.0) (vec3 0.0 1.0 5.0) (vec3 0.0 0.0 0.0))
  -- Lights
  ( light (ambient white 0.6)
  ∷ light (directional white 0.5 (vec3 -0.5 -1.0 -0.3))
  ∷ light (directional white 0.3 (vec3 0.5 0.5 0.5))
  -- Title
  ∷ text3D "WebGL Controls Demo"
      (mkTextStyle (builtin sans) 0.3 (rgb 0.2 0.5 0.9) center singleLine)
      []
      (mkTransform (vec3 0.0 1.5 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Dynamic buttons that respond to theme changes
  ∷ bindChildren (λ m →
      let theme = getTheme m in
      -- Row 1: Counter buttons
      ( button3D theme defaultButtonConfig "-"  Decrement
          (mkTransform (vec3 -1.5 0.7 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ button3D theme defaultButtonConfig "+"  Increment
          (mkTransform (vec3 1.5 0.7 0.0) identityQuat (vec3 2.0 2.0 2.0))
      -- Row 2: Toggle buttons
      ∷ toggleButton theme defaultButtonConfig "Dark" darkMode ToggleDark
          (mkTransform (vec3 -2.5 0.0 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ toggleButton theme defaultButtonConfig "Opt 1" option1 ToggleOpt1
          (mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ toggleButton theme defaultButtonConfig "Opt 2" option2 ToggleOpt2
          (mkTransform (vec3 2.5 0.0 0.0) identityQuat (vec3 2.0 2.0 2.0))
      -- Row 3: Size variants
      ∷ smallButton3D theme "Small" Reset
          (mkTransform (vec3 -2.5 -0.7 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ defaultButton3D theme "Normal" Reset
          (mkTransform (vec3 0.0 -0.7 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ largeButton3D theme "Large" Reset
          (mkTransform (vec3 2.5 -0.7 0.0) identityQuat (vec3 2.0 2.0 2.0))
      -- Disabled button
      ∷ disabledButton theme defaultButtonConfig "Disabled"
          (mkTransform (vec3 0.0 -1.6 0.0) identityQuat (vec3 2.0 2.0 2.0))
      ∷ [] ) ) identityTransform
  -- Floor
  ∷ mesh (plane (vec2 12.0 12.0))
         (unlit (rgb 0.1 0.1 0.12))
         []
         (mkTransform (vec3 0.0 -2.5 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ [] )

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

webglTemplate : Node Model Msg
webglTemplate =
  div [ class "webgl-demo" ]
    ( h1 [] [ text "WebGL Controls Demo" ]
    ∷ glCanvas (attr "width" "800" ∷ attr "height" "600" ∷ []) scene
    ∷ p [] [ bind (mkBinding (λ m → "Counter: " ++ show (counter m)) (λ _ _ → false)) ]
    ∷ p [] [ text "Click the 3D buttons to interact. Toggle buttons change color when active." ]
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = simpleApp initModel updateModel webglTemplate
