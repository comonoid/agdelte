{-# OPTIONS --without-K #-}

-- WebGLTest: interactive 3D scene with continuous animation
-- Demonstrates: perspective camera, phong material, lights,
-- bindTransform, bindMaterial, onClick, transitions, animate.
-- Click boxes to change state. Orbiting sphere is animated.

module WebGLTest where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Float as F using (Float; sin; cos)
open import Data.List using (List; []; _∷_; [_])
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; false)

open import Agdelte.Reactive.Node
open import Agdelte.WebGL.Types
  renaming (onClick to glClick; onHover to glHover; onLeave to glLeave)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

toFloat : ℕ → Float
toFloat zero = 0.0
toFloat (suc n) = 1.0 F.+ (toFloat n)

------------------------------------------------------------------------
-- Model / Msg / Update
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    posX   : ℕ   -- center box X offset (units of 0.5)
    scaleN : ℕ   -- center box scale (units of 0.25, starting from 4 = scale 1.0)
    clicks : ℕ   -- total click count

open Model public

initModel : Model
initModel = mkModel 4 4 0

data Msg : Set where
  MoveLeft   : Msg
  MoveRight  : Msg
  ScaleUp    : Msg
  ScaleDown  : Msg
  ClickLeft  : Msg
  ClickRight : Msg
  ClickCenter : Msg

updateModel : Msg → Model → Model
updateModel MoveLeft    m = mkModel (posX m ∸ 1) (scaleN m) (clicks m)
updateModel MoveRight   m = mkModel (posX m + 1) (scaleN m) (clicks m)
updateModel ScaleUp     m = mkModel (posX m) (scaleN m + 1) (clicks m)
updateModel ScaleDown   m = mkModel (posX m) (scaleN m ∸ 1) (clicks m)
updateModel ClickLeft   m = mkModel (posX m) (scaleN m) (clicks m + 1)
updateModel ClickRight  m = mkModel (posX m) (scaleN m) (clicks m + 1)
updateModel ClickCenter m = mkModel (posX m) (scaleN m + 1) (clicks m + 1)

------------------------------------------------------------------------
-- Derived values (Model → Transform / Material)
------------------------------------------------------------------------

centerTransform : Model → Transform
centerTransform m =
  let x = toFloat (posX m) F.* 0.5 F.- 2.0
      s = toFloat (scaleN m) F.* 0.25
  in mkTransform (vec3 x 0.0 0.0) identityQuat (vec3 s s s)

centerMaterial : Model → Material
centerMaterial m =
  let intensity = toFloat (scaleN m) F.* 0.1
  in phong (rgb intensity 0.3 0.2) 32.0

------------------------------------------------------------------------
-- Continuous animation: orbiting transform
------------------------------------------------------------------------

orbitTransform : Float → Transform
orbitTransform t =
  let x = 3.0 F.* cos t
      z = 3.0 F.* sin t
      y = 0.5 F.+ 0.5 F.* sin (t F.* 2.0)
  in mkTransform (vec3 x y z) identityQuat (vec3 0.5 0.5 0.5)

------------------------------------------------------------------------
-- Scene: interactive objects + animated orbit
------------------------------------------------------------------------

scene : Scene Model Msg
scene = mkScene
  (fixed (perspective 1.0 0.1 100.0) (vec3 0.0 2.0 8.0) (vec3 0.0 0.0 0.0))
  -- Lights
  ( light (ambient white 0.25)
  ∷ light (directional white 0.9 (vec3 -0.5 -1.0 -0.3))
  -- Left box: phong, click to increment counter
  ∷ mesh (sphere 0.9)
         (phong (rgb 0.2 0.5 0.8) 64.0)
         [ glClick ClickLeft ]
         (mkTransform (vec3 -2.5 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Center box: click to scale up, reactive transform + material with smooth transition
  ∷ bindTransform centerTransform
      (bindMaterial centerMaterial (box (vec3 1.5 1.5 1.5))
         (glClick ClickCenter ∷ transition (ms 300) easeInOut ∷ [])
         (mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)))
  -- Right box: phong, click to increment counter
  ∷ mesh (cylinder 0.7 1.8)
         (phong (rgb 0.2 0.7 0.3) 32.0)
         [ glClick ClickRight ]
         (mkTransform (vec3 2.5 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Orbiting sphere: continuous animation
  ∷ animate orbitTransform
      (mesh (sphere 0.4)
            (phong (rgb 0.9 0.8 0.2) 128.0)
            []
            identityTransform)
  -- Floor plane: unlit (for contrast)
  ∷ mesh (plane (vec2 10.0 10.0))
         (unlit (rgb 0.15 0.15 0.2))
         []
         (mkTransform (vec3 0.0 -1.5 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ [] )

------------------------------------------------------------------------
-- Template: DOM controls + WebGL canvas
------------------------------------------------------------------------

webglTemplate : Node Model Msg
webglTemplate =
  div [ class "webgl-demo" ]
    ( h1 [] [ text "Agdelte WebGL" ]
    ∷ glCanvas (attr "width" "800" ∷ attr "height" "600" ∷ []) scene
    ∷ div [ class "controls" ]
        ( button [ on "click" MoveLeft  ] [ text "← Left" ]
        ∷ button [ on "click" MoveRight ] [ text "Right →" ]
        ∷ button [ on "click" ScaleUp   ] [ text "Scale +" ]
        ∷ button [ on "click" ScaleDown ] [ text "Scale −" ]
        ∷ [] )
    ∷ p [] [ text "Click objects! Center box has transitions. Yellow sphere orbits continuously." ]
    ∷ p [] [ bind (mkBinding (λ m → "posX=" ++ show (posX m) ++ " scale=" ++ show (scaleN m) ++ " clicks=" ++ show (clicks m)) (λ _ _ → false)) ]
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = simpleApp initModel updateModel webglTemplate
