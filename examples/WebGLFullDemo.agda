{-# OPTIONS --without-K #-}

-- WebGLFullDemo: comprehensive WebGL scene covering all remaining features
-- Demonstrates: orthographic/fromModel camera, flat/pbr/textured materials,
-- point/spot lights, bindLight, icon, text3D/bindText3D, group,
-- onHover/onLeave, onScroll, onClickAt, onDrag, focusable/onKeyDown/onInput,
-- zoomScene, custom geometry.
-- Complements WebGLTest.agda which covers basics (perspective, phong, unlit,
-- animate, bindTransform, bindMaterial, onClick, transition).

module WebGLFullDemo where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Float as F using (Float; sin; cos)
open import Data.List using (List; []; _∷_; [_])
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)

open import Agdelte.Reactive.Node
open import Agdelte.WebGL.Types
  renaming ( onClick to glClick ; onHover to glHover ; onLeave to glLeave
           ; onScroll to glScroll ; onClickAt to glClickAt ; onDrag to glDrag
           ; focusable to glFocusable ; onKeyDown to glKeyDown
           ; onInput to glInput )

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

toFloat : ℕ → Float
toFloat zero = 0.0
toFloat (suc n) = 1.0 F.+ (toFloat n)

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    useOrtho     : Bool     -- camera projection toggle
    lightPower   : ℕ        -- point light intensity (units of 0.1)
    selectedObj  : ℕ        -- which object is highlighted (0=none)
    dragCount    : ℕ        -- how many drag events received
    clickAtCount : ℕ        -- how many clickAt events received
    keyCount     : ℕ        -- how many key events on focused obj
    scrollAccum  : ℕ        -- scroll events accumulated
    hovered      : ℕ        -- which object is hovered (0=none)

open Model public

initModel : Model
initModel = mkModel false 5 0 0 0 0 0 0

------------------------------------------------------------------------
-- Messages (only ℕ/Bool args — avoids --without-K issues with Vec3 etc.)
------------------------------------------------------------------------

data Msg : Set where
  ToggleCamera    : Msg
  LightUp         : Msg
  LightDown       : Msg
  SelectObj       : ℕ → Msg        -- glClick on object N
  HoverObj        : ℕ → Msg        -- glHover on object N
  LeaveObj        : ℕ → Msg        -- glLeave on object N
  Scrolled        : Msg            -- glScroll (discards Float)
  ClickedAt       : Msg            -- glClickAt (discards Vec3)
  Dragged         : Msg            -- glDrag (discards Vec3 pair)
  KeyPressed      : Msg            -- glKeyDown on focused obj
  InputReceived   : Msg            -- glInput on focused obj
  ResetCounters   : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel ToggleCamera m = record m { useOrtho = not (useOrtho m) }
updateModel LightUp m = record m { lightPower = lightPower m + 1 }
updateModel LightDown m = record m { lightPower = lightPower m ∸ 1 }
updateModel (SelectObj n) m = record m { selectedObj = n }
updateModel (HoverObj n) m = record m { hovered = n }
updateModel (LeaveObj n) m = record m { hovered = if hovered m ≡ᵇ n then 0 else hovered m }
updateModel Scrolled m = record m { scrollAccum = suc (scrollAccum m) }
updateModel ClickedAt m = record m { clickAtCount = suc (clickAtCount m) }
updateModel Dragged m = record m { dragCount = suc (dragCount m) }
updateModel KeyPressed m = record m { keyCount = suc (keyCount m) }
updateModel InputReceived m = record m { keyCount = suc (keyCount m) }
updateModel ResetCounters m = record m { dragCount = 0 ; clickAtCount = 0 ; keyCount = 0 ; scrollAccum = 0 }

------------------------------------------------------------------------
-- Derived values: Camera
------------------------------------------------------------------------

-- Reactive camera: switches between perspective and orthographic
cameraProjection : Model → Projection
cameraProjection m =
  if useOrtho m
  then orthographic 6.0 0.1 100.0
  else perspective 1.0 0.1 100.0

cameraPos : Model → Vec3
cameraPos _ = vec3 0.0 4.0 10.0

cameraTarget : Model → Vec3
cameraTarget _ = vec3 0.0 0.0 0.0

------------------------------------------------------------------------
-- Derived values: Lights
------------------------------------------------------------------------

-- Dynamic point light: intensity from model
pointLightFromModel : Model → Light
pointLightFromModel m =
  let intensity = toFloat (lightPower m) F.* 0.1
  in point (rgb 1.0 0.9 0.7) intensity (vec3 2.0 3.0 2.0) 15.0

------------------------------------------------------------------------
-- Derived values: Materials (hover highlights)
------------------------------------------------------------------------

-- PBR sphere: changes roughness when selected
pbrMaterial : Model → Material
pbrMaterial m =
  if selectedObj m ≡ᵇ 1
  then pbr (rgb 0.9 0.2 0.2) 0.9 0.2    -- metallic red when selected
  else pbr (rgb 0.8 0.8 0.8) 0.8 0.4    -- matte silver default

-- Flat floor: dims slightly when hovered
flatFloorMaterial : Model → Material
flatFloorMaterial m =
  if hovered m ≡ᵇ 5
  then flat (rgb 0.35 0.35 0.4)
  else flat (rgb 0.25 0.25 0.3)

------------------------------------------------------------------------
-- Derived values: Text
------------------------------------------------------------------------

statsText : Model → String
statsText m =
  "drags=" ++ show (dragCount m)
  ++ " clicks=" ++ show (clickAtCount m)
  ++ " keys=" ++ show (keyCount m)
  ++ " scroll=" ++ show (scrollAccum m)

selectedText : Model → String
selectedText m =
  if selectedObj m ≡ᵇ 0 then "none"
  else "obj " ++ show (selectedObj m)

lightText : Model → String
lightText m = "light=" ++ show (lightPower m)

------------------------------------------------------------------------
-- Text styles
------------------------------------------------------------------------

labelStyle : TextStyle
labelStyle = mkTextStyle (builtin sans) 0.3 white center singleLine

infoStyle : TextStyle
infoStyle = mkTextStyle (builtin mono) 0.2 (rgb 0.6 0.9 0.6) left singleLine

------------------------------------------------------------------------
-- Scene
------------------------------------------------------------------------

scene : Scene Model Msg
scene = mkScene
  -- Reactive camera (fromModel — switches ortho/perspective from model)
  (fromModel cameraProjection cameraPos cameraTarget)

  -- === Lights ===
  ( light (ambient (rgb 0.3 0.3 0.4) 0.3)                              -- ambient
  ∷ light (spot (rgb 0.8 0.8 1.0) 0.7                                  -- spot light
               (vec3 -3.0 5.0 0.0) (vec3 0.3 -1.0 0.0) 0.5 0.3)
  ∷ light (directional white 0.4 (vec3 0.5 -1.0 -0.5))                 -- directional
  ∷ bindLight pointLightFromModel                                        -- reactive point light

  -- === Object 1: PBR metallic sphere ===
  -- Demonstrates: pbr material, bindMaterial, glClick, glHover/glLeave
  ∷ bindMaterial pbrMaterial (sphere 0.8)
      ( glClick (SelectObj 1)
      ∷ glHover (HoverObj 1) ∷ glLeave (LeaveObj 1)
      ∷ transition (ms 400) easeInOut
      ∷ [])
      (mkTransform (vec3 -3.0 0.8 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Object 2: Textured box ===
  -- Demonstrates: textured material, glClickAt (surface coords)
  ∷ mesh (box (vec3 1.2 1.2 1.2))
         (textured (loadTexture "textures/crate.png") white)
         ( glClickAt (λ _ → ClickedAt)
         ∷ glHover (HoverObj 2) ∷ glLeave (LeaveObj 2)
         ∷ [])
         (mkTransform (vec3 0.0 0.6 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Object 3: Draggable cylinder ===
  -- Demonstrates: onDrag, flat material
  ∷ mesh (cylinder 0.5 1.5)
         (flat (rgb 0.2 0.6 0.9))
         ( glDrag (λ _ _ → Dragged)
         ∷ glClick (SelectObj 3)
         ∷ glHover (HoverObj 3) ∷ glLeave (LeaveObj 3)
         ∷ [])
         (mkTransform (vec3 3.0 0.75 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Object 4: Focusable box (keyboard interaction) ===
  -- Demonstrates: focusable, glKeyDown, onScroll
  ∷ mesh (box (vec3 1.0 1.0 1.0))
         (phong (rgb 0.9 0.7 0.2) 64.0)
         ( glFocusable
         ∷ glKeyDown (λ _ → KeyPressed)
         ∷ glScroll (λ _ → Scrolled)
         ∷ glClick (SelectObj 4)
         ∷ glHover (HoverObj 4) ∷ glLeave (LeaveObj 4)
         ∷ [])
         (mkTransform (vec3 -1.5 0.5 -2.5) identityQuat (vec3 1.0 1.0 1.0))

  -- === Group: two small objects under a common transform ===
  -- Demonstrates: group node
  ∷ group (mkTransform (vec3 1.5 0.0 -2.5) identityQuat (vec3 1.0 1.0 1.0))
      ( mesh (sphere 0.3)
             (phong (rgb 0.3 0.9 0.3) 32.0)
             [ glClick (SelectObj 5) ]
             (mkTransform (vec3 -0.5 0.3 0.0) identityQuat (vec3 1.0 1.0 1.0))
      ∷ mesh (sphere 0.3)
             (phong (rgb 0.9 0.3 0.9) 32.0)
             [ glClick (SelectObj 6) ]
             (mkTransform (vec3 0.5 0.3 0.0) identityQuat (vec3 1.0 1.0 1.0))
      ∷ [] )

  -- === Static text3D label ===
  -- Demonstrates: text3D (static string)
  ∷ text3D "WebGL Full Demo" labelStyle []
      (mkTransform (vec3 0.0 3.5 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Reactive text: bindText3D ===
  -- Demonstrates: bindText3D (dynamic string from model)
  ∷ bindText3D statsText infoStyle []
      (mkTransform (vec3 -3.5 2.5 0.0) identityQuat (vec3 1.0 1.0 1.0))

  ∷ bindText3D selectedText infoStyle []
      (mkTransform (vec3 -3.5 2.1 0.0) identityQuat (vec3 1.0 1.0 1.0))

  ∷ bindText3D lightText infoStyle []
      (mkTransform (vec3 -3.5 1.7 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Icon (textured quad) ===
  -- Demonstrates: icon node
  ∷ icon (loadTexture "textures/info-icon.png") (vec2 0.5 0.5) []
      (mkTransform (vec3 3.5 2.5 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Floor: flat material with reactive binding ===
  -- Demonstrates: flat material, bindMaterial on plane, onScroll
  ∷ bindMaterial flatFloorMaterial (plane (vec2 12.0 12.0))
      ( glScroll (λ _ → Scrolled)
      ∷ glHover (HoverObj 5) ∷ glLeave (LeaveObj 5)
      ∷ [])
      (mkTransform (vec3 0.0 -0.01 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Animated orbiting light indicator ===
  -- Demonstrates: animate with a small unlit sphere as visual indicator
  ∷ animate (λ t →
      let x = 2.0 F.* cos (t F.* 0.5)
          z = 2.0 F.* sin (t F.* 0.5)
      in mkTransform (vec3 x 3.0 z) identityQuat (vec3 0.15 0.15 0.15))
    (mesh (sphere 0.15)
          (unlit (rgb 1.0 0.9 0.5))
          []
          identityTransform)

  ∷ [] )

------------------------------------------------------------------------
-- Template: DOM controls + WebGL canvas
------------------------------------------------------------------------

webglTemplate : Node Model Msg
webglTemplate =
  div [ class "webgl-demo" ]
    ( h1 [] [ text "WebGL Full Demo" ]
    ∷ p  [] [ text "Covers all WebGL features not in WebGLTest" ]
    ∷ glCanvas (attr "width" "900" ∷ attr "height" "600" ∷ []) scene
    ∷ div [ class "controls" ]
        ( button [ on "click" ToggleCamera ] [ text "Toggle Ortho/Persp" ]
        ∷ button [ on "click" LightUp ]      [ text "Light +" ]
        ∷ button [ on "click" LightDown ]     [ text "Light −" ]
        ∷ button [ on "click" ResetCounters ] [ text "Reset Counters" ]
        ∷ [] )
    ∷ div [ class "info" ]
        ( p [] [ text "1: PBR sphere (click/hover) | 2: Textured box (clickAt) | 3: Cylinder (drag)" ]
        ∷ p [] [ text "4: Phong box (focusable, keyboard, scroll) | 5-6: Grouped spheres | Floor (scroll/hover)" ]
        ∷ [] )
    ∷ p [] [ bind (mkBinding statsText (λ _ _ → false)) ]
    ∷ p [] [ bind (mkBinding (λ m → "camera=" ++ (if useOrtho m then "ortho" else "persp")
                              ++ " selected=" ++ selectedText m
                              ++ " hovered=" ++ show (hovered m)
                              ++ " " ++ lightText m) (λ _ _ → false)) ]
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel webglTemplate
