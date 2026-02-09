{-# OPTIONS --without-K #-}

-- WebGLFullDemo: comprehensive WebGL scene covering all remaining features
-- Demonstrates: orthographic/fromModel camera, flat/pbr/textured materials,
-- point/spot lights, bindLight, text3D/bindText3D, group,
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
           ; onMiddleDrag to glMiddleDrag ; onScreenDrag to glScreenDrag
           ; focusable to glFocusable ; onKeyDown to glKeyDown
           ; onInput to glInput ; animateOnHover to glAnimateOnHover )

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

toFloat : ℕ → Float
toFloat zero = 0.0
toFloat (suc n) = 1.0 F.+ (toFloat n)

postulate floatEq : Float → Float → Bool
{-# COMPILE JS floatEq = x => y => x === y #-}

postulate floatLt : Float → Float → Bool
{-# COMPILE JS floatLt = x => y => x < y #-}

postulate floatGt : Float → Float → Bool
{-# COMPILE JS floatGt = x => y => x > y #-}

-- Append lists
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

------------------------------------------------------------------------
-- Constants (formerly magic numbers)
------------------------------------------------------------------------

-- Camera sensitivity
orbitSensitivity : Float
orbitSensitivity = 0.005

panSensitivityBase : Float
panSensitivityBase = 0.002

zoomSensitivity : Float
zoomSensitivity = 0.01

-- Camera limits
minElevation : Float
minElevation = 0.05

maxElevation : Float
maxElevation = 1.5

minDistance : Float
minDistance = 2.0

maxDistance : Float
maxDistance = 30.0

-- Initial camera state
initCamAngle : Float
initCamAngle = 0.0

initCamElevation : Float
initCamElevation = 0.38

initCamDistance : Float
initCamDistance = 10.77

initOrbitHeight : Float
initOrbitHeight = 2.0

-- Animation speeds
hoverRotationSpeed : Float
hoverRotationSpeed = 7.854  -- 180°/0.4s = 2.5π rad/s

orbitLightSpeed : Float
orbitLightSpeed = 0.5

orbitLightRadius : Float
orbitLightRadius = 1.5

orbitHeightStep : Float
orbitHeightStep = 0.3

------------------------------------------------------------------------
-- Model (split into nested records for clarity)
------------------------------------------------------------------------

-- Camera state: orbit angles, distance, pan target
record CameraState : Set where
  constructor mkCameraState
  field
    angle        : Float  -- azimuth (radians)
    baseAngle    : Float  -- azimuth at gesture start
    elevation    : Float  -- elevation angle (radians)
    baseElevation : Float -- elevation at gesture start
    distance     : Float  -- distance from target
    targetX      : Float  -- pan offset X
    targetY      : Float  -- pan offset Y
    targetZ      : Float  -- pan offset Z
    basePanX     : Float  -- pan X at gesture start
    basePanY     : Float  -- pan Y at gesture start
    basePanZ     : Float  -- pan Z at gesture start
    orbitStartX  : Float  -- screen X at orbit start
    orbitStartY  : Float  -- screen Y at orbit start
    panStartX    : Float  -- screen X at pan start
    panStartY    : Float  -- screen Y at pan start

open CameraState public

initCamera : CameraState
initCamera = mkCameraState
  initCamAngle initCamAngle
  initCamElevation initCamElevation
  initCamDistance
  0.0 0.0 0.0    -- target
  0.0 0.0 0.0    -- basePan
  0.0 0.0        -- orbitStart
  0.0 0.0        -- panStart

-- Object position on floor plane
record ObjPos : Set where
  constructor mkObjPos
  field posX : Float ; posZ : Float

open ObjPos public

-- All scene objects
record SceneObjects : Set where
  constructor mkSceneObjects
  field
    obj1 : ObjPos    -- PBR sphere
    obj2 : ObjPos    -- textured box
    obj3 : ObjPos    -- cylinder
    obj4 : ObjPos    -- phong box
    obj5 : ObjPos    -- dumbbell group
    obj5Rot : ℕ      -- rotation steps

open SceneObjects public

initObjects : SceneObjects
initObjects = mkSceneObjects
  (mkObjPos -3.0 0.0)   -- obj1
  (mkObjPos  0.0 0.0)   -- obj2
  (mkObjPos  3.0 0.0)   -- obj3
  (mkObjPos -1.5 -2.5)  -- obj4
  (mkObjPos  1.5 -2.5)  -- obj5
  0                      -- obj5Rot

-- UI counters
record Counters : Set where
  constructor mkCounters
  field
    dragCount    : ℕ
    clickAtCount : ℕ
    keyCount     : ℕ
    scrollAccum  : ℕ

open Counters public

initCounters : Counters
initCounters = mkCounters 0 0 0 0

-- Main model
record Model : Set where
  constructor mkModel
  field
    useOrtho     : Bool         -- camera projection toggle
    lightPower   : ℕ            -- point light intensity (units of 0.1)
    sphereActive : Bool         -- PBR sphere toggle
    selectedObj  : ℕ            -- highlighted object (0=none)
    hovered      : ℕ            -- hovered object (0=none)
    orbitHeight  : Float        -- orbiting light Y offset
    cam          : CameraState
    objs         : SceneObjects
    counters     : Counters

open Model public

initModel : Model
initModel = mkModel false 8 false 0 0 initOrbitHeight initCamera initObjects initCounters

-- Accessors for backward compatibility
camAngle : Model → Float
camAngle m = angle (cam m)

camBaseAngle : Model → Float
camBaseAngle m = baseAngle (cam m)

camElevAngle : Model → Float
camElevAngle m = elevation (cam m)

camBaseElevAngle : Model → Float
camBaseElevAngle m = baseElevation (cam m)

camDistance : Model → Float
camDistance m = distance (cam m)

camTargetX : Model → Float
camTargetX m = targetX (cam m)

camTargetY : Model → Float
camTargetY m = targetY (cam m)

camTargetZ : Model → Float
camTargetZ m = targetZ (cam m)

camBasePanX : Model → Float
camBasePanX m = basePanX (cam m)

camBasePanY : Model → Float
camBasePanY m = basePanY (cam m)

camBasePanZ : Model → Float
camBasePanZ m = basePanZ (cam m)

obj1X : Model → Float
obj1X m = posX (obj1 (objs m))
obj1Z : Model → Float
obj1Z m = posZ (obj1 (objs m))

obj2X : Model → Float
obj2X m = posX (obj2 (objs m))
obj2Z : Model → Float
obj2Z m = posZ (obj2 (objs m))

obj3X : Model → Float
obj3X m = posX (obj3 (objs m))
obj3Z : Model → Float
obj3Z m = posZ (obj3 (objs m))

obj4X : Model → Float
obj4X m = posX (obj4 (objs m))
obj4Z : Model → Float
obj4Z m = posZ (obj4 (objs m))

obj5X : Model → Float
obj5X m = posX (obj5 (objs m))
obj5Z : Model → Float
obj5Z m = posZ (obj5 (objs m))


-- Update helpers for nested records
updateCam : (CameraState → CameraState) → Model → Model
updateCam f m = record m { cam = f (cam m) }

updateObjs : (SceneObjects → SceneObjects) → Model → Model
updateObjs f m = record m { objs = f (objs m) }

updateCounters : (Counters → Counters) → Model → Model
updateCounters f m = record m { counters = f (counters m) }

-- Set object position by index
setObjPos : ℕ → Float → Float → SceneObjects → SceneObjects
setObjPos 1 x z os = record os { obj1 = mkObjPos x z }
setObjPos 2 x z os = record os { obj2 = mkObjPos x z }
setObjPos 3 x z os = record os { obj3 = mkObjPos x z }
setObjPos 4 x z os = record os { obj4 = mkObjPos x z }
setObjPos 5 x z os = record os { obj5 = mkObjPos x z }
setObjPos _ _ _ os = os

------------------------------------------------------------------------
-- Messages (only ℕ/Bool args — avoids --without-K issues with Vec3 etc.)
------------------------------------------------------------------------

data Msg : Set where
  ToggleCamera    : Msg
  ToggleSphere    : Msg            -- glClick on PBR sphere
  LightUp         : Msg
  LightDown       : Msg
  SelectObj       : ℕ → Msg        -- glClick on object N
  HoverObj        : ℕ → Msg        -- glHover on object N
  LeaveObj        : ℕ → Msg        -- glLeave on object N
  Scrolled        : Msg            -- glScroll (discards Float)
  ClickedAt       : Msg            -- glClickAt (discards Vec3)
  DragObj         : ℕ → Float → Float → Msg  -- drag object N to (x, z)
  RotateView      : Float → Float → Float → Float → Msg  -- screen-drag: startPxX, curPxX, startPxY, curPxY
  PanView         : Float → Float → Float → Float → Msg  -- middle-drag (world): startX, curX, startZ, curZ
  Zoom            : Float → Msg              -- scroll delta (positive = zoom out)
  OrbitUp         : Msg                       -- raise orbiting sphere
  OrbitDown       : Msg                       -- lower orbiting sphere
  KeyPressed      : Msg            -- glKeyDown on focused obj
  InputReceived   : Msg            -- glInput on focused obj
  RotateObj5      : Msg            -- spin dumbbell 180° on click
  ResetCounters   : Msg

------------------------------------------------------------------------
-- Attribute helpers (reduce duplication)
------------------------------------------------------------------------

-- Common interactive attrs for draggable, clickable, hoverable object
interactiveAttrs : ℕ → List (SceneAttr Msg)
interactiveAttrs n =
  glDrag (dragH n) ∷ glClick (SelectObj n) ∷ glHover (HoverObj n) ∷ glLeave (LeaveObj n) ∷ []
  where
    dragH : ℕ → Vec3 → Vec3 → Msg
    dragH i _ cur = DragObj i (vec3X cur) (vec3Z cur)

-- Same with transition
interactiveWithTransition : ℕ → Duration → Easing → List (SceneAttr Msg)
interactiveWithTransition n d e = interactiveAttrs n ++L (transition d e ∷ [])

------------------------------------------------------------------------
-- Material helpers (hover highlighting)
------------------------------------------------------------------------

-- Apply hover highlight to material
withHover : ℕ → Material → Material → Model → Material
withHover n hoverMat normalMat m = if hovered m ≡ᵇ n then hoverMat else normalMat

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel ToggleCamera m = record m { useOrtho = not (useOrtho m) }
updateModel ToggleSphere m = record m { sphereActive = not (sphereActive m) }
updateModel LightUp m = record m { lightPower = lightPower m + 1 }
updateModel LightDown m = record m { lightPower = lightPower m ∸ 1 }
updateModel (SelectObj n) m = record m { selectedObj = if selectedObj m ≡ᵇ n then 0 else n }
updateModel (HoverObj n) m = record m { hovered = n }
updateModel (LeaveObj n) m = record m { hovered = if hovered m ≡ᵇ n then 0 else hovered m }
updateModel Scrolled m =
  updateCounters (λ c → record c { scrollAccum = suc (scrollAccum c) }) m
updateModel ClickedAt m =
  updateCounters (λ c → record c { clickAtCount = suc (clickAtCount c) }) m
updateModel (DragObj n x z) m =
  updateObjs (setObjPos n x z)
    (updateCounters (λ c → record c { dragCount = suc (dragCount c) }) m)
updateModel (RotateView sx cx sy cy) m =
  -- Orbit: screen-space pixels → azimuth + elevation
  -- drag right → scene rotates right (azimuth decreases)
  -- drag up → scene tilts up (elevation decreases, screen Y inverted)
  let c = cam m
      sameGesture = if floatEq sx (orbitStartX c) then floatEq sy (orbitStartY c) else false
      baseA = if sameGesture then baseAngle c else angle c
      baseE = if sameGesture then baseElevation c else elevation c
      newAngle = baseA F.- (cx F.- sx) F.* orbitSensitivity
      newElev  = baseE F.+ (cy F.- sy) F.* orbitSensitivity
      clampedElev = if floatLt newElev minElevation then minElevation
                    else if floatGt newElev maxElevation then maxElevation else newElev
  in updateCam (λ _ → record c
       { angle = newAngle ; elevation = clampedElev
       ; baseAngle = baseA ; baseElevation = baseE
       ; orbitStartX = sx ; orbitStartY = sy }) m
updateModel (PanView sx cx sy cy) m =
  -- Pan: move camera along its local RIGHT and UP axes (like Blender Shift+MMB)
  -- Camera looks from position toward target. We move both by the same offset.
  let c = cam m
      sameGesture = if floatEq sx (panStartX c) then floatEq sy (panStartY c) else false
      bpX = if sameGesture then basePanX c else targetX c
      bpY = if sameGesture then basePanY c else targetY c
      bpZ = if sameGesture then basePanZ c else targetZ c
      dpx = cx F.- sx
      dpy = cy F.- sy
      sens = distance c F.* panSensitivityBase
      a = angle c
      e = elevation c
      -- Camera's local RIGHT vector: perpendicular to view direction in XZ plane
      -- For orbit camera looking at target: right = (cos(a), 0, -sin(a))
      rightX = cos a
      rightZ = 0.0 F.- sin a
      -- Camera's local UP vector: cross(right, forward)
      -- forward = (-cos(e)*sin(a), -sin(e), -cos(e)*cos(a))  [normalized, toward target]
      -- up = cross(right, forward) where right = (cos(a), 0, -sin(a))
      -- upX = 0*(-cos(e)*cos(a)) - (-sin(a))*(-sin(e)) = -sin(a)*sin(e)
      -- upY = (-sin(a))*(-cos(e)*sin(a)) - cos(a)*(-cos(e)*cos(a)) = cos(e)*(sin²a + cos²a) = cos(e)
      -- upZ = cos(a)*(-sin(e)) - 0*(-cos(e)*sin(a)) = -cos(a)*sin(e)
      upX = (0.0 F.- sin a) F.* sin e
      upY = cos e
      upZ = (0.0 F.- cos a) F.* sin e
      -- Move along right (screen X) and up (screen Y)
      moveX = ((0.0 F.- dpx) F.* rightX F.+ dpy F.* upX) F.* sens
      moveY = dpy F.* upY F.* sens
      moveZ = ((0.0 F.- dpx) F.* rightZ F.+ dpy F.* upZ) F.* sens
  in updateCam (λ _ → record c
       { targetX = bpX F.+ moveX
       ; targetY = bpY F.+ moveY
       ; targetZ = bpZ F.+ moveZ
       ; basePanX = bpX ; basePanY = bpY ; basePanZ = bpZ
       ; panStartX = sx ; panStartY = sy }) m
updateModel (Zoom delta) m =
  let c = cam m
      d = distance c F.+ delta F.* zoomSensitivity
      clamped = if floatLt d minDistance then minDistance
                else if floatGt d maxDistance then maxDistance else d
  in updateCam (λ _ → record c { distance = clamped }) m
updateModel OrbitUp m = record m { orbitHeight = orbitHeight m F.+ orbitHeightStep }
updateModel OrbitDown m = record m { orbitHeight = orbitHeight m F.- orbitHeightStep }
updateModel KeyPressed m =
  updateCounters (λ c → record c { keyCount = suc (keyCount c) }) m
updateModel InputReceived m =
  updateCounters (λ c → record c { keyCount = suc (keyCount c) }) m
updateModel RotateObj5 m =
  updateObjs (λ os → record os { obj5Rot = suc (obj5Rot os) }) m
updateModel ResetCounters m =
  record m { sphereActive = false
           ; orbitHeight = initOrbitHeight
           ; cam = initCamera
           ; objs = initObjects
           ; counters = initCounters }

------------------------------------------------------------------------
-- Derived values: Camera
------------------------------------------------------------------------

-- Reactive camera: switches between perspective and orthographic
cameraProjection : Model → Projection
cameraProjection m =
  if useOrtho m
  then orthographic 6.0 0.1 100.0
  else perspective 1.0 0.1 100.0

-- Camera: spherical orbit + pan offset
cameraPos : Model → Vec3
cameraPos m =
  let a = camAngle m
      e = camElevAngle m
      d = camDistance m
      h = d F.* cos e
  in vec3 (h F.* sin a F.+ camTargetX m) (d F.* sin e F.+ camTargetY m) (h F.* cos a F.+ camTargetZ m)

cameraTarget : Model → Vec3
cameraTarget m = vec3 (camTargetX m) (camTargetY m) (camTargetZ m)

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

-- PBR sphere: toggles material on its own click + hover glow
pbrMaterial : Model → Material
pbrMaterial m =
  if hovered m ≡ᵇ 1
  then (if sphereActive m
        then pbr (rgb 1.0 0.4 0.4) 0.9 0.2
        else pbr (rgb 0.95 0.95 0.95) 0.8 0.4)
  else (if sphereActive m
        then pbr (rgb 0.9 0.2 0.2) 0.9 0.2
        else pbr (rgb 0.8 0.8 0.8) 0.8 0.4)

-- Crate box: slight tint on hover
crateTex : TextureHandle
crateTex = loadTexture "textures/crate.png"

obj2Material : Model → Material
obj2Material m =
  if hovered m ≡ᵇ 2
  then textured crateTex (rgb 1.0 1.0 0.85)
  else textured crateTex white

-- Cylinder: PBR with slight brighten on hover
obj3Material : Model → Material
obj3Material m =
  if hovered m ≡ᵇ 3
  then pbr (rgb 0.55 0.75 1.0) 0.85 0.55
  else pbr (rgb 0.4 0.6 0.95) 0.85 0.55

-- Phong box: slight brighten on hover
obj4Material : Model → Material
obj4Material m =
  if hovered m ≡ᵇ 4
  then phong (rgb 1.0 0.85 0.35) 64.0
  else phong (rgb 0.9 0.7 0.2) 64.0

-- Dumbbell left sphere: green, brighten on hover
obj5LeftMat : Model → Material
obj5LeftMat m =
  if hovered m ≡ᵇ 5
  then phong (rgb 0.45 1.0 0.45) 32.0
  else phong (rgb 0.3 0.9 0.3) 32.0

-- Dumbbell right sphere: purple, brighten on hover
obj5RightMat : Model → Material
obj5RightMat m =
  if hovered m ≡ᵇ 5
  then phong (rgb 1.0 0.45 1.0) 32.0
  else phong (rgb 0.9 0.3 0.9) 32.0

-- Dumbbell bar: unlit, brighten on hover
obj5BarMat : Model → Material
obj5BarMat m =
  if hovered m ≡ᵇ 5
  then unlit (rgb 0.8 0.8 0.8)
  else unlit (rgb 0.6 0.6 0.6)

-- Floor material
gridTex : TextureHandle
gridTex = loadTexture "textures/grid.png"

floorMaterial : Material
floorMaterial = textured gridTex white

------------------------------------------------------------------------
-- Derived values: Draggable object transforms
------------------------------------------------------------------------

-- Helper: drag handler for object N — extracts floor-plane X,Z from current point
dragH : ℕ → Vec3 → Vec3 → Msg
dragH n _ cur = DragObj n (vec3X cur) (vec3Z cur)

obj1Transform : Model → Transform
obj1Transform m = mkTransform (vec3 (obj1X m) 0.8 (obj1Z m)) identityQuat (vec3 1.0 1.0 1.0)

obj2Transform : Model → Transform
obj2Transform m = mkTransform (vec3 (obj2X m) 0.6 (obj2Z m)) identityQuat (vec3 1.0 1.0 1.0)

-- Obj5 rotation (180° per click around Y axis, with transition)
obj5RotTransform : Model → Transform
obj5RotTransform m =
  let halfA = toFloat (obj5Rot (objs m)) F.* 1.5708  -- n × π/2 (half of n × π)
  in mkTransform (vec3 0.0 0.0 0.0) (quat 0.0 (sin halfA) 0.0 (cos halfA)) (vec3 1.0 1.0 1.0)

obj3Transform : Model → Transform
obj3Transform m = mkTransform (vec3 (obj3X m) 0.75 (obj3Z m)) identityQuat (vec3 1.0 1.0 1.0)

obj4Transform : Model → Transform
obj4Transform m = mkTransform (vec3 (obj4X m) 0.5 (obj4Z m)) identityQuat (vec3 1.0 1.0 1.0)

obj5Transform : Model → Transform
obj5Transform m = mkTransform (vec3 (obj5X m) 0.0 (obj5Z m)) identityQuat (vec3 1.0 1.0 1.0)

-- Orbiting light vertical offset (bindTransform composes with animate)
orbitOffset : Model → Transform
orbitOffset m = mkTransform (vec3 0.0 (orbitHeight m) 0.0) identityQuat (vec3 1.0 1.0 1.0)

------------------------------------------------------------------------
-- Derived values: Text
------------------------------------------------------------------------

statsText : Model → String
statsText m =
  let c = counters m
  in "drags=" ++ show (dragCount c)
  ++ " clicks=" ++ show (clickAtCount c)
  ++ " keys=" ++ show (keyCount c)
  ++ " scroll=" ++ show (scrollAccum c)

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
  ( light (ambient (rgb 0.4 0.4 0.5) 0.5)                              -- ambient
  ∷ light (spot (rgb 0.8 0.8 1.0) 0.9                                  -- spot light
               (vec3 -3.0 5.0 0.0) (vec3 0.3 -1.0 0.0) 0.6 0.3)
  ∷ light (directional white 0.7 (vec3 0.5 -1.0 -0.5))                 -- directional
  ∷ bindLight pointLightFromModel                                        -- reactive point light

  -- === Object 1: PBR metallic sphere (click toggles material, drag to move) ===
  ∷ bindTransform obj1Transform
      (bindMaterial pbrMaterial (sphere 0.8)
        ( glDrag (dragH 1)
        ∷ glClick ToggleSphere
        ∷ glClick (SelectObj 1)
        ∷ glHover (HoverObj 1) ∷ glLeave (LeaveObj 1)
        ∷ [])
        identityTransform)

  -- === Object 2: Textured crate box (drag to move, continuous rotation) ===
  -- bindTransform for drag position; animate for continuous Y-axis rotation
  ∷ bindTransform obj2Transform
      (animate (λ t →
          let a = t F.* hoverRotationSpeed
          in mkTransform (vec3 0.0 0.0 0.0) (quat 0.0 (sin (a F.* 0.5)) 0.0 (cos (a F.* 0.5))) (vec3 1.0 1.0 1.0))
        (bindMaterial obj2Material (box (vec3 1.2 1.2 1.2))
              ( glDrag (dragH 2)
              ∷ glClick (SelectObj 2)
              ∷ glClickAt (λ _ → ClickedAt)
              ∷ glHover (HoverObj 2) ∷ glLeave (LeaveObj 2)
              ∷ glAnimateOnHover
              ∷ [])
              identityTransform))

  -- === Object 3: Cylinder — solid with metallic PBR (drag to move) ===
  ∷ bindTransform obj3Transform
      (bindMaterial obj3Material (cylinder 0.5 1.5)
            ( glDrag (dragH 3)
            ∷ glClick (SelectObj 3)
            ∷ glHover (HoverObj 3) ∷ glLeave (LeaveObj 3)
            ∷ [])
            identityTransform)

  -- === Object 4: Phong box (drag to move, focusable, keyboard, scroll) ===
  ∷ bindTransform obj4Transform
      (bindMaterial obj4Material (box (vec3 1.0 1.0 1.0))
            ( glDrag (dragH 4)
            ∷ glFocusable
            ∷ glKeyDown (λ _ → KeyPressed)
            ∷ glScroll (λ _ → Scrolled)
            ∷ glClick (SelectObj 4)
            ∷ glHover (HoverObj 4) ∷ glLeave (LeaveObj 4)
            ∷ [])
            identityTransform)

  -- === Object 5: Linked pair — dumbbell (click to rotate 180°) ===
  -- group separates position (instant drag) from rotation (animated transition)
  ∷ bindTransform obj5Transform
    (group identityTransform
      ( bindTransform obj5RotTransform
          (group identityTransform
            ( -- connecting bar
              bindMaterial obj5BarMat (cylinder 0.06 1.0)
                   ( glDrag (dragH 5)
                   ∷ glClick RotateObj5
                   ∷ glClick (SelectObj 5)
                   ∷ glHover (HoverObj 5) ∷ glLeave (LeaveObj 5)
                   ∷ transition (ms 200) easeInOut
                   ∷ [])
                   (mkTransform (vec3 0.0 0.3 0.0) (quat 0.0 0.0 0.707 0.707) (vec3 1.0 1.0 1.0))
            ∷ bindMaterial obj5LeftMat (sphere 0.3)
                   ( glDrag (dragH 5)
                   ∷ glClick RotateObj5
                   ∷ glClick (SelectObj 5)
                   ∷ glHover (HoverObj 5) ∷ glLeave (LeaveObj 5)
                   ∷ transition (ms 200) easeInOut
                   ∷ [])
                   (mkTransform (vec3 -0.5 0.3 0.0) identityQuat (vec3 1.0 1.0 1.0))
            ∷ bindMaterial obj5RightMat (sphere 0.3)
                   ( glDrag (dragH 5)
                   ∷ glClick RotateObj5
                   ∷ glClick (SelectObj 5)
                   ∷ glHover (HoverObj 5) ∷ glLeave (LeaveObj 5)
                   ∷ transition (ms 200) easeInOut
                   ∷ [])
                   (mkTransform (vec3 0.5 0.3 0.0) identityQuat (vec3 1.0 1.0 1.0))
            ∷ [] ))
      ∷ [] ))

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

  -- === Floor: flat material with reactive binding ===
  -- Demonstrates: flat material, bindMaterial on plane, onScroll, onScreenDrag (orbit), onMiddleDrag (pan)
  ∷ mesh (plane (vec2 12.0 12.0)) floorMaterial
      ( glScreenDrag (λ start cur → RotateView (vec3X start) (vec3X cur) (vec3Y start) (vec3Y cur))
      ∷ glMiddleDrag (λ start cur → PanView (vec3X start) (vec3X cur) (vec3Y start) (vec3Y cur))
      ∷ glScroll (λ d → Zoom d)
      ∷ [])
      (mkTransform (vec3 0.0 -0.01 0.0) identityQuat (vec3 1.0 1.0 1.0))

  -- === Animated orbiting light (height adjustable via buttons) ===
  -- bindTransform sets Y offset from model; animate provides XZ orbit.
  -- The runtime composes both transforms (pos addition).
  ∷ bindTransform orbitOffset
    (animate (λ t →
        let x = orbitLightRadius F.* cos (t F.* orbitLightSpeed)
            z = orbitLightRadius F.* sin (t F.* orbitLightSpeed)
        in mkTransform (vec3 x 0.0 z) identityQuat (vec3 0.5 0.5 0.5))
      (group identityTransform
        ( mesh (sphere 0.5)
               (unlit (rgb 1.0 0.9 0.5))
               []
               identityTransform
        ∷ light (point (rgb 1.0 0.9 0.5) 4.0 (vec3 0.0 0.0 0.0) 12.0)
        ∷ [] )))

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
        ∷ button [ on "click" OrbitUp ]       [ text "Orbit ↑" ]
        ∷ button [ on "click" OrbitDown ]     [ text "Orbit ↓" ]
        ∷ button [ on "click" ResetCounters ] [ text "Reset" ]
        ∷ [] )
    ∷ div [ class "info" ]
        ( p [] [ text "All objects are draggable on the floor plane. Click to select." ]
        ∷ p [] [ text "4: also focusable (keyboard/scroll) | Floor: scroll/hover" ]
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
app = simpleApp initModel updateModel webglTemplate
