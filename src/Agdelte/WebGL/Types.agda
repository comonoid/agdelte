{-# OPTIONS --without-K #-}

-- WebGL.Types: Core types for 3D scene graphs
--
-- These types describe a WebGL scene. The runtime (reactive-gl.js) interprets
-- the Scott-encoded values to create WebGL resources and render.

module Agdelte.WebGL.Types where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)

------------------------------------------------------------------------
-- Math primitives (FFI to JS typed arrays / plain objects)
------------------------------------------------------------------------

postulate
  Vec2 : Set
  Vec3 : Set
  Quat : Set

postulate
  vec2 : Float → Float → Vec2
  vec3 : Float → Float → Float → Vec3
  quat : Float → Float → Float → Float → Quat

{-# COMPILE JS vec2 = x => y => ({ x, y }) #-}
{-# COMPILE JS vec3 = x => y => z => ({ x, y, z }) #-}
{-# COMPILE JS quat = x => y => z => w => ({ x, y, z, w }) #-}

postulate
  vec3X : Vec3 → Float
  vec3Y : Vec3 → Float
  vec3Z : Vec3 → Float

{-# COMPILE JS vec3X = v => v.x #-}
{-# COMPILE JS vec3Y = v => v.y #-}
{-# COMPILE JS vec3Z = v => v.z #-}

identityQuat : Quat
identityQuat = quat 0.0 0.0 0.0 1.0

------------------------------------------------------------------------
-- Color (GPU: Float 0-1, NOT Css.Color which is ℕ 0-255)
------------------------------------------------------------------------

postulate
  GlColor : Set

postulate
  rgb  : Float → Float → Float → GlColor
  rgba : Float → Float → Float → Float → GlColor

{-# COMPILE JS rgb  = r => g => b => ({ r, g, b, a: 1.0 }) #-}
{-# COMPILE JS rgba = r => g => b => a => ({ r, g, b, a }) #-}

white : GlColor
white = rgb 1.0 1.0 1.0

black : GlColor
black = rgb 0.0 0.0 0.0

------------------------------------------------------------------------
-- Transform
------------------------------------------------------------------------

data Transform : Set where
  mkTransform : Vec3 → Quat → Vec3 → Transform
  --            pos    rot    scale

identityTransform : Transform
identityTransform = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)

------------------------------------------------------------------------
-- Geometry (built-in primitives)
------------------------------------------------------------------------

postulate
  BufferHandle  : Set
  TextureHandle : Set

postulate
  loadTexture : String → TextureHandle

{-# COMPILE JS loadTexture = url => url #-}

data Geometry : Set where
  box      : Vec3 → Geometry              -- dimensions (w, h, d)
  sphere   : Float → Geometry             -- radius
  plane    : Vec2 → Geometry              -- width, height
  cylinder : Float → Float → Geometry     -- radius, height
  custom   : BufferHandle → Geometry      -- arbitrary mesh data

------------------------------------------------------------------------
-- Material
------------------------------------------------------------------------

data Material : Set where
  unlit    : GlColor → Material              -- flat color, no lighting
  flat     : GlColor → Material              -- ambient-only lighting
  phong    : GlColor → Float → Material     -- color, shininess (specular exponent)
  pbr      : GlColor → Float → Float → Material  -- albedo, metallic, roughness
  textured : TextureHandle → GlColor → Material  -- texture URL, tint color

------------------------------------------------------------------------
-- Light
------------------------------------------------------------------------

data Light : Set where
  ambient     : GlColor → Float → Light
  --            color     intensity
  directional : GlColor → Float → Vec3 → Light
  --            color     intensity  direction
  point       : GlColor → Float → Vec3 → Float → Light
  --            color     intensity  position  range
  spot        : GlColor → Float → Vec3 → Vec3 → Float → Float → Light
  --            color     intensity  pos    dir     angle   falloff

------------------------------------------------------------------------
-- Camera (parameterized by Model for reactive camera)
------------------------------------------------------------------------

data Projection : Set where
  perspective  : Float → Float → Float → Projection
  --             fov (radians) near  far
  orthographic : Float → Float → Float → Projection
  --             size           near    far

data Camera (Model : Set) : Set where
  fixed     : Projection → Vec3 → Vec3 → Camera Model
  --                       pos     target
  fromModel : (Model → Projection) → (Model → Vec3) → (Model → Vec3) → Camera Model
  --           projection             position          target

------------------------------------------------------------------------
-- Animation (declarative transitions)
------------------------------------------------------------------------

data Duration : Set where
  ms : ℕ → Duration

data Easing : Set where
  linear      : Easing
  easeIn      : Easing
  easeOut     : Easing
  easeInOut   : Easing
  cubicBezier : Float → Float → Float → Float → Easing

------------------------------------------------------------------------
-- Scene attributes (events + transitions)
------------------------------------------------------------------------

postulate
  KeyEvent : Set

postulate
  keyEventKey   : KeyEvent → String
  keyEventShift : KeyEvent → Bool
  keyEventCtrl  : KeyEvent → Bool
  keyEventAlt   : KeyEvent → Bool

{-# COMPILE JS keyEventKey   = e => e.key #-}
{-# COMPILE JS keyEventShift = e => e.shiftKey #-}
{-# COMPILE JS keyEventCtrl  = e => e.ctrlKey #-}
{-# COMPILE JS keyEventAlt   = e => e.altKey #-}

data SceneAttr (Msg : Set) : Set where
  -- Events (color picking)
  onClick    : Msg → SceneAttr Msg
  onHover    : Msg → SceneAttr Msg
  onLeave    : Msg → SceneAttr Msg
  onScroll   : (Float → Msg) → SceneAttr Msg
  -- Events (color picking + ray cast)
  onClickAt  : (Vec3 → Msg) → SceneAttr Msg
  onDrag     : (Vec3 → Vec3 → Msg) → SceneAttr Msg
  onMiddleDrag : (Vec3 → Vec3 → Msg) → SceneAttr Msg  -- middle mouse button drag
  onScreenDrag : (Vec3 → Vec3 → Msg) → SceneAttr Msg  -- left drag, screen pixel coords (x=px, y=px, z=0)
  -- Focus / keyboard
  focusable  : SceneAttr Msg
  onKeyDown  : (KeyEvent → Msg) → SceneAttr Msg
  onInput    : (String → Msg) → SceneAttr Msg
  -- Animation
  transition      : Duration → Easing → SceneAttr Msg
  animateOnHover  : SceneAttr Msg    -- parent animate node only ticks while hovered

------------------------------------------------------------------------
-- Text types (MSDF font rendering)
------------------------------------------------------------------------

data BuiltinFont : Set where
  sans : BuiltinFont
  mono : BuiltinFont

data FontRef : Set where
  builtin : BuiltinFont → FontRef
  custom  : String → FontRef    -- URL to MSDF atlas

data Align : Set where
  left   : Align
  center : Align
  right  : Align

data TextLayout : Set where
  singleLine : TextLayout
  wrapAt     : Float → TextLayout   -- max width, word wrap
  ellipsis   : Float → TextLayout   -- max width, truncate with "..."

data TextStyle : Set where
  mkTextStyle : FontRef → Float → GlColor → Align → TextLayout → TextStyle
  --            font      size    color     align   layout

------------------------------------------------------------------------
-- Scene node (parameterized by Model and Msg)
------------------------------------------------------------------------

data SceneNode (Model Msg : Set) : Set where
  -- Static nodes
  mesh  : Geometry → Material → List (SceneAttr Msg) → Transform
        → SceneNode Model Msg
  group : Transform → List (SceneNode Model Msg) → SceneNode Model Msg

  -- Icon (textured quad)
  icon : TextureHandle → Vec2 → List (SceneAttr Msg) → Transform
       → SceneNode Model Msg

  -- Text (MSDF rendering)
  text3D     : String → TextStyle → List (SceneAttr Msg) → Transform
             → SceneNode Model Msg
  bindText3D : (Model → String) → TextStyle → List (SceneAttr Msg) → Transform
             → SceneNode Model Msg

  -- Lighting
  light     : Light → SceneNode Model Msg
  bindLight : (Model → Light) → SceneNode Model Msg

  -- Reactive bindings
  bindTransform : (Model → Transform) → SceneNode Model Msg
               → SceneNode Model Msg
  bindMaterial  : (Model → Material) → Geometry → List (SceneAttr Msg)
               → Transform → SceneNode Model Msg

  -- Continuous animation
  animate : (Float → Transform) → SceneNode Model Msg → SceneNode Model Msg
  --        time (seconds)        wraps existing node

------------------------------------------------------------------------
-- Scene = camera + nodes
------------------------------------------------------------------------

data Scene (Model Msg : Set) : Set where
  mkScene : Camera Model → List (SceneNode Model Msg) → Scene Model Msg

------------------------------------------------------------------------
-- Scene composition (zoom / remap Model and Msg)
------------------------------------------------------------------------

mapSceneAttrs : ∀ {Msg Msg'} → (Msg' → Msg) → List (SceneAttr Msg') → List (SceneAttr Msg)
mapSceneAttrs wrap [] = []
mapSceneAttrs wrap (onClick msg ∷ rest)        = onClick (wrap msg) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onHover msg ∷ rest)        = onHover (wrap msg) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onLeave msg ∷ rest)        = onLeave (wrap msg) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onScroll handler ∷ rest)   = onScroll (λ f → wrap (handler f)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onClickAt handler ∷ rest)  = onClickAt (λ v → wrap (handler v)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onDrag handler ∷ rest)     = onDrag (λ s c → wrap (handler s c)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onMiddleDrag handler ∷ rest) = onMiddleDrag (λ s c → wrap (handler s c)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onScreenDrag handler ∷ rest) = onScreenDrag (λ s c → wrap (handler s c)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (focusable ∷ rest)          = focusable ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onKeyDown handler ∷ rest)  = onKeyDown (λ e → wrap (handler e)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (onInput handler ∷ rest)    = onInput (λ s → wrap (handler s)) ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (transition d e ∷ rest)     = transition d e ∷ mapSceneAttrs wrap rest
mapSceneAttrs wrap (animateOnHover ∷ rest)    = animateOnHover ∷ mapSceneAttrs wrap rest

mutual
  zoomSceneNode : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg)
                → SceneNode M' Msg' → SceneNode M Msg
  zoomSceneNode get wrap (mesh g m attrs t) =
    mesh g m (mapSceneAttrs wrap attrs) t
  zoomSceneNode get wrap (icon tex sz attrs t) =
    icon tex sz (mapSceneAttrs wrap attrs) t
  zoomSceneNode get wrap (text3D str style attrs t) =
    text3D str style (mapSceneAttrs wrap attrs) t
  zoomSceneNode get wrap (bindText3D extract style attrs t) =
    bindText3D (λ m → extract (get m)) style (mapSceneAttrs wrap attrs) t
  zoomSceneNode get wrap (group t children) =
    group t (mapSceneNodes get wrap children)
  zoomSceneNode get wrap (light l) = light l
  zoomSceneNode get wrap (bindLight extract) =
    bindLight (λ m → extract (get m))
  zoomSceneNode get wrap (bindTransform extract child) =
    bindTransform (λ m → extract (get m)) (zoomSceneNode get wrap child)
  zoomSceneNode get wrap (bindMaterial extract g attrs t) =
    bindMaterial (λ m → extract (get m)) g (mapSceneAttrs wrap attrs) t
  zoomSceneNode get wrap (animate timeFn child) =
    animate timeFn (zoomSceneNode get wrap child)

  mapSceneNodes : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg)
                → List (SceneNode M' Msg') → List (SceneNode M Msg)
  mapSceneNodes get wrap [] = []
  mapSceneNodes get wrap (n ∷ rest) = zoomSceneNode get wrap n ∷ mapSceneNodes get wrap rest

zoomCamera : ∀ {M M'} → (M → M') → Camera M' → Camera M
zoomCamera get (fixed p pos target) = fixed p pos target
zoomCamera get (fromModel projF posF targetF) =
  fromModel (λ m → projF (get m)) (λ m → posF (get m)) (λ m → targetF (get m))

zoomScene : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg)
          → Scene M' Msg' → Scene M Msg
zoomScene get wrap (mkScene cam nodes) =
  mkScene (zoomCamera get cam) (mapSceneNodes get wrap nodes)
