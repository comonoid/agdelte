# WebGL (3D Scene Graphs)

From `Agdelte.WebGL.Types`.

## Overview

The WebGL module provides a declarative 3D scene graph DSL:
- Perspective and orthographic cameras (static or model-reactive)
- Multiple material types (unlit, flat, phong, PBR, textured)
- Light sources (ambient, directional, point, spot)
- Reactive bindings for transforms, materials, lights, and text
- Interactive events via color-picking and ray casting
- Hierarchical groups, MSDF text, and continuous animation
- Scene composition via `zoomScene`

## Math Primitives

Postulate types backed by JS objects:

| Type | Constructor | Description |
|------|-------------|-------------|
| `Vec2` | `vec2 x y` | 2D vector |
| `Vec3` | `vec3 x y z` | 3D vector |
| `Quat` | `quat x y z w` | Quaternion |
| `GlColor` | `rgb r g b` / `rgba r g b a` | GPU color (Float 0-1) |

Constants: `identityQuat`, `white`, `black`.

## Transform

```agda
data Transform : Set where
  mkTransform : Vec3 → Quat → Vec3 → Transform
  --            pos    rot    scale
```

Constant: `identityTransform`.

## Geometry

```agda
data Geometry : Set where
  box      : Vec3 → Geometry           -- dimensions (w, h, d)
  sphere   : Float → Geometry          -- radius
  plane    : Vec2 → Geometry           -- width, height
  cylinder : Float → Float → Geometry  -- radius, height
  custom   : BufferHandle → Geometry   -- arbitrary mesh data
```

## Material

| Constructor | Arguments | Description |
|-------------|-----------|-------------|
| `unlit` | `GlColor` | Flat color, no lighting |
| `flat` | `GlColor` | Ambient-only lighting |
| `phong` | `GlColor Float` | Color + shininess |
| `pbr` | `GlColor Float Float` | Albedo + metallic + roughness |
| `textured` | `TextureHandle GlColor` | Texture + tint |

`loadTexture : String -> TextureHandle` loads a texture by URL.

## Light

| Constructor | Arguments | Description |
|-------------|-----------|-------------|
| `ambient` | `GlColor Float` | Color + intensity |
| `directional` | `GlColor Float Vec3` | Color + intensity + direction |
| `point` | `GlColor Float Vec3 Float` | Color + intensity + position + range |
| `spot` | `GlColor Float Vec3 Vec3 Float Float` | Color + intensity + pos + dir + angle + falloff |

## Camera

```agda
data Projection : Set where
  perspective  : Float → Float → Float → Projection  -- fov, near, far
  orthographic : Float → Float → Float → Projection  -- size, near, far

data Camera (Model : Set) : Set where
  fixed     : Projection → Vec3 → Vec3 → Camera Model
  --                       pos     target
  fromModel : (Model → Projection) → (Model → Vec3) → (Model → Vec3) → Camera Model
  --           projection             position          target
```

`fixed` is static. `fromModel` makes camera reactive (projection, position, and target are functions of model).

## Scene Attributes

Events on 3D objects (via color-picking / ray casting):

| Constructor | Type | Description |
|-------------|------|-------------|
| `onClick` | `Msg` | Click on object |
| `onHover` | `Msg` | Pointer enters object |
| `onLeave` | `Msg` | Pointer leaves object |
| `onScroll` | `Float → Msg` | Scroll wheel on object |
| `onClickAt` | `Vec3 → Msg` | Click with surface coordinates |
| `onDrag` | `Vec3 → Vec3 → Msg` | Drag (start + current position) |
| `focusable` | (flag) | Object can receive keyboard focus |
| `onKeyDown` | `KeyEvent → Msg` | Keyboard event on focused object |
| `onInput` | `String → Msg` | Text input on focused object |
| `transition` | `Duration Easing` | Smooth animated transitions |

## Scene Nodes

```agda
data SceneNode (Model Msg : Set) : Set where
  -- Static
  mesh          : Geometry → Material → List (SceneAttr Msg) → Transform → ...
  group         : Transform → List (SceneNode Model Msg) → ...
  icon          : TextureHandle → Vec2 → List (SceneAttr Msg) → Transform → ...
  text3D        : String → TextStyle → List (SceneAttr Msg) → Transform → ...
  light         : Light → ...

  -- Reactive
  bindTransform : (Model → Transform) → SceneNode Model Msg → ...
  bindMaterial  : (Model → Material) → Geometry → List (SceneAttr Msg) → Transform → ...
  bindText3D    : (Model → String) → TextStyle → List (SceneAttr Msg) → Transform → ...
  bindLight     : (Model → Light) → ...

  -- Animation
  animate       : (Float → Transform) → SceneNode Model Msg → ...
```

## Text Styles

```agda
data TextStyle : Set where
  mkTextStyle : FontRef → Float → GlColor → Align → TextLayout → TextStyle
  --            font      size    color     align   layout
```

Font: `builtin sans`, `builtin mono`, or `custom url`. Align: `left`, `center`, `right`. Layout: `singleLine`, `wrapAt width`, `ellipsis width`.

## Scene

```agda
data Scene (Model Msg : Set) : Set where
  mkScene : Camera Model → List (SceneNode Model Msg) → Scene Model Msg
```

## Composition

| Function | Description |
|----------|-------------|
| `zoomScene get wrap scene` | Remap Model and Msg for scene embedding |
| `zoomCamera get camera` | Remap Model for camera |
| `zoomSceneNode get wrap node` | Remap Model and Msg for a single node |
| `mapSceneAttrs wrap attrs` | Remap Msg for scene attributes |

## DOM Integration

From `Agdelte.Reactive.Node`:

```agda
glCanvas : List (Attr Model Msg) → Scene Model Msg → Node Model Msg
```

Embeds a WebGL canvas in the reactive DOM template. The runtime (`reactive-gl.js`) observes the DOM and initializes WebGL rendering on canvas elements.

## Examples

- `examples/WebGLTest.agda` — basics: perspective, phong, animate, bindTransform, onClick
- `examples/WebGLFullDemo.agda` — comprehensive: all cameras, materials, lights, text, groups, events
