# WebGL objects as first-class Agdelte elements

## Core insight

WebGL bindings follow the same pattern as DOM bindings. The runtime updates
GPU state (uniforms, buffers, transforms) the same way it updates DOM nodes:

```
DOM binding:    Model → String → node.textContent = value
WebGL binding:  Model → Float  → gl.uniformMatrix4fv(loc, value)
WebGL binding:  Model → Vec3   → gl.uniform3f(loc, x, y, z)
```

`updateScope` checks `lastValue`, if changed -- calls a GL command instead of
a DOM mutation. The runtime manages rendering via a three-state loop
(IDLE/DIRTY/ANIMATING) -- static UI renders only on model change, animated
UI runs `requestAnimationFrame` while animations are active (see §4).

## Scene graph as inductive types

Scene = camera + list of nodes. Camera is separate (not a scene node).
Nodes can be static or reactive (bound to model). Full definitions in
"Consolidated type definitions" section below; overview:

```agda
data Scene (Model Msg : Set) : Set₁ where
  mkScene : Camera Model → List (SceneNode Model Msg) → Scene Model Msg

data SceneNode (Model Msg : Set) : Set₁ where
  -- Static
  mesh   : Geometry → Material → List (SceneAttr Model Msg)
         → Transform → SceneNode Model Msg
  group  : Transform → List (SceneNode Model Msg) → SceneNode Model Msg
  light  : Light → SceneNode Model Msg
  text3D : String → TextStyle → Transform → SceneNode Model Msg
  icon   : TextureHandle → Vec2 → Transform → SceneNode Model Msg
  -- Reactive (bound to model)
  bindMesh      : (Model → Transform) → Geometry → Material
                → List (SceneAttr Model Msg) → SceneNode Model Msg
  bindMaterial  : (Model → Material) → Geometry
                → List (SceneAttr Model Msg) → Transform → SceneNode Model Msg
  bindTransform : (Model → Transform) → SceneNode Model Msg → SceneNode Model Msg
  bindText3D    : (Model → String) → TextStyle → Transform → SceneNode Model Msg
  bindLight     : (Model → Light) → SceneNode Model Msg
  -- Animation
  animate : (ℕ → Transform) → SceneNode Model Msg → SceneNode Model Msg

data Geometry : Set where
  box      : Vec3 → Geometry
  sphere   : Float → Geometry
  plane    : Vec2 → Geometry
  cylinder : Float → Float → Geometry
  custom   : BufferHandle → Geometry

data Transform : Set where
  mkTransform : Vec3 → Quat → Vec3 → Transform
  --            pos    rot    scale
```

## Materials and shaders

Materials are the 3D equivalent of CSS -- color, texture, transparency,
lighting response. A basic inductive type:

```agda
data Material : Set where
  unlit    : Color → Material                          -- no lighting
  flat     : Color → Material                          -- ambient only
  phong    : Color → Float → Material                  -- diffuse + specular
  pbr      : Color → Float → Float → Material          -- metallic, roughness
  textured : TextureHandle → MaterialType → Material
  custom   : ShaderHandle → List Uniform → Material
```

No "cascading" or inheritance like CSS. In 3D, material is bound directly to
a mesh -- this is simpler and more natural. Material can be reactive via
`bindMaterial` to change appearance based on model state (e.g. hover).

### GLSL: FFI + DSL

Preferred approach: FFI for arbitrary GLSL strings, with an optional DSL
on top for type safety.

**FFI layer (escape hatch):**

```agda
postulate
  compileShader : String → String → ShaderHandle
  -- vertex source → fragment source → handle

myShader : ShaderHandle
myShader = compileShader vertexSrc fragmentSrc
  where
    vertexSrc = "#version 300 es\nin vec3 pos; uniform mat4 mvp; ..."
    fragmentSrc = "#version 300 es\nprecision mediump float; uniform vec3 color; ..."
```

**DSL layer (type-safe, optional, future):**

```agda
-- Typed shader language embedded in Agda
data Expr : GLType → Set where
  uniform  : String → Expr t
  attr     : String → Expr t
  _+ᵥ_    : Expr Vec3 → Expr Vec3 → Expr Vec3
  _*ₘ_    : Expr Mat4 → Expr Vec4 → Expr Vec4
  sample   : Expr Sampler2D → Expr Vec2 → Expr Vec4
  ...

-- Compiles to GLSL string at Agda level
compileExpr : Expr t → String
```

This is a substantial project on its own. Start with FFI, add DSL
incrementally.

## 3D controls -- native in-scene UI

UI controls live inside the 3D scene, not as DOM overlays. Buttons, inputs,
grids, tree views are 3D meshes with interaction handlers.

```agda
-- 3D button: mesh + label, color changes on hover via bindMaterial
button3D : String → (Model → Material) → Msg → SceneNode Model Msg
button3D label matFn msg =
  group identityTransform
    ( bindMaterial matFn (box (vec3 2 0.8 0.2))
        [ onClick msg, transition (ms 150) easeOut ]
        identityTransform
    ∷ text3D label (mkTextStyle (builtin sans) 0.3 white center singleLine)
        (mkTransform (vec3 0 0 0.15) identityQuat (vec3 1 1 1))
    ∷ [] )

-- 3D input field: mesh + text binding + keyboard capture
input3D : (Model → String) → (String → Msg) → Material → SceneNode Model Msg

-- 3D grid: rows of meshes in 3D space
grid3D : (Model → List Row) → (Row → List (SceneNode Model Msg))
       → GridLayout → SceneNode Model Msg

-- 3D tree view: recursive scene nodes with expand/collapse
tree3D : (Model → Tree A) → (A → SceneNode Model Msg)
       → TreeLayout → SceneNode Model Msg
```

This opens the door for fundamentally new controls that don't exist in 2D:
- Spatial menus (radial, spherical)
- Data visualizations as interactive 3D objects
- Zoomable/navigable information spaces
- Stacked/layered views with depth

### Mouse event handling: two-level system

DOM `onClick` doesn't exist in WebGL. Solution: color picking + ray casting.

**Level 1: Color Picking (always)**

Render scene to offscreen framebuffer where each object = unique flat color
(24 bits = 16M objects). On click/mousemove, `readPixels` → objectID → dispatch.

```glsl
#version 300 es
precision mediump float;
uniform vec3 u_objectId;  // (r, g, b) = ID / 255
out vec4 fragColor;
void main() {
  fragColor = vec4(u_objectId, 1.0);
}
```

Covers 90% of cases:
- `onClick : Msg` — clicked on object
- `onHover : Msg` — cursor entered/left object
- `onScroll : Float → Msg` — scroll over object

Optimizations:
- Async `readPixels` via PBO (WebGL2) — no CPU↔GPU stall
- Render pick buffer only on mousemove, not every frame
- Small viewport around cursor instead of full buffer

**Level 2: Ray Casting (on demand)**

Only when **coordinates on surface** are needed. Color picking gives objectID,
then ray cast **only that object** (not whole scene) → Vec3.

```
Canvas Event
     │
     ▼
  Color Picking → objectID
     │
     ▼
  Object has onClickAt/onDrag?
     │
    Yes → Ray Cast (single object) → Vec3 → dispatch
     │
    No  → dispatch(onClick msg)
```

Key optimization: ray cast one known object = O(K triangles), not O(N scene).

**Agda types:**

```agda
data SceneAttr (Model Msg : Set) : Set₁ where
  -- Color picking only (cheap)
  onClick   : Msg → SceneAttr Model Msg
  onHover   : Msg → SceneAttr Model Msg
  onLeave   : Msg → SceneAttr Model Msg
  onScroll  : (Float → Msg) → SceneAttr Model Msg

  -- Color picking + ray cast (when coordinates needed)
  onClickAt : (Vec3 → Msg) → SceneAttr Model Msg
  onDrag    : (Vec3 → Vec3 → Msg) → SceneAttr Model Msg  -- start, current
```

Runtime checks attribute type and decides if ray cast is needed.

## Runtime architecture

```
reactive.js (existing)            reactive-gl.js (new)
┌───────────────────────┐         ┌──────────────────────────┐
│ DOM scopes            │         │ GL scopes                │
│ text/attr/style       │         │ uniform/buffer/transform │
│ bindings              │         │ bindings                 │
│                       │         │                          │
│ updateScope:          │         │ updateGLScope:           │
│   node.textContent    │         │   gl.uniformMatrix4fv    │
│   el.setAttribute     │         │   gl.bufferSubData       │
│   el.style.setProperty│         │   markDirty()            │
└───────────────────────┘         └──────────────────────────┘
         │                                │
         └──────────┬─────────────────────┘
                    │
              dispatch(msg)
              model = update(msg)(old)
              updateScope(domRoot, ...)
              updateGLScope(glRoot, ...)
```

Both runtimes share the same model and dispatch cycle. A single `update`
function handles both DOM and GL messages. Templates can mix DOM and GL:

```agda
appTemplate : Node Model Msg
appTemplate =
  div []
    ( glCanvas [ width 800, height 600 ] sceneGraph
    ∷ div [ class "toolbar" ]
        ( button [ onClick ResetCamera ] [ text "Reset" ]
        ∷ [] )
    ∷ [] )
```

Where `glCanvas` embeds a WebGL scene inside the DOM tree. The canvas is a
regular DOM element; its contents are managed by `reactive-gl.js`.

## What already works

- `elem "canvas" [...]` creates a canvas element -- trivial
- Binding system (extract + lastValue comparison) -- directly applicable
- Scope-based update skipping -- works for GL scopes too
- Event dispatch via `on` / `onValue` -- canvas click events arrive normally
- `SharedArrayBuffer` for geometry/texture data (see shared-buffers.md)

## What needs building

1. **`reactive-gl.js`** -- GL scope management, GL bindings (uniform, buffer,
   transform), scene graph traversal, draw call generation
2. **Color picker** -- offscreen ID buffer, async readPixels, object registry
3. **Ray caster** (optional) -- for `onClickAt`/`onDrag` with Vec3 coordinates
4. **Agda types** -- `SceneNode`, `Geometry`, `Material`, `Transform`,
   `SceneAttr`, `Light`, `Projection`, `Camera`
5. **GLSL FFI** -- `compileShader` postulate, runtime implementation
6. **Text rendering** -- MSDF font atlas for in-scene text
   (needed for 3D buttons, labels, input fields)
7. **Focus/keyboard** for 3D inputs -- which in-scene element has focus,
   keyboard event routing

## Relation to other ideas

### shared-buffers.md

Geometry and texture data are large buffers. They should live in
`SharedArrayBuffer` / buffer registry, not in the Agda model. The model
stores handles and versions.

### concurrency.md

Heavy operations (geometry generation, texture processing, pick buffer
rendering) can run in workers. The GL runtime on the main thread only
updates uniforms and issues draw calls -- lightweight.

### mutation.md

Transform updates are frequent (every frame for animations). In-place
mutation of transform data avoids allocation pressure in the binding
update loop.

## Gaps to address

Target use case: **3D UI** (like SVG but in 3D), not games or simulations.

### 1. Animation ✓

Two mechanisms for UI animation:

**Transitions (declarative, like CSS):**

```agda
data SceneAttr (Model Msg : Set) : Set₁ where
  ...
  transition : Duration → Easing → SceneAttr Model Msg
```

Runtime interpolates automatically when bound values change (transform or
material). No manual time management needed.

**Continuous animation (binding to time):**

```agda
data SceneNode (Model Msg : Set) : Set₁ where
  ...
  animate : (ℕ → Transform) → SceneNode Model Msg → SceneNode Model Msg
  --        time in ms (ℕ)          wraps existing node
```

Wraps any node. Runtime calls the function each frame, applies result
as transform. For loading spinners, pulsing effects, etc.

**Render loop strategy:**

```
activeAnimations : Int  -- transitions in progress + animate nodes

if activeAnimations > 0:
    requestAnimationFrame(render)
else:
    render only on model change (on-demand)
```

Efficient: static UI doesn't waste CPU/GPU.

### 2. Camera ✓

Both projection types needed:

- **Perspective** — for depth effects ("push to background", parallax)
- **Orthographic** — for predictable sizing, simple layouts

```agda
data Projection : Set where
  perspective  : Float → Float → Float → Projection
  --             fov     near    far
  orthographic : Float → Float → Float → Projection
  --             size    near    far

data Camera (Model : Set) : Set where
  fixed     : Projection → Vec3 → Vec3 → Camera Model
  --                       pos     target
  fromModel : (Model → Projection × Vec3 × Vec3) → Camera Model
  --          bind camera to model state
```

Position and target separate from projection — can animate one without other.

**Typical UI setups:**
- Orthographic top-down: flat panels, 2.5D layouts
- Perspective with low FOV: subtle depth, "card stack" effects
- Perspective with high FOV: dramatic "fly through" transitions

### 3. Lighting ✓

All standard light types supported:

```agda
data Light : Set where
  ambient     : Color → Float → Light
  --            color   intensity
  directional : Color → Float → Vec3 → Light
  --            color   intensity  direction
  point       : Color → Float → Vec3 → Float → Light
  --            color   intensity  position  range
  spot        : Color → Float → Vec3 → Vec3 → Float → Float → Light
  --            color   intensity  pos    dir     angle   falloff
```

Scene can have multiple lights:

```agda
data SceneNode (Model Msg : Set) : Set₁ where
  ...
  light     : Light → SceneNode Model Msg
  bindLight : (Model → Light) → SceneNode Model Msg  -- reactive light
```

**Material response to lighting:**

```agda
data Material : Set where
  unlit    : Color → Material                          -- no lighting, flat color
  flat     : Color → Material                          -- ambient only
  phong    : Color → Float → Material                  -- diffuse + specular
  pbr      : Color → Float → Float → Material          -- metallic, roughness
  textured : TextureHandle → MaterialType → Material   -- texture + lighting model
  custom   : ShaderHandle → List Uniform → Material
```

For simple UI: `unlit` or `flat`. For 3D effects: `phong` or `pbr`.

### 4. Render loop ✓

Each canvas owns its render loop. Three states:

```
IDLE      — no rAF scheduled, waiting for changes
DIRTY     — changes pending, one rAF scheduled
ANIMATING — active animations, rAF loop running
```

**Integration with reactive cycle:**

```
model change →
  updateScope(dom)       // sync, DOM mutations
  updateGLScope(gl)      // sync, uniforms/buffers
  markDirty()            // schedule rAF if not animating

next rAF →
  render()               // draw calls
```

Multiple model changes per tick = one render (batching).

**Implementation:**

```javascript
// per canvas
const state = { mode: 'IDLE', activeAnims: 0 };
let lastTime = 0;

function markDirty() {
  if (state.mode === 'IDLE') {
    state.mode = 'DIRTY';
    requestAnimationFrame(frame);
  }
}

function frame(time) {
  const dt = Math.min(time - lastTime, 100); // cap delta for hidden tabs
  lastTime = time;

  updateGLScopes(dt);
  render();

  if (state.activeAnims > 0) {
    state.mode = 'ANIMATING';
    requestAnimationFrame(frame);
  } else {
    state.mode = 'IDLE';
  }
}
```

**Hidden tab handling:** Browser pauses rAF automatically. On return, delta
capped to 100ms to prevent animation jumps.

### 5. Transparency and draw order ✓

Painter's algorithm — sufficient for UI:

```
render():
  1. Render opaque objects (any order, z-buffer ON, z-write ON)
  2. Sort transparent objects by distance to camera
  3. Render transparent back-to-front (z-write OFF, z-test ON)
```

UI elements typically don't intersect — panels at different Z depths.

**Detecting transparency:** An object is transparent if its material color
has alpha < 1.0. Runtime checks `color.a` to sort into opaque/transparent
buckets.

Edge cases (intersecting transparent objects) are rare in UI. If needed,
split geometry into more triangles to avoid intersection. Document as
known limitation.

### 6. Canvas integration ✓

**Resize handling with HiDPI support:**

```javascript
function setupCanvas(canvas) {
  const resize = () => {
    const dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();

    // Render at device resolution for sharpness
    canvas.width = rect.width * dpr;
    canvas.height = rect.height * dpr;
    gl.viewport(0, 0, canvas.width, canvas.height);

    // Projection uses CSS pixels — physical size stays constant
    updateProjection(rect.width, rect.height);
    resizePickBuffer(canvas.width, canvas.height);
    markDirty();
  };

  new ResizeObserver(resize).observe(canvas);
  resize();
}
```

**Physical size consistency:**
- FullHD laptop (dpr=1): 1920x1080 device pixels
- 4K laptop same size (dpr=2): 3840x2160 device pixels
- Same physical element size on both — 4K just sharper

Projection and scene logic work in CSS pixels (physical units).
Canvas renders at device pixels (more detail on HiDPI).

**Scrollable containers:** Browser clips automatically, no action needed.

**Multiple canvases:** Each has own render loop (decided in §4).

### 7. Text in 3D ✓

**Format: MSDF** (Multi-channel Signed Distance Field)

Better than SDF for sharp corners (M, W, K). Scales without quality loss.

**Font loading strategy:**

1. **Prebuild atlases** for standard fonts (sans, mono) — included in runtime
2. **FFI for custom fonts** — load pregenerated atlas (JSON + PNG)
3. **No runtime generation** — too heavy, requires dependencies

**Types:**

```agda
data BuiltinFont : Set where
  sans : BuiltinFont
  mono : BuiltinFont

data FontRef : Set where
  builtin : BuiltinFont → FontRef
  custom  : String → FontRef  -- pregenerated atlas URL

data Align : Set where
  left : Align
  center : Align
  right : Align

data TextLayout : Set where
  singleLine : TextLayout
  wrapAt     : Float → TextLayout   -- max width, wrap
  ellipsis   : Float → TextLayout   -- max width, truncate with "..."

data TextStyle : Set where
  mkTextStyle : FontRef → Float → Color → Align → TextLayout → TextStyle
  --                      size
```

### 8. Loading assets ✓

**Textures:**

```agda
postulate
  loadTexture : String → TextureHandle  -- URL, PNG/JPG

data Material : Set where
  ...
  textured : TextureHandle → MaterialType → Material
```

Runtime loads image, creates WebGL texture. `MaterialType` controls
lighting model applied to the texture (unlitTex, phongTex, pbrTex, flatTex).

**Icons:**

Two approaches:
1. **Textured quads** — PNG icon on a plane (simple, works now)
2. **Icon font via MSDF** — same mechanism as text (scalable)

```agda
icon : TextureHandle → Vec2 → Transform → SceneNode Model Msg
--                     size
```

**3D models:**

Not needed for UI in first version. Can add later via FFI if needed:

```agda
postulate
  loadGeometry : String → BufferHandle  -- GLTF/OBJ URL (future)
```

### 9. Focus and keyboard ✓

For 3D input fields and interactive elements:

**Focus model:**
- One element has focus at a time (like DOM)
- Tab navigation through focusable elements (depth-first scene order)
- Click on element = focus it
- Escape = blur

**Implementation:**
```javascript
// Canvas must be focusable to receive keyboard events
canvas.setAttribute('tabindex', '0');

// runtime state
let focusedObjectId = null;

function handleKeyboard(event) {
  if (focusedObjectId === null) return;
  const handler = keyboardHandlers.get(focusedObjectId);
  if (handler) handler(event);
}

canvas.addEventListener('keydown', handleKeyboard);
```

**Agda types:**
```agda
data SceneAttr (Model Msg : Set) : Set₁ where
  ...
  focusable  : SceneAttr Model Msg
  onKeyDown  : (KeyEvent → Msg) → SceneAttr Model Msg
  onInput    : (String → Msg) → SceneAttr Model Msg  -- for text input
```

Visual focus indicator: outline, glow, or scale — customizable per element.

---

## Consolidated type definitions

All types in one place for implementation reference:

### Primitives

```agda
-- Math primitives (FFI to JS typed arrays)
postulate
  Float : Set
  Vec2  : Set  -- { x y : Float }
  Vec3  : Set  -- { x y z : Float }
  Vec4  : Set  -- { x y z w : Float }
  Quat  : Set  -- { x y z w : Float } normalized quaternion
  Mat4  : Set  -- 4x4 matrix, column-major
  Color : Set  -- { r g b a : Float } 0-1 range

-- Constructors (FFI)
postulate
  vec2 : Float → Float → Vec2
  vec3 : Float → Float → Float → Vec3
  vec4 : Float → Float → Float → Float → Vec4
  quat : Float → Float → Float → Float → Quat
  rgb  : Float → Float → Float → Color        -- alpha = 1
  rgba : Float → Float → Float → Float → Color

identityQuat : Quat
identityQuat = quat 0 0 0 1

white : Color
white = rgb 1 1 1

black : Color
black = rgb 0 0 0

-- Handles (opaque runtime references)
postulate
  TextureHandle : Set
  ShaderHandle  : Set
  BufferHandle  : Set

-- Shader uniforms (for custom materials)
data UniformValue : Set where
  uFloat : Float → UniformValue
  uVec2  : Vec2 → UniformValue
  uVec3  : Vec3 → UniformValue
  uVec4  : Vec4 → UniformValue
  uMat4  : Mat4 → UniformValue
  uTex   : TextureHandle → UniformValue

record Uniform : Set where
  field
    name  : String
    value : UniformValue

-- Keyboard events
record KeyEvent : Set where
  field
    key     : String   -- "Enter", "a", "ArrowUp", ...
    shift   : Bool
    ctrl    : Bool
    alt     : Bool
```

### Geometry and Transform

```agda
data Geometry : Set where
  box      : Vec3 → Geometry              -- dimensions
  sphere   : Float → Geometry             -- radius
  plane    : Vec2 → Geometry              -- width, height
  cylinder : Float → Float → Geometry     -- radius, height
  custom   : BufferHandle → Geometry      -- arbitrary mesh

data Transform : Set where
  mkTransform : Vec3 → Quat → Vec3 → Transform
  --            position  rotation  scale

identityTransform : Transform
identityTransform = mkTransform (vec3 0 0 0) (quat 0 0 0 1) (vec3 1 1 1)
```

### Materials and Lighting

```agda
data Material : Set where
  unlit    : Color → Material
  flat     : Color → Material
  phong    : Color → Float → Material      -- color, shininess
  pbr      : Color → Float → Float → Material  -- albedo, metallic, roughness
  textured : TextureHandle → MaterialType → Material
  custom   : ShaderHandle → List Uniform → Material

data MaterialType : Set where
  unlitTex : MaterialType
  flatTex  : MaterialType                    -- ambient only
  phongTex : Float → MaterialType            -- shininess
  pbrTex   : Float → Float → MaterialType    -- metallic, roughness

data Light : Set where
  ambient     : Color → Float → Light
  directional : Color → Float → Vec3 → Light
  point       : Color → Float → Vec3 → Float → Light
  spot        : Color → Float → Vec3 → Vec3 → Float → Float → Light
```

### Camera

```agda
data Projection : Set where
  perspective  : Float → Float → Float → Projection  -- fov, near, far
  orthographic : Float → Float → Float → Projection  -- size, near, far

data Camera (Model : Set) : Set where
  fixed     : Projection → Vec3 → Vec3 → Camera Model
  fromModel : (Model → Projection × Vec3 × Vec3) → Camera Model
```

### Animation

```agda
data Easing : Set where
  linear      : Easing
  easeIn      : Easing
  easeOut     : Easing
  easeInOut   : Easing
  cubicBezier : Float → Float → Float → Float → Easing

data Duration : Set where
  ms : ℕ → Duration       -- reuse from Css.Easing
  s  : Float → Duration
```

### Text

```agda
data BuiltinFont : Set where
  sans : BuiltinFont
  mono : BuiltinFont

data FontRef : Set where
  builtin : BuiltinFont → FontRef
  custom  : String → FontRef  -- URL to MSDF atlas

data Align : Set where
  left : Align
  center : Align
  right : Align

data TextLayout : Set where
  singleLine : TextLayout
  wrapAt     : Float → TextLayout
  ellipsis   : Float → TextLayout

data TextStyle : Set where
  mkTextStyle : FontRef → Float → Color → Align → TextLayout → TextStyle
```

### Scene Graph

```agda
data SceneNode (Model Msg : Set) : Set₁ where
  -- Static nodes
  mesh      : Geometry → Material → List (SceneAttr Model Msg)
            → Transform → SceneNode Model Msg
  group     : Transform → List (SceneNode Model Msg) → SceneNode Model Msg
  light     : Light → SceneNode Model Msg
  text3D    : String → TextStyle → Transform → SceneNode Model Msg
  icon      : TextureHandle → Vec2 → Transform → SceneNode Model Msg

  -- Reactive nodes (bound to model)
  bindMesh      : (Model → Transform) → Geometry → Material
                → List (SceneAttr Model Msg) → SceneNode Model Msg
  bindMaterial  : (Model → Material) → Geometry
                → List (SceneAttr Model Msg) → Transform → SceneNode Model Msg
  bindText3D    : (Model → String) → TextStyle → Transform → SceneNode Model Msg
  bindLight     : (Model → Light) → SceneNode Model Msg
  bindTransform : (Model → Transform) → SceneNode Model Msg → SceneNode Model Msg

  -- Continuous animation
  animate : (ℕ → Transform) → SceneNode Model Msg → SceneNode Model Msg

data SceneAttr (Model Msg : Set) : Set₁ where
  -- Events (color picking)
  onClick   : Msg → SceneAttr Model Msg
  onHover   : Msg → SceneAttr Model Msg
  onLeave   : Msg → SceneAttr Model Msg
  onScroll  : (Float → Msg) → SceneAttr Model Msg

  -- Events (color picking + ray cast)
  onClickAt : (Vec3 → Msg) → SceneAttr Model Msg
  onDrag    : (Vec3 → Vec3 → Msg) → SceneAttr Model Msg

  -- Animation
  transition : Duration → Easing → SceneAttr Model Msg

  -- Focus/keyboard
  focusable : SceneAttr Model Msg
  onKeyDown : (KeyEvent → Msg) → SceneAttr Model Msg
  onInput   : (String → Msg) → SceneAttr Model Msg

data Scene (Model Msg : Set) : Set₁ where
  mkScene : Camera Model → List (SceneNode Model Msg) → Scene Model Msg
```

### Top-level integration

```agda
-- Embed WebGL canvas in DOM tree
glCanvas : List (Attr Model Msg) → Scene Model Msg → Node Model Msg
```

---

## Built-in shaders

Runtime includes pre-written GLSL programs for each material type. User
never writes GLSL unless using `custom` material.

| Material | Vertex shader | Fragment shader |
|----------|--------------|-----------------|
| `unlit` | MVP transform | `fragColor = u_color` |
| `flat` | MVP + normal → varying | ambient light × color |
| `phong` | MVP + normal + viewDir | Blinn-Phong: ambient + diffuse + specular |
| `pbr` | MVP + normal + viewDir + TBN | Cook-Torrance BRDF |
| `textured` | MVP + UV pass-through | Same as above but sample texture |
| `msdf` (text) | MVP + UV | MSDF distance field → alpha |
| `picking` | MVP only | `fragColor = vec4(u_objectId, 1.0)` |

All shaders share a common uniform block:

```glsl
// Vertex common
uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_projection;

// Fragment common
uniform vec3 u_cameraPos;

// Per-material
uniform vec4 u_color;         // unlit, flat, phong
uniform float u_shininess;    // phong
uniform float u_metallic;     // pbr
uniform float u_roughness;    // pbr

// Lighting (array, max N lights)
uniform int u_numLights;
uniform int u_lightType[N];   // 0=ambient, 1=dir, 2=point, 3=spot
uniform vec3 u_lightColor[N];
uniform float u_lightIntensity[N];
uniform vec3 u_lightPosOrDir[N];
uniform float u_lightRange[N];
uniform float u_lightAngle[N];
uniform float u_lightFalloff[N];
```

## Transition interpolation

When a `transition` attribute is present and a binding value changes
(transform via `bindTransform`/`bindMesh`, or material via `bindMaterial`):

```
Vec3 (position, scale): linear interpolation (LERP)
  result = a + (b - a) × t

Quat (rotation): spherical linear interpolation (SLERP)
  result = slerp(a, b, t)

t = easing(elapsed / duration)
```

**Easing functions** map `[0,1] → [0,1]`:
- `linear`: `t`
- `easeIn`: `t²`
- `easeOut`: `1 - (1-t)²`
- `easeInOut`: `t < 0.5 ? 2t² : 1 - (-2t+2)²/2`
- `cubicBezier(x1,y1,x2,y2)`: standard CSS cubic-bezier

**Material transitions** (for `bindMaterial`):
- Color: LERP each channel (r, g, b, a)
- Shininess/metallic/roughness: LERP
- Cannot transition between different material types (e.g. phong → unlit)

## Agda to JS compilation

Agda scene graph compiles via MAlonzo to JS objects:

```
Agda                          JS runtime
─────                         ──────────
SceneNode constructors   →    { tag: "mesh", geometry: {...}, ... }
SceneAttr constructors   →    { tag: "onClick", msg: 42 }
Scene                    →    { camera: {...}, nodes: [...] }
Binding functions        →    JS functions: model → value
```

**reactive-gl.js receives a JS scene graph object** and:

1. **Walks the tree** creating WebGL resources:
   - Geometry → VBO + VAO
   - Material → shader program + uniforms
   - Transform → model matrix (Float32Array)

2. **Registers bindings** (same pattern as DOM):
   - `bindTransform` → scope with extract function + lastValue
   - `bindMaterial` → scope with extract function + lastValue
   - `bindText3D` → scope with extract function + lastValue

3. **Assigns object IDs** for color picking:
   - Each mesh/text node with event attrs gets unique 24-bit ID
   - Stored in `objectRegistry: Map<int, { attrs, geometry }>`

4. **On model change** (`updateGLScope`):
   - Walk scopes, call extract(model), compare with lastValue
   - If changed: update uniform/buffer, markDirty()

5. **On render** (`frame`):
   - Set camera uniforms (view, projection matrices)
   - For each node: set model matrix, bind VAO, set material uniforms, drawElements
   - Opaque first (any order), then transparent (sorted)
   - If pick buffer dirty: render picking pass

---

## Implementation order

### Phase 1: Minimal viable (static scene)
1. `reactive-gl.js` skeleton — canvas setup, WebGL context
2. Basic geometry — box, plane
3. Unlit material — flat color, no lighting
4. Fixed orthographic camera
5. Static `mesh` and `group` nodes
6. Compile Agda scene → JS scene graph

**Milestone:** Render colored boxes on screen.

### Phase 2: Reactivity
1. `bindTransform` — transform from model
2. Scope-based updates — only update changed nodes
3. `markDirty()` integration with reactive.js
4. Basic transitions — linear interpolation

**Milestone:** Boxes move when model changes.

### Phase 3: Interaction
1. Color picking framebuffer
2. Object ID registry
3. `onClick` / `onHover` events
4. Mouse event handling

**Milestone:** Click on box → dispatch message.

### Phase 4: Text and UI
1. MSDF shader and rendering
2. Built-in font atlas (sans)
3. `text3D` node
4. Focus management
5. `onKeyDown` / `onInput`

**Milestone:** Clickable 3D buttons with labels.

### Phase 5: Polish
1. All geometry types (sphere, cylinder)
2. Lighting (phong material)
3. Perspective camera
4. All easing functions
5. Texture loading
6. Custom fonts

**Milestone:** Full-featured 3D UI.

---

## Complete example

```agda
module Example3DUI where

-- Model
data BtnId : Set where
  plusBtn minusBtn : BtnId

record Model : Set where
  field
    count   : Nat
    hovered : Maybe BtnId

data Msg : Set where
  Increment : Msg
  Decrement : Msg
  Hover     : BtnId → Msg
  Unhover   : Msg

-- Update
update : Msg → Model → Model
update Increment   m = record m { count = count m + 1 }
update Decrement   m = record m { count = count m ∸ 1 }
update (Hover id)  m = record m { hovered = just id }
update Unhover     m = record m { hovered = nothing }

-- Styles
normalStyle : Material
normalStyle = phong (rgb 0.2 0.5 0.8) 32.0

hoveredStyleOf : Material
hoveredStyleOf = phong (rgb 0.4 0.7 1.0) 64.0

-- Button material changes on hover via bindMaterial
btnMaterial : BtnId → Model → Material
btnMaterial id m with hovered m
... | just h  = if h ≡ id then hoveredStyleOf else normalStyle
... | nothing = normalStyle

button3D : String → Vec3 → BtnId → Msg → SceneNode Model Msg
button3D label pos id msg =
  group (mkTransform pos identityQuat (vec3 1 1 1))
    ( bindMaterial (btnMaterial id) (box (vec3 2 0.8 0.2))
        [ onClick msg
        , onHover (Hover id)
        , onLeave Unhover
        , transition (ms 150) easeOut
        ]
        identityTransform
    ∷ text3D label
        (mkTextStyle (builtin sans) 0.3 white center singleLine)
        (mkTransform (vec3 0 0 0.15) identityQuat (vec3 1 1 1))
    ∷ [] )

counterDisplay : SceneNode Model Msg
counterDisplay =
  bindText3D (λ m → show (count m))
    (mkTextStyle (builtin mono) 0.5 white center singleLine)
    (mkTransform (vec3 0 1 0) identityQuat (vec3 1 1 1))

scene : Scene Model Msg
scene = mkScene
  (fixed (orthographic 10 0.1 100) (vec3 0 0 5) (vec3 0 0 0))
  ( counterDisplay
  ∷ button3D "+" (vec3 2 0 0) plusBtn Increment
  ∷ button3D "−" (vec3 -2 0 0) minusBtn Decrement
  ∷ light (ambient white 0.3)
  ∷ light (directional white 0.7 (vec3 0 1 1))
  ∷ [] )

-- DOM template with embedded WebGL
template : Node Model Msg
template =
  div [ class "app" ]
    ( glCanvas [ width 800, height 600 ] scene
    ∷ div [ class "status" ]
        ( bindText (λ m → "Count: " ++ show (count m))
        ∷ [] )
    ∷ [] )
```

---

## Codebase alignment issues

The types in this document were designed in isolation. Comparing with the
actual Agdelte codebase reveals 10 mismatches that must be resolved before
implementation. Each entry lists the discrepancy, the existing code, and a
proposed resolution.

### A1. Duration: Float vs ℕ

**Problem:** webgl.md defines `ms : Float → Duration`, but the codebase uses
`ms : ℕ → Duration` everywhere.

**Existing code** (`Css/Easing.agda:48-49`):
```agda
data Duration : Set where
  ms : ℕ → Duration
  s  : Float → Duration
```

**In this doc** (Animation section, consolidated types):
```agda
data Duration : Set where
  ms : Float → Duration    -- WRONG: should be ℕ
  s  : Float → Duration
```

**Resolution:** Use existing `Duration` from `Css.Easing`. Change `ms 150` in
examples to `ms 150` (already works — ℕ literal). No new Duration type needed.

### A2. Easing already exists

**Problem:** webgl.md redefines `Easing` from scratch, missing constructors
that already exist.

**Existing code** (`Css/Easing.agda:28-31`):
```agda
data Easing : Set where
  ease linear easeIn easeOut easeInOut : Easing
  cubicBezier : Float → Float → Float → Float → Easing
  raw         : String → Easing
```

Plus `Float → Float` evaluation functions (`linearFn`, `easeInFn`, `easeOutFn`,
`easeInOutFn`).

**In this doc:** Redefines Easing without `ease` and `raw` constructors.

**Resolution:** Import `Easing` and `Duration` from `Css.Easing`. For WebGL
transitions, the runtime evaluates easing via the existing `*Fn` functions.
No new Easing type needed.

### A3. Tween/Spring already exist

**Problem:** webgl.md defines `transition` from scratch. The codebase already
has a full Tween system (`Anim/Tween.agda`) with elapsed/duration tracking,
easing, lerp, retarget, and a Spring system (`Anim/Spring.agda`) with physics
simulation, presets (gentle/snappy/bouncy), and stable fixed-step ticking.

**Existing code** (`Anim/Tween.agda:31-39`):
```agda
record Tween (A : Set) : Set where
  constructor mkTween
  field
    elapsed  : ℕ           -- ms elapsed so far
    duration : ℕ           -- total ms
    from     : A
    to       : A
    easing   : Float → Float
    lerp     : A → A → Float → A
```

`retargetTween` snapshots current value as new start — exactly what's needed
when a binding value changes mid-transition.

**Existing code** (`Anim/Spring.agda:30-38`):
```agda
record Spring : Set where
  constructor mkSpring
  field
    position velocity target stiffness damping : Float
```

With `tickSpringStable` (subdivided Euler for large dt) and presets
(`gentle`, `snappy`, `bouncy`).

**Resolution:** WebGL transitions should use `Tween` internally. The runtime
creates a `Tween Vec3` for position, `Tween Vec3` for scale, SLERP tween
for rotation. `retargetTween` handles interruptions. Optionally allow
`spring` attribute alongside `transition` for spring-driven animations.

### A4. Node is the universal type

**Problem:** Everything in Agdelte composes to `Node M Msg`. SVG elements are
just `elem "circle"`, `elem "rect"` etc. — all `Node M Msg`. But webgl.md
introduces a separate `SceneNode` type that doesn't compose with `Node`.

**Existing pattern** (`Svg/Elements.agda`):
```agda
circle' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
circle' = elem "circle"
```

SVG is fully embedded in the Node tree. WebGL should follow the same pattern.

**Resolution:** `glCanvas` is a `Node` that embeds a `Scene`. This is already
shown in the doc (`glCanvas : List (Attr Model Msg) → Scene Model Msg → Node
Model Msg`). The `SceneNode` type is intentionally separate because WebGL
scene graph nodes are NOT DOM nodes — they're GPU objects managed by
`reactive-gl.js`. The `glCanvas` bridge is the integration point.

This is acceptable: SVG works because SVG elements ARE DOM nodes. WebGL meshes
are not. The key requirement is that `glCanvas` returns `Node M Msg` so it
composes with the rest of the tree. ✓ Already satisfied.

### A5. Binding record vs raw functions

**Problem:** The codebase uses `Binding` records with `extract` + `equals`
fields for change detection. webgl.md uses raw functions `(Model → Transform)`.

**Existing code** (`Reactive/Node.agda:27-32`):
```agda
record Binding (Model : Set) (A : Set) : Set where
  constructor mkBinding
  field
    extract : Model → A
    equals  : A → A → Bool
```

**In this doc:**
```agda
bindTransform : (Model → Transform) → SceneNode Model Msg → SceneNode Model Msg
```

**Resolution:** The Agda types can stay as `(Model → X)` — this is the user-
facing API. The **runtime** (`reactive-gl.js`) wraps these in binding objects
with `lastValue` comparison, just like `reactive.js` does for DOM bindings.
The `equals` for WebGL types is structural (compare floats in typed arrays).

No change needed in Agda types. Runtime implementation detail.

### A6. SceneAttr vs Attr

**Problem:** `Attr` is the existing attribute type with `on`/`onValue`/`attr`/
`style` etc. webgl.md defines a separate `SceneAttr` type.

**Existing code** (`Reactive/Node.agda:68-82`):
```agda
data Attr (Model Msg : Set) : Set₁ where
  attr      : String → String → Attr Model Msg
  attrBind  : String → Binding Model String → Attr Model Msg
  on        : String → Msg → Attr Model Msg
  onValue   : String → (String → Msg) → Attr Model Msg
  style     : String → String → Attr Model Msg
  styleBind : String → Binding Model String → Attr Model Msg
```

**Resolution:** `SceneAttr` is intentionally separate. `Attr` is for DOM
attributes (strings, CSS styles, DOM events). `SceneAttr` is for GPU objects
(transitions that interpolate transforms, events dispatched via color picking,
not DOM event listeners). They live in different worlds.

However, the **event helpers** (`onClick`, `onHover`) could follow the naming
convention from `Attr`. In the codebase, `onClick` is a smart constructor
(`Node.agda:176`): `onClick = on "click"`. For WebGL, `onClick` is a
`SceneAttr` constructor — different type, same name. This is fine: they're
in different modules.

No structural change needed. Separate `SceneAttr` is correct.

### A7. Color: two different types

**Problem:** `Css/Color.agda` defines `Color` as CSS color values (`hex`, `rgb`
with ℕ 0-255, `rgba`, `hsl`, `named`, `var`, `raw`). webgl.md postulates a
separate `Color` as GPU color values (`rgb : Float → Float → Float → Color`
with floats 0-1).

**Existing code** (`Css/Color.agda:21-28`):
```agda
data Color : Set where
  hex  : String → Color               -- "#ff0000"
  rgb  : ℕ → ℕ → ℕ → Color
  rgba : ℕ → ℕ → ℕ → Float → Color
  hsl  : ℕ → ℕ → ℕ → Color
  named : String → Color              -- "red"
  var   : String → Color              -- CSS custom property
  raw   : String → Color
```

**In this doc:**
```agda
postulate
  Color : Set
  rgb  : Float → Float → Float → Color        -- 0.0-1.0
  rgba : Float → Float → Float → Float → Color
```

**Resolution:** These are genuinely different types. CSS Color uses ℕ (0-255)
and supports CSS-specific constructors (hex, hsl, named, var). WebGL Color
uses Float (0.0-1.0) and maps directly to `gl.uniform3f`. Rename the WebGL
type to `GlColor` or keep it in a separate module (`WebGL.Color`). Do NOT
reuse `Css.Color` — the representations are incompatible.

Alternatively: add `glRgb : Float → Float → Float → Color` constructor to
`Css.Color` and have the runtime branch on constructor when rendering. This
unifies the type but adds GPU-specific constructors to a CSS module. Probably
cleaner to keep them separate.

**Decision:** Separate types. `Css.Color` is a CSS serialization format
(ℕ 0–255, hex, hsl, named, var → `showColor → String`). `WebGL.Color` is a
GPU runtime value (Float 0–1 → `gl.uniform3f`). Different representations,
different semantics, no benefit to unifying.

### A8. Time as ℕ everywhere

**Problem:** Codebase uses ℕ (milliseconds) for all time values. Tween:
`elapsed : ℕ`, `duration : ℕ`. Spring: `tickSpring : Spring → ℕ → Spring`.
But webgl.md uses Float for time in `animate`:

```agda
animate : (Float → Transform) → SceneNode Model Msg → SceneNode Model Msg
--        time in ms (ℕ)
```

**Resolution:** Change `animate` signature to use ℕ (milliseconds):
```agda
animate : (ℕ → Transform) → SceneNode Model Msg → SceneNode Model Msg
--        time in ms
```

This is consistent with the rest of the codebase. The runtime passes
`performance.now()` truncated to ℕ. If fractional time is needed for
smooth animation math, the user converts inside the function:
`λ ms → let t = toFloat ms / 1000.0 in ...`

### A9. Missing zoomNode integration

**Problem:** `zoomNode` (`Node.agda:321`) is the core composition mechanism.
It remaps model/message types AND adds automatic `scopeProj` for subtree
skipping. webgl.md doesn't discuss how `Scene` composes with `zoomNode`.

**Existing code** (`Reactive/Node.agda:321-322`):
```agda
zoomNode : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNode get wrap node = scopeProj get (zoomNode' get wrap node)
```

Plus `zoomNodeL` (with Lens + Prism), `zoomNodeS` (with fingerprint).

**Resolution:** Add `zoomScene` for remapping Scene model/message types:

```agda
zoomScene : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg)
          → Scene M' Msg' → Scene M Msg

zoomSceneL : ∀ {M M' Msg Msg'} → Lens M M' → Prism Msg Msg'
           → Scene M' Msg' → Scene M Msg
```

This allows embedding a WebGL component that has its own Model/Msg types
inside a parent app. `glCanvas attrs (zoomScene get wrap childScene)`.
Essential for component composition.

### A10. Events pattern

**Problem:** SVG events (`Svg/Events.agda`) are smart constructors that return
`Attr M Msg` via `on`/`onValue`. Example:

```agda
onSvgClick : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgClick handler = onValue "click" (λ s → handler (parsePoint s))
```

WebGL events are `SceneAttr` constructors. There's no `on`/`onValue` pattern.

**Resolution:** As discussed in A6, `SceneAttr` events are dispatched via
color picking, not DOM events. The `on "click"` pattern doesn't apply because
there's no DOM element per mesh. However, the **canvas-level** DOM events
(actual click/mousemove on the `<canvas>`) DO use `on`/`onValue` internally
in the runtime. The `SceneAttr` is a higher-level abstraction that the runtime
translates to canvas event handlers + color picking + optional ray casting.

No change needed. The pattern difference is inherent to the architecture.

---

## Open questions (deferred)

For future consideration, not blocking initial implementation:

1. **WebGL context loss** — save scene state, recreate resources on restore.
   Not critical for UI (rare event).

2. **Instancing** — useful for particle effects, data viz with many items.
   Add `instanced : Geometry → List Transform → SceneNode` later.

3. **WebXR** — separate integration, different input model.
   Future project.

4. **LOD** — not needed for UI scale scenes.
   Defer indefinitely.

5. **WebGL version** — start with WebGL2 only (async readPixels needed).
   WebGL1 fallback if demand exists. WebGPU as future evolution.
