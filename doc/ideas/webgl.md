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
a DOM mutation. The GPU redraws automatically on the next frame. No separate
render loop logic needed -- the GPU handles redraw, the runtime handles
state changes.

## Scene graph as inductive types

```agda
data SceneNode (Model Msg : Set) : Set₁ where
  mesh      : Geometry → Material → Transform → SceneNode Model Msg
  group     : Transform → List (SceneNode Model Msg) → SceneNode Model Msg
  light     : LightType → SceneNode Model Msg
  camera    : CameraParams → SceneNode Model Msg
  -- Reactive bindings -- same idea as DOM bind
  bindMesh  : Binding Model Transform → Geometry → Material → SceneNode Model Msg
  bindLight : Binding Model LightParams → LightType → SceneNode Model Msg

data Geometry : Set where
  box      : Vec3 → Geometry
  sphere   : Float → Geometry
  plane    : Vec2 → Geometry
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
  flat     : Color → Material
  phong    : Color → Shininess → Material
  textured : TextureHandle → Material
  custom   : ShaderHandle → List Uniform → Material
```

No "cascading" or inheritance like CSS. In 3D, material is bound directly to
a mesh -- this is simpler and more natural.

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
    vertexSrc = "attribute vec3 pos; uniform mat4 mvp; ..."
    fragmentSrc = "precision mediump float; uniform vec3 color; ..."
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
-- 3D button: a mesh that responds to ray-cast clicks
button3D : String → Material → Msg → SceneNode Model Msg
button3D label mat msg =
  mesh (textGeometry label) mat identityTransform
    -- onClick is resolved via ray casting, not DOM events

-- 3D input field: mesh + text binding + keyboard capture
input3D : Lens Model String → Material → SceneNode Model Msg

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

### Click handling via ray casting

DOM `onClick` doesn't exist in WebGL. The equivalent:

1. On canvas click, get (x, y) screen coordinates
2. Unproject through camera → ray in world space
3. Intersect ray with scene geometry (bounding boxes, then precise)
4. Hit object has an associated `Msg` → `dispatch`

This is the "onClick solved, long to describe" part. Implementation is
runtime-level (JS), not Agda-level. The Agda side just declares:

```agda
data SceneAttr (Model Msg : Set) : Set₁ where
  onClick    : Msg → SceneAttr Model Msg
  onHover    : Msg → SceneAttr Model Msg
  onDrag     : (Vec3 → Msg) → SceneAttr Model Msg  -- drag delta
  onScroll   : (Float → Msg) → SceneAttr Model Msg
```

The runtime maintains a spatial index (BVH or octree) for efficient
ray casting. Updated when transforms change (via bindings).

## Runtime architecture

```
reactive.js (existing)          reactive-gl.js (new)
┌─────────────────────┐         ┌──────────────────────────┐
│ DOM scopes           │         │ GL scopes                │
│ text/attr/style      │         │ uniform/buffer/transform │
│ bindings             │         │ bindings                 │
│                      │         │                          │
│ updateScope:         │         │ updateGLScope:           │
│   node.textContent   │         │   gl.uniformMatrix4fv    │
│   el.setAttribute    │         │   gl.bufferSubData       │
│   el.style.setProperty         │   recalc bounding box    │
└─────────────────────┘         └──────────────────────────┘
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
2. **Ray caster** -- unproject + BVH/octree intersection for click handling
3. **Agda types** -- `SceneNode`, `Geometry`, `Material`, `Transform`,
   `SceneAttr`, `LightType`, `CameraParams`
4. **GLSL FFI** -- `compileShader` postulate, runtime implementation
5. **Text rendering** -- SDF or MSDF font atlas for in-scene text
   (needed for 3D buttons, labels, input fields)
6. **Focus/keyboard** for 3D inputs -- which in-scene element has focus,
   keyboard event routing

## Relation to other ideas

### shared-buffers.md

Geometry and texture data are large buffers. They should live in
`SharedArrayBuffer` / buffer registry, not in the Agda model. The model
stores handles and versions.

### concurrency.md

Heavy operations (BVH rebuild, geometry generation, physics) should run in
workers. The GL runtime on the main thread only updates uniforms and
issues draw calls -- lightweight.

### mutation.md

Transform updates are frequent (every frame for animations). In-place
mutation of transform data avoids allocation pressure in the binding
update loop.

## Open questions

1. How to handle WebGL context loss and restoration?
2. Should the scene graph support instancing (many copies of same geometry
   with different transforms)?
3. How to integrate with WebXR for VR/AR?
4. Level-of-detail (LOD) -- should it be declarative in the scene graph
   or runtime-managed?
5. Should `reactive-gl.js` use WebGL2 only, or support WebGL1 fallback?
   WebGPU as future target?
