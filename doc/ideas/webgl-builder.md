# WebGL Builder Library (Agdelte.WebGL.Builder)

A helper library for building complex interactive 3D objects.
A layer between low-level `Agdelte.WebGL.Types` and high-level `Agdelte.WebGL.Controls`.

## Problem Statement

### Current State

Currently `Agdelte.WebGL.Types` provides:
- Primitives: `box`, `sphere`, `cylinder`, `plane`
- `mesh` — primitive + material + attributes + transform
- `group` — grouping multiple `SceneNode`s
- Events: `glClick`, `glHover`, `glLeave`, `glDrag`, etc.

### Problems

**1. Building composite objects is cumbersome**

To create a button from frame + background + text:
```agda
-- Currently: verbose, lots of boilerplate
button3D = group identityTransform
  ( mesh (box frameSize) frameMaterial [] frameTransform
  ∷ mesh (box bgSize) bgMaterial [] bgTransform
  ∷ text3D "Click" style [] textTransform
  ∷ [] )
```

**2. Events must be assigned to each mesh separately**

```agda
-- Want: one onClick for the entire button
-- Currently: must repeat on each mesh
button3D = group identityTransform
  ( mesh frame frameMat [ glClick ButtonClicked, glHover ButtonHover ] ...
  ∷ mesh bg bgMat [ glClick ButtonClicked, glHover ButtonHover ] ...  -- duplication!
  ∷ mesh text textMat [ glClick ButtonClicked, glHover ButtonHover ] ... -- again!
  ∷ [] )
```

**3. No CSG or complex geometry**

Cannot subtract one shape from another, create rounded corners, or build from profiles.
Everything must be done manually through custom buffers.

**4. No layout system**

Arranging 10 elements in a row with equal spacing requires manually calculating transforms.

**5. Performance: many draw calls**

Each `mesh` = separate draw call. 100 buttons = 300+ draw calls.
No instancing, no geometry merging.

## Library Goals

1. **Declarative construction** of complex objects from simple ones
2. **Unified events** on groups of elements (like in HTML/SVG)
3. **CSG and procedural geometry** (extrude, revolve, boolean ops)
4. **Layout system** for 3D (stack, grid, ring, etc.)
5. **Optimization** through geometry merging and instancing
6. **Hit testing** as good as HTML — accurate, with nesting support

---

## Part 1: Geometry Composition

### 1.1 Mesh Combining

```agda
-- Combine multiple geometries into one (single draw call)
-- All must use the same material!
combineGeometry : List (Geometry × Transform) → Geometry

-- Example: frame from 4 boxes
frameGeometry : Float → Float → Float → Geometry
frameGeometry w h thickness =
  combineGeometry
    ( (box (vec3 w thickness thickness), translate 0 (h/2) 0)
    ∷ (box (vec3 w thickness thickness), translate 0 (-h/2) 0)
    ∷ (box (vec3 thickness h thickness), translate (w/2) 0 0)
    ∷ (box (vec3 thickness h thickness), translate (-w/2) 0 0)
    ∷ [] )
```

**Questions to explore:**
- How to combine UV coordinates?
- How to handle different materials? (texture atlas?)
- How to preserve separate hit testing for parts?

### 1.2 CSG Operations

```agda
-- Boolean operations
union : Geometry → Geometry → Geometry
subtract : Geometry → Geometry → Geometry
intersect : Geometry → Geometry → Geometry

-- Example: button with rounded corners
roundedBox : Vec3 → Float → Geometry
roundedBox size radius = ... -- CSG: box + cylinders + spheres at corners

-- Example: hole
plateWithHole : Geometry
plateWithHole = subtract (box plateSize) (cylinder holeRadius plateThickness)
```

**Questions to explore:**
- CSG algorithm (BSP trees? exact mesh boolean?)
- Performance — compile time or runtime?
- Normals after CSG operations
- Can this be done in Agda or need JS helper?

### 1.3 Procedural Geometry

```agda
-- Extrude 2D profile
extrude : Path2D → Float → Geometry
extrude profile depth = ...

-- With beveled edges
extrudeBevel : Path2D → Float → Float → ℕ → Geometry
extrudeBevel profile depth bevelSize bevelSegments = ...

-- Revolve profile around axis
revolve : Path2D → Axis → ℕ → Geometry
revolve profile axis segments = ...

-- Loft between profiles (morphing)
loft : List (Path2D × Float) → Geometry  -- (profile, position along axis)

-- Sweep along 3D path
sweep : Path2D → Path3D → ℕ → Geometry
sweep profile path segments = ...

-- Text as geometry
textGeometry : String → Font → Float → Geometry
```

**Questions to explore:**
- Path2D format — reuse SVG path?
- How to specify Font for 3D text?
- Triangulation of arbitrary polygons (ear clipping?)
- UV generation for procedural geometry

### 1.4 Arbitrary Geometry (Low Level)

```agda
-- Vertex with attributes
record Vertex : Set where
  constructor mkVertex
  field
    position : Vec3
    normal   : Maybe Vec3        -- Nothing = auto-calculate
    uv       : Maybe Vec2
    color    : Maybe Color

-- Triangle (basic WebGL primitive)
Triangle : Set
Triangle = Vertex × Vertex × Vertex

-- Geometry from triangles (lowest level)
fromTriangles : List Triangle → Geometry

-- Quad (automatically split into 2 triangles)
Quad : Set
Quad = Vertex × Vertex × Vertex × Vertex  -- CCW order

fromQuads : List Quad → Geometry

-- Polygon (arbitrary polygon, triangulated)
fromPolygon : List Vertex → Geometry       -- convex or concave
fromPolygons : List (List Vertex) → Geometry

-- With holes (polygon with holes)
fromPolygonWithHoles : List Vertex → List (List Vertex) → Geometry
```

**Indexed geometry (more efficient):**

```agda
-- Vertices + indices (standard approach)
record IndexedMesh : Set where
  constructor mkIndexedMesh
  field
    vertices : List Vertex
    indices  : List (ℕ × ℕ × ℕ)  -- triangles as vertex indices

fromIndexed : IndexedMesh → Geometry

-- Build indexed mesh from triangles (with welding of identical vertices)
toIndexed : List Triangle → Float → IndexedMesh  -- tolerance for welding
```

**Strips and Fans (less data):**

```agda
-- Triangle strip: v0-v1-v2, v1-v2-v3, v2-v3-v4, ...
fromTriangleStrip : List Vertex → Geometry

-- Triangle fan: v0-v1-v2, v0-v2-v3, v0-v3-v4, ... (for convex shapes)
fromTriangleFan : Vertex → List Vertex → Geometry  -- center + perimeter

-- Line strip (for wireframe)
fromLineStrip : List Vec3 → Geometry
fromLineLoop : List Vec3 → Geometry
```

**Normal Generation:**

```agda
-- Flat normals (each triangle has its own normal)
flatNormals : Geometry → Geometry

-- Smooth normals (averaged across vertices)
smoothNormals : Geometry → Geometry

-- Smoothing with angle threshold (sharp edges preserved)
smoothNormalsAngle : Float → Geometry → Geometry  -- angle in radians
```

**Modifiers:**

```agda
-- Transform all vertices
transformGeometry : Transform → Geometry → Geometry

-- Invert normals (flip inside out)
flipNormals : Geometry → Geometry

-- Subdivision (Catmull-Clark or Loop)
subdivide : ℕ → Geometry → Geometry

-- Simplification (reduce polycount)
simplify : Float → Geometry → Geometry  -- target ratio (0-1)

-- Weld close vertices
weldVertices : Float → Geometry → Geometry  -- tolerance
```

**Questions to explore:**
- Triangulation of concave polygons — ear clipping or other algorithm?
- Polygons with holes — how to handle?
- Storage format — directly to Float32Array or List in Agda?
- Performance — where is the boundary between Agda and JS?

### 1.5 Parametric Primitives

```agda
-- More primitives with parameters
roundedBox : Vec3 → Float → ℕ → Geometry          -- size, radius, segments
capsule : Float → Float → ℕ → Geometry            -- radius, height, segments
torus : Float → Float → ℕ → ℕ → Geometry          -- major, minor, segments
cone : Float → Float → ℕ → Geometry               -- radius, height, segments
pyramid : Float → Float → ℕ → Geometry            -- base, height, sides
prism : Path2D → Float → Geometry                 -- arbitrary cross-section
tube : Path3D → Float → ℕ → Geometry              -- path, radius, segments
lathe : List (Float × Float) → ℕ → Geometry       -- profile points (r, y), segments
```

---

## Part 2: Interactive Groups

### 2.1 Group with Shared Events

```agda
-- Group where events apply to all children
interactiveGroup : ∀ {M A}
                 → List (SceneAttr A)        -- events for entire group
                 → List (SceneNode M A)      -- children
                 → Transform
                 → SceneNode M A

-- Example: button
button3D label onClick =
  interactiveGroup
    [ glClick onClick, glHover (Hover True), glLeave (Hover False) ]
    ( mesh bgGeometry bgMaterial [] identityTransform
    ∷ text3D label style [] textTransform
    ∷ [] )
    identityTransform
```

**Questions to explore:**
- Runtime: how to determine that click hit any child of the group?
- Pick buffer: one ID per group or per mesh?
- Nested groups: event bubbling?
- stopPropagation equivalent?

### 2.2 Named Parts

```agda
-- Give a name to part of an object (for precise hit testing)
named : String → SceneNode M A → SceneNode M A

-- Event on specific named part
onPartClick : String → A → SceneAttr A
onPartHover : String → A → SceneAttr A

-- Example: slider with separate handle
slider3D value onChange =
  interactiveGroup [ glDrag onDrag ]
    ( named "track" (mesh trackGeom trackMat [] ...)
    ∷ named "handle" (mesh handleGeom handleMat [ onPartClick "handle" HandleClick ] ...)
    ∷ [] )
```

**Questions to explore:**
- How to store names in pick buffer? (separate mapping?)
- Performance of name lookup
- Name uniqueness — should we check?

### 2.3 Hit Testing Modes

```agda
-- Hit detection modes
data HitMode : Set where
  BoundingBox   : HitMode    -- fast, imprecise
  PerTriangle   : HitMode    -- precise, slow
  ConvexHull    : HitMode    -- compromise
  Custom        : Geometry → HitMode  -- separate hitbox geometry

-- Set mode for node
setHitMode : HitMode → SceneNode M A → SceneNode M A

-- Automatic bounding box
autoHitbox : SceneNode M A → SceneNode M A  -- = setHitMode BoundingBox

-- Invisible hitbox geometry (larger than visible)
expandedHitbox : Float → SceneNode M A → SceneNode M A
```

**Questions to explore:**
- Current runtime uses color picking — how to integrate BoundingBox mode?
- Performance of per-triangle on complex meshes
- Hitbox for text (invisible rect behind text?)

### 2.4 Focus and Keyboard in Groups

```agda
-- Group accepts focus as a single unit
focusableGroup : ∀ {M A}
               → (KeyEvent → A)           -- keyboard handler
               → List (SceneNode M A)
               → Transform
               → SceneNode M A

-- Tab order between groups
tabIndex : ℕ → SceneNode M A → SceneNode M A

-- Focus visual indicator (automatic highlight)
withFocusRing : Color → Float → SceneNode M A → SceneNode M A
```

---

## Part 3: Layout System

### 3.1 Linear Layouts

```agda
-- Arrange in row along axis
hstack3D : Float → List (SceneNode M A) → SceneNode M A  -- X axis
vstack3D : Float → List (SceneNode M A) → SceneNode M A  -- Y axis
dstack3D : Float → List (SceneNode M A) → SceneNode M A  -- Z axis (depth)

-- With alignment
data Align : Set where
  Start Center End : Align

hstackAligned : Float → Align → List (SceneNode M A) → SceneNode M A
```

**Questions to explore:**
- How to determine SceneNode size for position calculation?
- Do we need bounding box API?
- Dynamic sizes (dependent on model)?

### 3.2 Grid Layout

```agda
-- 2D grid (in XY, XZ, or YZ plane)
grid3D : ℕ × ℕ → Vec2 → Plane → List (SceneNode M A) → SceneNode M A

-- With automatic cell size
gridAuto : ℕ → Float → List (SceneNode M A) → SceneNode M A  -- columns, total width

-- Example:
buttonGrid = grid3D (3, 4) (vec2 1.2 0.8) XZ (map makeButton items)
```

### 3.3 Radial Layouts

```agda
-- In a circle (in XZ plane)
ring3D : Float → List (SceneNode M A) → SceneNode M A

-- Arc (part of circle)
arc3D : Float → Float → Float → List (SceneNode M A) → SceneNode M A  -- radius, start, end angle

-- Spiral
spiral3D : Float → Float → Float → List (SceneNode M A) → SceneNode M A  -- radius, pitch, turns

-- On sphere surface
sphereLayout : Float → List (SceneNode M A) → SceneNode M A

-- On cylinder
cylinderLayout : Float → Float → ℕ → List (SceneNode M A) → SceneNode M A  -- radius, height, rings
```

### 3.4 Responsive and Adaptive

```agda
-- Different layout depending on viewport size
responsive3D : List (Float × (List (SceneNode M A) → SceneNode M A))
             → List (SceneNode M A)
             → SceneNode M A
-- [(minWidth, layoutFn), ...]

-- Scale group to fit in bounds
fitToBounds : Vec3 → SceneNode M A → SceneNode M A

-- Preserve aspect ratio
preserveAspect : SceneNode M A → SceneNode M A
```

---

## Part 4: Optimization

### 4.1 Geometry Batching

```agda
-- Combine static geometry (single draw call)
batch : List (SceneNode M A) → SceneNode M A

-- Only for nodes with same material, no animations
-- Runtime combines vertex buffers
```

**Questions to explore:**
- How to handle different materials? (multi-material?)
- Static vs dynamic batching
- When to rebatch (on model change?)

### 4.2 Instancing

```agda
-- Many copies of one geometry with different transforms
instanced : Geometry → Material → List Transform → SceneNode M A

-- With different colors (per-instance color)
instancedColored : Geometry → List (Transform × Color) → SceneNode M A

-- With different materials? (texture array)
instancedTextured : Geometry → List (Transform × TextureIndex) → SceneNode M A

-- Interactive instancing (click returns index)
instancedInteractive : ∀ {M A}
                     → Geometry → Material
                     → (M → List Transform)
                     → (ℕ → A)              -- instance index
                     → SceneNode M A
```

**Questions to explore:**
- WebGL instancing API (ANGLE_instanced_arrays / WebGL2)
- How to do picking on instanced geometry? (instance ID in pick buffer)
- Maximum number of instances

### 4.3 LOD (Level of Detail)

```agda
-- Different geometry at different distances
lod : List (Float × SceneNode M A) → SceneNode M A  -- (maxDistance, node)

-- Example:
tree = lod
  ( (10.0, highPolyTree)
  ∷ (50.0, mediumPolyTree)
  ∷ (100.0, lowPolyTree)
  ∷ (∞, billboard)  -- sprite at large distance
  ∷ [] )

-- Automatic LOD generation (mesh simplification)
autoLOD : List Float → Geometry → List Geometry
```

### 4.4 Frustum Culling

```agda
-- Mark node for frustum culling (don't draw if outside camera)
cullable : SceneNode M A → SceneNode M A

-- Specify bounding volume explicitly (for complex objects)
withBounds : BoundingVolume → SceneNode M A → SceneNode M A

data BoundingVolume : Set where
  BBox : Vec3 → Vec3 → BoundingVolume  -- min, max
  BSphere : Vec3 → Float → BoundingVolume  -- center, radius
```

---

## Part 5: Utilities

### 5.1 Materials and Styles

```agda
-- Style for group (applies to children if not overridden)
withMaterial : Material → SceneNode M A → SceneNode M A

-- Theme (set of materials by name)
record Theme : Set where
  field
    primary : Material
    secondary : Material
    background : Material
    accent : Material
    text : Material

withTheme : Theme → SceneNode M A → SceneNode M A
themed : (Theme → Material) → SceneNode M A → SceneNode M A
```

### 5.2 Animations

```agda
-- Animation composition
sequence : List (Duration × (Float → Transform)) → (Float → Transform)
parallel : List (Float → Transform) → (Float → Transform)

-- Standard animations
fadeIn : Duration → SceneNode M A → SceneNode M A
fadeOut : Duration → SceneNode M A → SceneNode M A
scaleIn : Duration → SceneNode M A → SceneNode M A
slideIn : Vec3 → Duration → SceneNode M A → SceneNode M A

-- Spring physics
springTo : Float → Float → Transform → (Float → Transform)  -- stiffness, damping
```

### 5.3 Debug Helpers

```agda
-- Show bounding box
showBounds : Color → SceneNode M A → SceneNode M A

-- Show axes (XYZ arrows)
showAxes : Float → SceneNode M A → SceneNode M A

-- Show normals
showNormals : Float → Color → Geometry → SceneNode M A

-- Wireframe mode
wireframe : SceneNode M A → SceneNode M A

-- Stats overlay (draw calls, triangles, etc.)
withStats : SceneNode M A → SceneNode M A
```

---

## Part 6: Import and Dynamic Objects

### 6.1 Model Loading (Runtime)

```agda
-- Loading returns Cmd, result arrives as Msg
loadModel : String → (LoadedModel → A) → (String → A) → Cmd A
-- loadModel url onSuccess onError

-- Loaded model — tree of nodes
record LoadedModel : Set where
  constructor mkLoadedModel
  field
    scenes    : List ModelScene
    materials : List Material
    textures  : List TextureHandle

record ModelScene : Set where
  constructor mkModelScene
  field
    name  : String
    nodes : List ModelNode

-- Node can contain mesh, children, or both
record ModelNode : Set where
  constructor mkModelNode
  field
    name      : String
    transform : Transform
    mesh      : Maybe (Geometry × ℕ)  -- geometry × material index
    children  : List ModelNode

-- Use in scene
importedModel : LoadedModel → SceneNode M A
importedModel model = ...  -- convert to SceneNode
```

**Formats:**

```agda
-- GLTF/GLB (recommended, includes everything)
loadGLTF : String → (LoadedModel → A) → (String → A) → Cmd A

-- OBJ + MTL (legacy, geometry and simple materials only)
loadOBJ : String → (LoadedModel → A) → (String → A) → Cmd A

-- STL (geometry only, for 3D printing)
loadSTL : String → (Geometry → A) → (String → A) → Cmd A

-- PLY (point clouds, scans)
loadPLY : String → (Geometry → A) → (String → A) → Cmd A
```

### 6.2 Lenses for Model Navigation

A loaded model is a complex tree. Lenses allow:
- Finding a node by name/path
- Modifying transform/material of a specific part
- Reactively updating parts of the model

```agda
open import Agdelte.Reactive.Lens

-- Lens to node by name
nodeByName : String → Lens LoadedModel (Maybe ModelNode)

-- Lens to node by path
nodeByPath : List String → Lens LoadedModel (Maybe ModelNode)

-- Lens to node's transform
nodeTransform : Lens ModelNode Transform

-- Lens to mesh's material
nodeMaterial : Lens ModelNode (Maybe ℕ)

-- Composition: find node "wheel_front_left" and get its transform
wheelTransform : Lens LoadedModel (Maybe Transform)
wheelTransform = nodeByName "wheel_front_left" ∘ mapped ∘ nodeTransform
```

**Why lenses instead of just functions?**

```agda
-- Without lenses: need separate getter and setter
getWheelTransform : LoadedModel → Maybe Transform
setWheelTransform : Transform → LoadedModel → LoadedModel

-- With lenses: single object for reading and writing
view wheelTransform model          -- get
set wheelTransform newT model      -- set
over wheelTransform rotate model   -- modify
```

### 6.3 Reactive Bindings for Imported Models

```agda
-- Import with reactive transform for part of model
importedWithBind : ∀ {M A}
                 → LoadedModel
                 → String                    -- node name
                 → (M → Transform)           -- dynamic transform
                 → SceneNode M A

-- Import with reactive material
importedWithMaterial : ∀ {M A}
                     → LoadedModel
                     → String                -- node name
                     → (M → Material)
                     → SceneNode M A

-- More general: apply function to node
importedModified : ∀ {M A}
                 → LoadedModel
                 → (ModelNode → M → ModelNode)  -- modifier
                 → SceneNode M A

-- Example: car with rotating wheels
car : LoadedModel → SceneNode Model Msg
car model = importedModified model λ node m →
  if name node == "wheel_fl" ∨ name node == "wheel_fr"
  then record node { transform = rotateY (wheelAngle m) (transform node) }
  else node
```

### 6.4 Dynamic Adding/Removing Objects

The Model in Agda is immutable. Dynamic objects work through the application model:

```agda
-- In model we store list of loaded objects
record Model : Set where
  field
    staticScene : SceneNode Model Msg
    dynamicObjects : List (String × LoadedModel × Transform)
    -- id × model × current transform

-- Scene combines static and dynamic
scene : Model → Scene Model Msg
scene m = mkScene camera
  ( staticScene m
  ∷ map renderDynamic (dynamicObjects m)
  )
  where
    renderDynamic : String × LoadedModel × Transform → SceneNode Model Msg
    renderDynamic (id, model, t) =
      group t [ importedModel model ]

-- Commands for adding/removing
data Msg : Set where
  ModelLoaded : String → LoadedModel → Msg
  RemoveObject : String → Msg
  MoveObject : String → Transform → Msg
```

### 6.5 Asset Management

```agda
-- Caching loaded models
record AssetCache : Set where
  field
    models   : List (String × LoadedModel)
    textures : List (String × TextureHandle)
    loading  : List String  -- URLs in progress

-- Load with caching
loadCached : String → AssetCache → Cmd A × AssetCache

-- Preload set of assets
preloadAssets : List String → (AssetCache → A) → Cmd A

-- Unload unused
unloadUnused : List String → AssetCache → AssetCache  -- keep these URLs
```

### 6.6 Procedural Generation at Runtime

```agda
-- Geometry can be generated dynamically
data DynamicGeometry : Set where
  Static    : Geometry → DynamicGeometry
  Generated : (M → Geometry) → DynamicGeometry  -- recalculated when model changes
  Streamed  : (M → List Triangle) → DynamicGeometry  -- for infinite/procedural worlds

-- Example: terrain from heightmap in model
terrain : DynamicGeometry
terrain = Generated λ m → heightmapToGeometry (terrainData m)

-- Example: trail behind moving object
trail : DynamicGeometry
trail = Streamed λ m → generateTrailTriangles (positionHistory m)
```

---

## Part 7: Integration with Agdelte FRP Model

### 7.1 Agdelte Architecture Overview (Reminder)

```
┌─────────────────────────────────────────────────────┐
│                      Model                          │
│  (immutable application state)                      │
└─────────────────────────────────────────────────────┘
        │                              ▲
        │ view                         │ update
        ▼                              │
┌─────────────────┐              ┌─────────────────┐
│   Node M Msg    │              │      Msg        │
│   (template)    │─── events ──▶│   (messages)    │
└─────────────────┘              └─────────────────┘
        │                              │
        │ render                       │ cmd
        ▼                              ▼
┌─────────────────┐              ┌─────────────────┐
│      DOM        │              │   Cmd Msg       │
│  (side effects) │              │ (async effects) │
└─────────────────┘              └─────────────────┘
                                       │
                                       │ Event Msg
                                       ▼
                                ┌─────────────────┐
                                │  subscriptions  │
                                │   (subs)        │
                                └─────────────────┘
```

### 7.2 Where Do Loaded Models Live?

**Option A: In Application Model**

```agda
record Model : Set where
  field
    -- Regular data
    counter : ℕ

    -- Loaded 3D assets
    carModel : Maybe LoadedModel
    treeModel : Maybe LoadedModel

    -- Loading state
    loading : List String

data Msg : Set where
  CarLoaded : LoadedModel → Msg
  TreeLoaded : LoadedModel → Msg
  LoadError : String → Msg
  -- ...
```

**Pros:** Pure FRP, everything in model
**Cons:** Model grows large, LoadedModel is big

**Option B: In Separate AssetStore (via Cmd/Sub)**

```agda
-- AssetStore lives in runtime, not in Model
-- Access through special Cmd and identifiers

data AssetId : Set where
  mkAssetId : String → AssetId

-- Loading puts in store, returns id
loadToStore : String → (AssetId → A) → (String → A) → Cmd A

-- In Model we only store id
record Model : Set where
  field
    carAsset : Maybe AssetId
    treeAsset : Maybe AssetId

-- In template we use id for reference
template : Node Model Msg
template =
  glCanvas []
    (mkScene camera
      ( maybe (assetById (carAsset m)) empty
      ∷ [] ))
```

**Pros:** Model stays small, assets are cached
**Cons:** Indirection, requires runtime store

**Option C: Hybrid**

```agda
-- In Model: lightweight references + metadata
record AssetRef : Set where
  field
    id : AssetId
    loaded : Bool
    error : Maybe String

record Model : Set where
  field
    car : AssetRef
    carTransform : Transform  -- mutable state
    carWheelAngle : Float
```

### 7.3 Cmd for Loading

Loading is an async operation, naturally expressed through Cmd:

```agda
-- Main loading command
loadModel : String → (LoadedModel → Msg) → (String → Msg) → Cmd Msg

-- In update:
update : Msg → Model → Model × Cmd Msg
update LoadCarClicked m =
  ( record m { loading = "car" ∷ loading m }
  , loadModel "/models/car.glb" CarLoaded LoadError
  )
update (CarLoaded model) m =
  ( record m { carModel = just model ; loading = remove "car" (loading m) }
  , none
  )

-- With progress (through Event, not Cmd)
loadModelWithProgress : String
                      → (Float → Msg)         -- progress 0-1
                      → (LoadedModel → Msg)   -- success
                      → (String → Msg)        -- error
                      → Event Msg
```

### 7.4 Event/Sub for Streaming

For streaming loading or procedural generation — Event:

```agda
-- Subscribe to chunks of large model
streamModel : String → (ModelChunk → Msg) → (String → Msg) → Event Msg

-- In subs:
subs : Model → Event Msg
subs m =
  if needsStreaming m
  then streamModel "/terrain/chunk" TerrainChunk StreamError
  else never

-- Chunk is appended to existing geometry
update (TerrainChunk chunk) m =
  record m { terrain = appendChunk chunk (terrain m) }
```

### 7.5 Reactivity of Loaded Models

A loaded model is static data. Reactivity is achieved through:

**A. bindTransform at SceneNode level:**

```agda
-- Model is already loaded in m.carModel
-- Apply dynamic transform from m.carPosition
scene m = mkScene camera
  ( case carModel m of
      nothing → empty
      just car →
        bindTransform (λ m → m.carPosition)  -- reactive transform
          (importedModel car)
  ∷ [] )
```

**B. Lenses for accessing parts:**

```agda
-- Car wheels need to rotate
scene m = mkScene camera
  ( case carModel m of
      nothing → empty
      just car →
        importedWithBindings car
          [ ("wheel_fl", λ m → rotateY (wheelAngle m) identityTransform)
          , ("wheel_fr", λ m → rotateY (wheelAngle m) identityTransform)
          , ("wheel_bl", λ m → rotateY (wheelAngle m) identityTransform)
          , ("wheel_br", λ m → rotateY (wheelAngle m) identityTransform)
          ]
  ∷ [] )

-- importedWithBindings uses lenses internally
importedWithBindings : LoadedModel
                     → List (String × (M → Transform))
                     → SceneNode M Msg
```

**C. Materials can also be reactive:**

```agda
importedWithMaterials : LoadedModel
                      → List (String × (M → Material))
                      → SceneNode M Msg

-- Example: car changes color when selected
scene m = importedWithMaterials car
  [ ("body", λ m → if selected m then highlightMat else normalMat) ]
```

### 7.6 Full Application Example

```agda
module CarViewer where

open import Agdelte.Reactive.Node
open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  field
    -- Assets
    carModel    : Maybe LoadedModel
    loading     : Bool
    loadError   : Maybe String

    -- Scene state
    carRotation : Float
    wheelAngle  : Float
    selectedPart : Maybe String

    -- Camera
    cameraAngle : Float
    cameraDistance : Float

initialModel : Model
initialModel = record
  { carModel = nothing
  ; loading = false
  ; loadError = nothing
  ; carRotation = 0.0
  ; wheelAngle = 0.0
  ; selectedPart = nothing
  ; cameraAngle = 0.0
  ; cameraDistance = 5.0
  }

------------------------------------------------------------------------
-- Msg
------------------------------------------------------------------------

data Msg : Set where
  -- Loading
  LoadCar     : Msg
  CarLoaded   : LoadedModel → Msg
  LoadFailed  : String → Msg

  -- Interaction
  RotateCar   : Float → Msg
  SpinWheels  : Msg
  SelectPart  : String → Msg
  DeselectPart : Msg

  -- Camera
  OrbitCamera : Float → Float → Msg
  ZoomCamera  : Float → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

update : Msg → Model → Model
update LoadCar m = record m { loading = true }
update (CarLoaded model) m = record m { carModel = just model ; loading = false }
update (LoadFailed err) m = record m { loadError = just err ; loading = false }
update (RotateCar delta) m = record m { carRotation = carRotation m + delta }
update SpinWheels m = record m { wheelAngle = wheelAngle m + 0.1 }
update (SelectPart name) m = record m { selectedPart = just name }
update DeselectPart m = record m { selectedPart = nothing }
update (OrbitCamera dx dy) m = record m { cameraAngle = cameraAngle m + dx }
update (ZoomCamera delta) m = record m { cameraDistance = cameraDistance m + delta }

------------------------------------------------------------------------
-- Cmd
------------------------------------------------------------------------

cmd : Msg → Model → Cmd Msg
cmd LoadCar _ = loadModel "/models/car.glb" CarLoaded LoadFailed
cmd _ _ = none

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs : Model → Event Msg
subs m =
  if isJust (carModel m)
  then interval 16 SpinWheels  -- 60fps wheel animation
  else never

------------------------------------------------------------------------
-- View Helpers
------------------------------------------------------------------------

carTransform : Model → Transform
carTransform m = rotateY (carRotation m) identityTransform

wheelBindings : Model → List (String × Transform)
wheelBindings m =
  let rot = rotateX (wheelAngle m) identityTransform
  in [ ("wheel_fl", rot), ("wheel_fr", rot)
     , ("wheel_bl", rot), ("wheel_br", rot) ]

partMaterial : Model → String → Material
partMaterial m name =
  if selectedPart m == just name
  then emissive (rgb 1.0 0.5 0.0) 0.3  -- highlight
  else defaultMaterial

------------------------------------------------------------------------
-- Scene
------------------------------------------------------------------------

scene : Model → Scene Model Msg
scene m = mkScene (orbitCamera (cameraAngle m) 0.3 (cameraDistance m))
  ( -- Environment
    light (ambient white 0.4)
  ∷ light (directional white 0.8 (vec3 1.0 -1.0 -1.0))
  ∷ mesh (plane (vec2 10.0 10.0)) floorMaterial [] floorTransform

  -- Car (if loaded)
  ∷ maybe′
      (λ car →
        bindTransform carTransform
          (importedInteractive car
            (map fst (wheelBindings m))  -- animated nodes
            (λ m name → lookup name (wheelBindings m))  -- transform for node
            (λ m name → partMaterial m name)  -- material for node
            (λ name → SelectPart name)  -- onClick
            (λ _ → DeselectPart)))  -- onClickOutside
      empty
      (carModel m)

  ∷ [] )

------------------------------------------------------------------------
-- Template (HTML + WebGL)
------------------------------------------------------------------------

template : Node Model Msg
template =
  div [ class "car-viewer" ]
    ( h1 [] [ text "Car Viewer" ]

    -- Load button
    ∷ when (λ m → isNothing (carModel m) ∧ not (loading m))
        (button [ onClick LoadCar ] [ text "Load Car" ])

    -- Loading indicator
    ∷ when loading
        (div [ class "loading" ] [ text "Loading..." ])

    -- Error
    ∷ when (isJust ∘ loadError)
        (div [ class "error" ] [ bindF (fromMaybe "" ∘ loadError) ])

    -- WebGL canvas
    ∷ glCanvas [ attr "width" "800", attr "height" "600" ] scene

    -- Selected part info
    ∷ when (isJust ∘ selectedPart)
        (div [ class "info" ]
          [ text "Selected: "
          , bindF (fromMaybe "" ∘ selectedPart) ])

    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel update template cmd subs
```

### 7.7 Key Integration Principles

1. **Model contains state, not resources**
   - `Maybe LoadedModel` — ok (reference to loaded asset)
   - Don't store raw vertex data in Model

2. **Loading through Cmd**
   - Async operations = Cmd
   - Result arrives as Msg
   - update remains a pure function

3. **Animation through Subs/Event**
   - interval for continuous animation
   - Animation state (wheelAngle) in Model

4. **Reactivity through bind functions**
   - `bindTransform` — transform depends on Model
   - `bindMaterial` — material depends on Model
   - Lenses for accessing model parts

5. **Events from 3D objects are regular Msg**
   - `glClick` → `SelectPart name`
   - Handled in update like any other

**Questions to explore:**
- Garbage collection for unloaded models?
- Hot reload — how to preserve loaded assets?
- Serialization of Model with Maybe LoadedModel?
- Animations from GLTF — separate type or integration with Event?

---

## Architecture

### Layers

```
┌─────────────────────────────────────────┐
│     Agdelte.WebGL.Controls              │  ← high-level widgets
├─────────────────────────────────────────┤
│     Agdelte.WebGL.Builder               │  ← THIS LIBRARY
│  ┌─────────────┬──────────────────────┐ │
│  │ Geometry    │ InteractiveGroup     │ │
│  │ CSG         │ Layout               │ │
│  │ Procedural  │ Optimization         │ │
│  └─────────────┴──────────────────────┘ │
├─────────────────────────────────────────┤
│     Agdelte.WebGL.Types                 │  ← basic types, primitives
├─────────────────────────────────────────┤
│     runtime/reactive-gl.js              │  ← JS runtime
└─────────────────────────────────────────┘
```

### Modules

```
Agdelte/
  WebGL/
    Builder.agda                    -- re-exports
    Builder/
      Geometry/
        Combine.agda                -- combineGeometry, batch
        CSG.agda                    -- union, subtract, intersect
        Procedural.agda             -- extrude, revolve, loft, sweep
        Primitives.agda             -- roundedBox, capsule, torus, etc.
        Text.agda                   -- textGeometry
      Interaction/
        Group.agda                  -- interactiveGroup
        Named.agda                  -- named, onPartClick
        HitTest.agda                -- HitMode, setHitMode
        Focus.agda                  -- focusableGroup, tabIndex
      Layout/
        Stack.agda                  -- hstack3D, vstack3D, dstack3D
        Grid.agda                   -- grid3D, gridAuto
        Radial.agda                 -- ring3D, arc3D, spiral3D
        Responsive.agda             -- responsive3D, fitToBounds
      Optimize/
        Batch.agda                  -- batch
        Instance.agda               -- instanced, instancedInteractive
        LOD.agda                    -- lod, autoLOD
        Culling.agda                -- cullable, withBounds
      Util/
        Theme.agda                  -- Theme, withTheme
        Animation.agda              -- sequence, parallel, fadeIn, etc.
        Debug.agda                  -- showBounds, showAxes, wireframe
```

---

## Runtime Changes

To support Builder, changes are needed in `reactive-gl.js`:

### Pick Buffer

**Currently:** one pick ID per mesh
**Needed:**
- Groups get one ID (click on any child = click on group)
- Named parts get sub-ID
- Instanced geometry: ID = base + instance index

### Bounding Volumes

**Currently:** none
**Needed:**
- Calculate bounding box when loading geometry
- API for getting group bounds
- Frustum culling based on bounds

### Instancing

**Currently:** none
**Needed:**
- WebGL2 instancing support
- Instance attributes (transform, color)
- Per-instance pick ID

### Geometry Combining

**Currently:** each mesh separately
**Needed:**
- Combine vertex buffers for static geometry
- Bake transforms into vertices
- Single draw call for batch

---

## Implementation Priorities

### Phase 1: Interactive Groups (critical for Controls)
1. `interactiveGroup` — unified events on group
2. `named` / `onPartClick` — events on parts
3. Runtime fixes for group picking

### Phase 2: Layout (needed for Controls)
4. `hstack3D`, `vstack3D`, `dstack3D`
5. `grid3D`
6. `ring3D`, `arc3D`

### Phase 3: Extended Geometry
7. `combineGeometry`
8. Additional primitives (`roundedBox`, `capsule`, etc.)
9. `extrude`, `revolve`

### Phase 4: Optimization
10. `instanced`, `instancedInteractive`
11. `batch`
12. `lod`

### Phase 5: Advanced Features
13. CSG operations
14. `sweep`, `loft`
15. `textGeometry`
16. Automatic LOD

---

## Open Questions

1. **CSG in Agda or JS?**
   - Agda: type-safe, but complex algorithms
   - JS: faster to implement, can use existing libraries
   - Hybrid: Agda API, JS implementation via FFI

2. **Bounds API**
   - How to calculate bounds for group? (union of children)
   - Lazy or eager calculation?
   - Should we cache?

3. **Compatibility with Existing Code**
   - Builder nodes should be regular `SceneNode`
   - Can mix Builder and manual construction

4. **Compile-time Performance**
   - Complex geometry operations may slow compilation
   - Do we need lazy evaluation?

5. **Serialization**
   - Can we cache built geometry?
   - Format for pre-compiled meshes
