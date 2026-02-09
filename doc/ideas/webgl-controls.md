# WebGL Controls Library (Agdelte.WebGL.Controls)

Pure Agda library for 3D UI controls and data visualization in WebGL.
Built on top of `Agdelte.WebGL.Types`. Returns `SceneNode M A`, composable with other scene elements.

## Design Principles

1. **3D-native** — controls that make sense in 3D space, not just flat panels
2. **Spatial** — leverage depth, perspective, rotation
3. **Interactive** — raycasting, hover, drag in 3D
4. **Integrated** — controls as part of the scene, not overlay

## When to Use WebGL Controls

| Use Case | Recommended |
|----------|-------------|
| Regular app UI | HTML Controls |
| 2D data visualization | SVG Controls |
| Charts inside 3D scene | WebGL Controls |
| 3D data visualization | WebGL Controls |
| VR/AR interfaces | WebGL Controls |
| Game UI | WebGL Controls |
| CAD/modeling tools | WebGL Controls |

## 3D Equivalents of 2D Controls

### Buttons

```agda
-- Flat button in 3D space (like a sign)
button3D : ∀ {M A}
         → String                 -- label
         → Material
         → A
         → Transform
         → SceneNode M A

-- Pushable button (animates depth on click)
pushButton3D : ∀ {M A}
             → Vec3               -- size
             → String             -- label
             → Material
             → A
             → Transform
             → SceneNode M A

-- Sphere button
sphereButton : ∀ {M A}
             → Float              -- radius
             → Material
             → A
             → Transform
             → SceneNode M A

-- Floating action button (hovers, has shadow)
fab3D : ∀ {M A}
      → IconMesh                  -- 3D icon
      → Material
      → A
      → Transform
      → SceneNode M A
```

### Sliders

```agda
-- Linear slider with 3D handle
slider3D : ∀ {M A}
         → Float                  -- length
         → Vec3                   -- axis direction
         → (M → Float)            -- value 0-1
         → (Float → A)
         → Transform
         → SceneNode M A

-- Circular dial/knob
dial3D : ∀ {M A}
       → Float                    -- radius
       → Float → Float            -- min, max angle
       → (M → Float)
       → (Float → A)
       → Transform
       → SceneNode M A

-- 2D pad (XY input, like joystick)
pad3D : ∀ {M A}
      → Float                     -- size
      → (M → Float × Float)       -- x, y values
      → (Float → Float → A)
      → Transform
      → SceneNode M A

-- 3D position handle (draggable point in space)
positionHandle : ∀ {M A}
               → (M → Vec3)
               → (Vec3 → A)
               → SceneNode M A
```

### Toggles & Selection

```agda
-- Toggle switch (3D lever)
toggle3D : ∀ {M A}
         → (M → Bool)
         → A
         → Transform
         → SceneNode M A

-- Physical checkbox (box that opens/fills)
checkbox3D : ∀ {M A}
           → Float                -- size
           → (M → Bool)
           → A
           → Transform
           → SceneNode M A

-- Radio buttons (spheres, one lit)
radioGroup3D : ∀ {M A}
             → Float              -- spacing
             → (M → ℕ)
             → (ℕ → A)
             → List String        -- labels
             → Transform
             → SceneNode M A

-- Segmented control (connected buttons)
segmented3D : ∀ {M A}
            → (M → ℕ)
            → (ℕ → A)
            → List String
            → Transform
            → SceneNode M A
```

### Menus & Navigation

```agda
-- Floating menu (panel in 3D space)
menu3D : ∀ {M A}
       → (M → Bool)               -- isOpen
       → A                        -- close
       → List (String × A)        -- items
       → Transform
       → SceneNode M A

-- Radial menu (items around center, in XZ plane)
radialMenu3D : ∀ {M A}
             → Float              -- radius
             → (M → Bool)
             → List (String × IconMesh × A)
             → Transform
             → SceneNode M A

-- Spherical menu (items on sphere surface)
sphericalMenu : ∀ {M A}
              → Float             -- radius
              → (M → Bool)
              → List (String × A)
              → Transform
              → SceneNode M A

-- Helix menu (items along helix path)
helixMenu : ∀ {M A}
          → Float → Float         -- radius, pitch
          → (M → Bool)
          → (M → ℕ)               -- selected
          → (ℕ → A)
          → List String
          → Transform
          → SceneNode M A

-- Dock (row of items, scales on hover like macOS dock)
dock3D : ∀ {M A}
       → (M → ℕ)                  -- hovered index
       → (ℕ → A)
       → List (IconMesh × String)
       → Transform
       → SceneNode M A
```

### Tabs & Panels

```agda
-- Tab bar with 3D tabs (physical tabs you click)
tabBar3D : ∀ {M A}
         → (M → ℕ)
         → (ℕ → A)
         → List (String × SceneNode M A)  -- tab + content
         → Transform
         → SceneNode M A

-- Carousel (rotating set of panels)
carousel3D : ∀ {M A}
           → Float                -- radius
           → (M → ℕ)              -- current
           → (ℕ → A)              -- select
           → List (SceneNode M A)
           → Transform
           → SceneNode M A

-- Card stack (swipe through)
cardStack : ∀ {M A}
          → Vec2                  -- card size
          → (M → ℕ)
          → A → A                 -- next, prev
          → List (SceneNode M A)
          → Transform
          → SceneNode M A

-- Accordion (panels that expand in Z)
accordion3D : ∀ {M A}
            → (M → ℕ)             -- open section
            → (ℕ → A)
            → List (String × SceneNode M A)
            → Transform
            → SceneNode M A
```

## 3D Data Visualization

### Charts in 3D

```agda
-- 3D bar chart (bars with depth)
barChart3D : ∀ {M A}
           → Vec3                 -- base size
           → (M → List (String × Float × Color))
           → Maybe (ℕ → A)        -- click handler
           → Transform
           → SceneNode M A

-- Stacked 3D bar chart
stackedBarChart3D : ∀ {M A}
                  → Vec3
                  → List String   -- series names
                  → List Color
                  → (M → List (String × List Float))
                  → Transform
                  → SceneNode M A

-- 3D scatter plot (points in space)
scatterPlot3D : ∀ {M A}
              → Vec3              -- bounds
              → (M → List (Vec3 × Color × Float))  -- pos, color, size
              → Maybe (ℕ → A)
              → Transform
              → SceneNode M A

-- Line chart with depth (ribbon)
ribbonChart : ∀ {M A}
            → Float               -- width
            → (M → List (Float × Float))  -- (x, y) points
            → Color
            → Transform
            → SceneNode M A

-- Multiple line series in 3D (each at different Z)
multiLineChart3D : ∀ {M A}
                 → Float          -- z spacing
                 → (M → List (List (Float × Float) × Color))
                 → Transform
                 → SceneNode M A
```

### Surfaces & Volumes

```agda
-- Surface plot (height field)
surfacePlot : ∀ {M A}
            → ℕ × ℕ               -- resolution
            → (M → Float → Float → Float)  -- height function(x, z)
            → (Float → Color)     -- height to color
            → Transform
            → SceneNode M A

-- Wireframe surface
wireframeSurface : ∀ {M A}
                 → ℕ × ℕ
                 → (M → Float → Float → Float)
                 → Color
                 → Transform
                 → SceneNode M A

-- Contour plot (3D contour lines)
contourPlot3D : ∀ {M A}
              → ℕ × ℕ
              → List Float        -- contour levels
              → (M → Float → Float → Float)
              → Transform
              → SceneNode M A

-- Volume rendering (density field)
volumeRender : ∀ {M A}
             → ℕ × ℕ × ℕ          -- resolution
             → (M → Float → Float → Float → Float)  -- density(x,y,z)
             → (Float → Color × Float)  -- density to (color, opacity)
             → Transform
             → SceneNode M A

-- Isosurface (marching cubes)
isosurface : ∀ {M A}
           → ℕ × ℕ × ℕ
           → Float                -- iso level
           → (M → Float → Float → Float → Float)
           → Material
           → Transform
           → SceneNode M A
```

### Network & Relations

```agda
-- 3D network graph (nodes and edges in space)
networkGraph3D : ∀ {M A}
               → (M → List (String × Vec3 × Color))        -- nodes
               → (M → List (String × String × Float))      -- edges (from, to, weight)
               → Maybe (String → A)                        -- node click
               → Transform
               → SceneNode M A

-- Force-directed graph (auto-layout, animated)
forceGraph3D : ∀ {M A}
             → (M → List (String × Color))
             → (M → List (String × String))
             → Maybe (String → A)
             → Transform
             → SceneNode M A

-- Tree in 3D (hierarchical)
tree3D : ∀ {M A D}
       → (D → String)             -- label
       → (D → List D)             -- children
       → (M → D)                  -- root
       → Maybe (D → A)
       → Transform
       → SceneNode M A

-- Sankey in 3D (flow between layers)
sankey3D : ∀ {M A}
         → (M → List (String × Float × Float))  -- nodes: (label, layer, value)
         → (M → List (String × String × Float)) -- links
         → Transform
         → SceneNode M A
```

### Spectrum & Signal Visualization

```agda
-- 3D spectrum (frequency × magnitude, with depth)
spectrum3D : ∀ {M A}
           → Vec3                 -- size (width, height, depth)
           → Color
           → (M → List Float)     -- frequency bins
           → Transform
           → SceneNode M A

-- Waterfall spectrum (time scrolling in Z axis)
-- New spectrum data pushes old data back
waterfallSpectrum : ∀ {M A}
                  → Vec3          -- size
                  → ℕ             -- history depth (number of time slices)
                  → (Float → Color)  -- magnitude to color
                  → (M → List Float) -- current spectrum
                  → Transform
                  → SceneNode M A

-- 3D spectrogram surface (time × frequency × magnitude as height)
spectrogramSurface : ∀ {M A}
                   → Vec2         -- base size (time × frequency)
                   → Float        -- height scale
                   → (Float → Color)
                   → (M → List (List Float))  -- time × frequency
                   → Transform
                   → SceneNode M A

-- Circular waterfall (rotating cylinder with spectrum)
circularWaterfall : ∀ {M A}
                  → Float → Float  -- radius, height
                  → ℕ              -- time slices around circumference
                  → (Float → Color)
                  → (M → List Float)
                  → Transform
                  → SceneNode M A

-- 3D oscilloscope (waveform as ribbon in space)
oscilloscope3D : ∀ {M A}
               → Float → Float    -- length, amplitude scale
               → Color
               → (M → List Float) -- samples
               → Transform
               → SceneNode M A

-- Multi-channel waveform (stacked in Z)
multiChannelWaveform : ∀ {M A}
                     → Float → Float → Float  -- length, height, channel spacing
                     → List Color
                     → (M → List (List Float))  -- channels × samples
                     → Transform
                     → SceneNode M A

-- Lissajous figure (XY oscilloscope mode)
lissajous3D : ∀ {M A}
            → Float              -- size
            → Color
            → (M → List Float)   -- X channel
            → (M → List Float)   -- Y channel
            → Transform
            → SceneNode M A

-- Frequency spiral (spectrum mapped to helix)
frequencySpiral : ∀ {M A}
                → Float → Float   -- radius, pitch
                → ℕ               -- turns
                → (Float → Color)
                → (M → List Float)
                → Transform
                → SceneNode M A

-- 3D frequency bars (classic visualizer, dancing bars)
frequencyBars3D : ∀ {M A}
                → ℕ × ℕ           -- grid dimensions (1×N for single row)
                → Float           -- bar spacing
                → (Float → Color) -- magnitude to color
                → (M → List Float)
                → Transform
                → SceneNode M A

-- Frequency terrain (fly through spectrum landscape)
frequencyTerrain : ∀ {M A}
                 → Vec2           -- terrain size
                 → ℕ              -- history length (depth)
                 → (Float → Color)
                 → (M → List Float)  -- current spectrum
                 → Transform
                 → SceneNode M A

-- Spherical harmonics audio visualizer
sphericalHarmonics : ∀ {M A}
                   → Float        -- base radius
                   → (M → List Float)  -- harmonic coefficients
                   → Material
                   → Transform
                   → SceneNode M A

-- Audio blob (sphere that morphs with audio)
audioBlob : ∀ {M A}
          → Float               -- base radius
          → (M → List Float)    -- frequency bins (deform sphere)
          → Material
          → Transform
          → SceneNode M A
```

### 3D Audio Instruments & Controls

```agda
-- 3D piano keyboard (keys animate on press)
piano3D : ∀ {M A}
        → ℕ → ℕ                 -- octave range
        → (M → List ℕ)          -- pressed notes (MIDI)
        → (ℕ → A)               -- note on/off
        → Transform
        → SceneNode M A

-- Drum pad grid (3D pads that depress on hit)
drumPads3D : ∀ {M A}
           → ℕ × ℕ              -- grid size
           → Float              -- pad size
           → (M → List ℕ)       -- active pads (indices)
           → (ℕ → A)            -- pad hit
           → Transform
           → SceneNode M A

-- 3D mixer console (channel strips with faders)
mixer3D : ∀ {M A}
        → ℕ                     -- number of channels
        → (M → List Float)      -- fader positions (0-1)
        → (M → List Float)      -- meter levels
        → (ℕ → Float → A)       -- set fader
        → Transform
        → SceneNode M A

-- 3D knob (rotary encoder)
knob3D : ∀ {M A}
       → Float                  -- radius
       → (M → Float)            -- value (0-1)
       → (Float → A)
       → Transform
       → SceneNode M A

-- XY pad in 3D (Kaoss-style)
xyPad3D : ∀ {M A}
        → Float                 -- size
        → (M → Float × Float)   -- x, y position
        → (Float → Float → A)
        → Transform
        → SceneNode M A

-- Ribbon controller
ribbon3D : ∀ {M A}
         → Float → Float        -- length, width
         → (M → Maybe Float)    -- touch position (Nothing = not touched)
         → (Maybe Float → A)
         → Transform
         → SceneNode M A
```

### 3D Spatial Audio

```agda
-- Surround sound panner (position source in 3D space)
surroundPanner : ∀ {M A}
               → Float            -- room radius
               → (M → Vec3)       -- source position
               → (Vec3 → A)       -- move source
               → List Vec3        -- speaker positions (visual reference)
               → Transform
               → SceneNode M A

-- HRTF visualization (head with sound direction)
hrtfVisualizer : ∀ {M A}
               → Float            -- head radius
               → (M → List (Vec3 × Float))  -- source directions × intensity
               → Transform
               → SceneNode M A

-- Room acoustics / ray tracing visualization
roomAcoustics : ∀ {M A}
              → List (Vec3 × Vec3 × Vec3)  -- room geometry (triangles)
              → (M → Vec3)                  -- source position
              → (M → Vec3)                  -- listener position
              → (M → List (List Vec3))      -- reflection paths
              → Transform
              → SceneNode M A

-- Ambisonics sphere (B-format visualization)
ambisonicsSphere : ∀ {M A}
                 → Float          -- radius
                 → (M → List Float)  -- ambisonic coefficients (W, X, Y, Z, ...)
                 → Transform
                 → SceneNode M A

-- Distance attenuation visualizer (shows falloff)
attenuationField : ∀ {M A}
                 → Float          -- max distance
                 → (M → Vec3)     -- source position
                 → (M → Float × Float)  -- rolloff params
                 → Transform
                 → SceneNode M A
```

### 3D Synthesis Visualization

```agda
-- 3D ADSR envelope (time on X, level on Y, animates in Z)
envelope3D : ∀ {M A}
           → Vec3               -- size
           → (M → Float × Float × Float × Float)  -- ADSR
           → (M → Maybe Float)  -- current position in envelope
           → Transform
           → SceneNode M A

-- Modulation matrix (3D grid showing connections)
modulationMatrix3D : ∀ {M A}
                   → List String  -- sources
                   → List String  -- destinations
                   → (M → List (ℕ × ℕ × Float))  -- connections (src, dest, amount)
                   → (ℕ → ℕ → A)  -- click connection
                   → Transform
                   → SceneNode M A

-- Wavetable visualizer (3D stack of waveforms)
wavetable3D : ∀ {M A}
            → Vec3              -- size
            → (M → List (List Float))  -- wavetable frames
            → (M → Float)       -- current position (morph)
            → Transform
            → SceneNode M A

-- Additive synthesis (3D harmonic bars)
additiveHarmonics3D : ∀ {M A}
                    → ℕ           -- number of harmonics
                    → Float       -- spacing
                    → (M → List Float)  -- harmonic amplitudes
                    → (ℕ → Float → A)   -- adjust harmonic
                    → Transform
                    → SceneNode M A

-- FM synthesis operator visualization
fmOperators3D : ∀ {M A}
              → (M → List (Vec3 × Float × Float))  -- pos, freq, amplitude per op
              → (M → List (ℕ × ℕ × Float))         -- modulation connections
              → Transform
              → SceneNode M A

-- Filter resonance surface (cutoff × resonance × response)
filterSurface3D : ∀ {M A}
                → Vec3            -- size
                → (Float → Float → Float → Float)  -- response(freq, cutoff, Q)
                → (M → Float × Float)  -- current cutoff, Q (for marker)
                → Transform
                → SceneNode M A
```

### Geographic

```agda
-- 3D globe with data
globe : ∀ {M A}
      → Float                     -- radius
      → TextureHandle             -- earth texture
      → (M → List (Float × Float × Color × Float))  -- (lat, lon, color, height)
      → Maybe (ℕ → A)
      → Transform
      → SceneNode M A

-- Extruded map (countries as 3D shapes)
extrudedMap : ∀ {M A}
            → (String → M → Float)  -- region → height
            → (String → M → Color)  -- region → color
            → Maybe (String → A)
            → Transform
            → SceneNode M A

-- 3D city/terrain
terrain : ∀ {M A}
        → ℕ × ℕ                   -- grid size
        → (M → Float → Float → Float)  -- heightmap
        → TextureHandle           -- surface texture
        → Transform
        → SceneNode M A
```

## Unique 3D Controls

Things that only make sense in 3D:

### Gizmos & Handles

```agda
-- Translation gizmo (XYZ arrows)
translateGizmo : ∀ {M A}
               → (M → Vec3)
               → (Vec3 → A)
               → SceneNode M A

-- Rotation gizmo (XYZ circles)
rotateGizmo : ∀ {M A}
            → (M → Quat)
            → (Quat → A)
            → SceneNode M A

-- Scale gizmo (XYZ boxes)
scaleGizmo : ∀ {M A}
           → (M → Vec3)
           → (Vec3 → A)
           → SceneNode M A

-- Combined transform gizmo (translate + rotate + scale)
transformGizmo : ∀ {M A}
               → (M → Transform)
               → (Transform → A)
               → SceneNode M A

-- Bounding box with handles (resize)
boundingBoxHandle : ∀ {M A}
                  → (M → Vec3 × Vec3)  -- min, max
                  → (Vec3 → Vec3 → A)
                  → SceneNode M A
```

### Spatial Selection

```agda
-- 3D selection box (drag to create box, selects objects inside)
selectionBox3D : ∀ {M A}
               → (M → Maybe (Vec3 × Vec3))
               → (Vec3 → Vec3 → A)  -- selection complete
               → SceneNode M A

-- Lasso selection (draw path, selects objects inside projected area)
lasso3D : ∀ {M A}
        → (M → List Vec3)
        → (List Vec3 → A)
        → SceneNode M A

-- Sphere selection (expanding sphere from point)
sphereSelection : ∀ {M A}
                → (M → Maybe (Vec3 × Float))
                → (Vec3 → Float → A)
                → SceneNode M A
```

### Measurement & Annotation

```agda
-- Distance measurement (line with label)
measureDistance : ∀ {M A}
                → Vec3 → Vec3
                → (Float → String)  -- formatter
                → SceneNode M A

-- Angle measurement
measureAngle : ∀ {M A}
             → Vec3 → Vec3 → Vec3  -- three points
             → SceneNode M A

-- 3D annotation (billboard text attached to point)
annotation3D : ∀ {M A}
             → Vec3               -- anchor
             → String             -- text
             → SceneNode M A

-- Callout with line
callout3D : ∀ {M A}
          → Vec3                  -- target
          → Vec3                  -- label position
          → String
          → SceneNode M A
```

### Camera Controls (UI elements)

```agda
-- View cube (click faces to snap camera)
viewCube : ∀ {M A}
         → (Vec3 → A)             -- set camera direction
         → SceneNode M A          -- renders in corner of screen

-- Camera orbit indicator
orbitIndicator : ∀ {M A}
               → (M → Float × Float)  -- azimuth, elevation
               → SceneNode M A

-- Compass (shows north)
compass3D : ∀ {M A}
          → (M → Float)           -- heading
          → SceneNode M A
```

### Portals & Windows

```agda
-- Portal (window into another scene/camera)
portal : ∀ {M A}
       → Vec2                     -- size
       → Scene M A                -- scene to render
       → Camera                   -- camera for that scene
       → Transform
       → SceneNode M A

-- Picture-in-picture (secondary camera view)
pip : ∀ {M A}
    → Vec2
    → (M → Camera)
    → Transform
    → SceneNode M A

-- Mirror (reflects scene)
mirror : ∀ {M A}
       → Vec2
       → Transform
       → SceneNode M A
```

## Creative / Exotic 3D Controls

### Physics-based

```agda
-- Pendulum selector (swings to selection)
pendulumSelector : ∀ {M A}
                 → Float          -- length
                 → (M → ℕ)
                 → (ℕ → A)
                 → List String
                 → Transform
                 → SceneNode M A

-- Marble maze menu (tilt to navigate)
marbleMaze : ∀ {M A}
           → (M → Float × Float)  -- tilt X, Y
           → (String → A)         -- reached target
           → List (Vec2 × String) -- targets
           → Transform
           → SceneNode M A

-- Spring buttons (bounce on click)
springButton : ∀ {M A}
             → String → A
             → Transform
             → SceneNode M A
```

### Volumetric

```agda
-- Holographic display (volumetric text/graphics)
hologram : ∀ {M A}
         → Vec3                   -- size
         → SceneNode M A          -- content
         → Transform
         → SceneNode M A

-- Particle text (text made of particles)
particleText : ∀ {M A}
             → (M → String)
             → Float              -- size
             → Color
             → Transform
             → SceneNode M A

-- Morphing shape selector
morphSelector : ∀ {M A}
              → (M → ℕ)
              → (ℕ → A)
              → List Geometry     -- shapes to morph between
              → Transform
              → SceneNode M A
```

### Dimensional

```agda
-- Tesseract menu (4D hypercube projection)
tesseractMenu : ∀ {M A}
              → (M → Float)       -- 4D rotation angle
              → (ℕ → A)           -- select vertex
              → List String       -- 16 items
              → Transform
              → SceneNode M A

-- Klein bottle slider (non-orientable surface)
kleinSlider : ∀ {M A}
            → (M → Float)
            → (Float → A)
            → Transform
            → SceneNode M A

-- Möbius strip selector
mobiusSelector : ∀ {M A}
               → Float            -- radius
               → (M → Float)      -- position 0-1
               → (Float → A)
               → Transform
               → SceneNode M A
```

### Architectural

```agda
-- Room selector (3D floor plan)
roomSelector : ∀ {M A}
             → (M → String)       -- selected room
             → (String → A)
             → List (String × List Vec2)  -- room polygons
             → Transform
             → SceneNode M A

-- Exploded view control (pull apart assembly)
explodedView : ∀ {M A}
             → (M → Float)        -- explosion factor 0-1
             → (Float → A)
             → List (SceneNode M A × Vec3)  -- parts × directions
             → Transform
             → SceneNode M A

-- Layer visibility (toggle layers in 3D model)
layerControl : ∀ {M A}
             → (M → List Bool)    -- layer visibility
             → (ℕ → A)            -- toggle layer
             → List (String × SceneNode M A)
             → Transform
             → SceneNode M A
```

## Module Structure

```
Agdelte/
  WebGL/
    Controls.agda              -- re-exports all
    Controls/
      Buttons.agda
      Sliders.agda
      Toggles.agda
      Menus.agda
      Tabs.agda
      Charts/
        Bar3D.agda
        Scatter3D.agda
        Surface.agda
        Network3D.agda
      Visualization/
        Volume.agda
        Globe.agda
        Terrain.agda
      Gizmos/
        Transform.agda
        Selection.agda
        Measure.agda
      Creative/
        Physics.agda
        Volumetric.agda
        Dimensional.agda
```

## Integration

WebGL controls return `SceneNode M A`, composable with regular scene elements:

```agda
myScene : Scene Model Msg
myScene = mkScene camera
  ( -- Regular 3D content
    mesh (box (vec3 1.0 1.0 1.0)) redMaterial [] identityTransform

  -- 3D bar chart
  ∷ barChart3D (vec3 5.0 3.0 2.0) salesData Nothing
      (mkTransform (vec3 -3.0 0.0 0.0) identityQuat unitScale)

  -- Control panel in 3D space
  ∷ group (mkTransform (vec3 3.0 1.5 0.0) identityQuat unitScale)
      ( slider3D 2.0 (vec3 1.0 0.0 0.0) brightness SetBrightness identityTransform
      ∷ toggle3D showWireframe ToggleWireframe
          (mkTransform (vec3 0.0 -0.5 0.0) identityQuat unitScale)
      ∷ [] )

  -- Transform gizmo on selected object
  ∷ when hasSelection (transformGizmo selectedTransform UpdateTransform)

  ∷ [] )
```

## Open Questions

1. **Text rendering** — 3D text is expensive. Options:
   - SDF (signed distance field) fonts
   - Billboarded 2D text
   - Texture atlases
   - HTML overlay for text-heavy UI

2. **Accessibility** — how to make 3D UI accessible?
   - Screen reader integration?
   - Keyboard navigation in 3D space?

3. **Performance** — complex controls add draw calls
   - Instancing for repeated elements?
   - LOD for distant controls?

4. **Input mapping** — 3D controls need careful interaction design
   - What does "click" mean on a sphere?
   - Drag direction in perspective view?
   - Touch input for 3D?

5. **VR/AR** — these controls could work in WebXR
   - Hand tracking interaction?
   - Gaze-based selection?
   - Haptic feedback?
