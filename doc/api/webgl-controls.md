# Agdelte.WebGL.Controls

3D UI controls library for WebGL scenes. Provides themed buttons, sliders, toggles, menus, and tabs.
All components return `SceneNode M Msg` and compose with WebGL scene trees.

## Design Principles

1. **3D Native** — controls rendered as 3D geometry (boxes, spheres, cylinders)
2. **Themeable** — `ControlTheme` configures colors, materials, dimensions
3. **Reactive** — model-driven via `bindTransform`, `bindMaterial`
4. **Interactive** — `onClick`, `onDrag` handlers for user input

## Quick Start

```agda
open import Agdelte.WebGL.Controls

-- Use controls in WebGL scene
view model =
  group identityTransform
    ( button darkTheme "Click me" ButtonClicked t1
    ∷ hslider darkTheme getValue SetValue t2
    ∷ toggle darkTheme isEnabled ToggleEnabled t3
    ∷ [])
```

---

## Core Infrastructure

### Theme

`Agdelte.WebGL.Controls.Theme`

```agda
record ControlTheme : Set where
  field
    primaryColor     : Color    -- active/selected elements
    secondaryColor   : Color    -- secondary accents
    accentColor      : Color    -- highlights
    backgroundColor  : Color    -- backgrounds
    foregroundColor  : Color    -- text, borders
    hoverColor       : Color    -- hover state
    activeColor      : Color    -- pressed state
    disabledColor    : Color    -- disabled elements
    surfaceMaterial  : Material -- default surface
    frameMaterial    : Material -- frames/borders
    cornerRadius     : Float    -- rounded corners
    borderWidth      : Float    -- border thickness
    padding          : Float    -- internal spacing

-- Built-in themes
defaultTheme : ControlTheme
darkTheme    : ControlTheme
lightTheme   : ControlTheme
```

### State

`Agdelte.WebGL.Controls.State`

```agda
data ControlState : Set where
  Normal   : ControlState
  Hovered  : ControlState
  Active   : ControlState
  Disabled : ControlState

stateMaterial : ControlTheme → ControlState → Material
disabledMaterial : ControlTheme → Material
```

### Text

`Agdelte.WebGL.Controls.Text`

```agda
-- Static label
label       : ControlTheme → String → Transform → SceneNode M Msg
leftLabel   : ControlTheme → String → Transform → SceneNode M Msg
rightLabel  : ControlTheme → String → Transform → SceneNode M Msg

-- Dynamic label (updates with model)
dynamicLabel : ControlTheme → (M → String) → Transform → SceneNode M Msg
dynamicValue : ControlTheme → (M → String) → Transform → SceneNode M Msg

-- Sized labels
sizedLabel : ControlTheme → Float → String → Transform → SceneNode M Msg
```

---

## Buttons

`Agdelte.WebGL.Controls.Buttons`

### Basic Button

```agda
record ButtonConfig : Set where
  field
    width   : Float
    height  : Float
    depth   : Float
    radius  : Float    -- corner radius

defaultButtonConfig : ButtonConfig

button3D : ∀ {M Msg}
         → ControlTheme
         → ButtonConfig
         → String        -- label
         → Msg           -- onClick message
         → Transform
         → SceneNode M Msg

-- Simple button with defaults
button : ∀ {M Msg}
       → ControlTheme → String → Msg → Transform
       → SceneNode M Msg
```

### Button Variants

```agda
-- Icon button (mesh instead of text)
iconButton : ∀ {M Msg}
           → ControlTheme → Geometry → Msg → Transform
           → SceneNode M Msg

-- Round floating action button
fabButton : ∀ {M Msg}
          → ControlTheme → Float → String → Msg → Transform
          → SceneNode M Msg

-- Labeled button with icon
labeledButton : ∀ {M Msg}
              → ControlTheme → String → Geometry → Msg → Transform
              → SceneNode M Msg
```

---

## Sliders

`Agdelte.WebGL.Controls.Sliders`

### Linear Sliders

```agda
record SliderConfig : Set where
  field
    length       : Float   -- track length
    trackRadius  : Float   -- track thickness
    handleRadius : Float   -- handle size
    showValue    : Bool    -- display value text

defaultSliderConfig : SliderConfig
thinSliderConfig    : SliderConfig
largeSliderConfig   : SliderConfig

-- Horizontal slider (value 0.0 to 1.0)
hslider3D : ∀ {M Msg}
          → ControlTheme
          → SliderConfig
          → (M → Float)       -- current value
          → (Float → Msg)     -- onChange
          → Transform
          → SceneNode M Msg

hslider : ∀ {M Msg}
        → ControlTheme → (M → Float) → (Float → Msg) → Transform
        → SceneNode M Msg

-- Vertical slider
vslider3D : ∀ {M Msg}
          → ControlTheme
          → SliderConfig
          → (M → Float)
          → (Float → Msg)
          → Transform
          → SceneNode M Msg

vslider : ∀ {M Msg}
        → ControlTheme → (M → Float) → (Float → Msg) → Transform
        → SceneNode M Msg
```

### Dial / Knob

```agda
record DialConfig : Set where
  field
    radius    : Float   -- dial radius
    thickness : Float   -- Z depth
    minAngle  : Float   -- start angle (radians)
    maxAngle  : Float   -- end angle (radians)

defaultDialConfig : DialConfig   -- -135° to +135°

dial3D : ∀ {M Msg}
       → ControlTheme
       → DialConfig
       → (M → Float)       -- value (0-1)
       → (Float → Msg)
       → Transform
       → SceneNode M Msg

dial : ∀ {M Msg}
     → ControlTheme → (M → Float) → (Float → Msg) → Transform
     → SceneNode M Msg
```

### Specialized Sliders

```agda
-- Slider with label and value display
labeledSlider : ∀ {M Msg}
              → ControlTheme
              → String              -- label
              → (M → Float)
              → (Float → Msg)
              → (Float → String)    -- value formatter
              → Transform
              → SceneNode M Msg

-- Integer slider (snaps to integers)
intSlider : ∀ {M Msg}
          → ControlTheme
          → ℕ → ℕ               -- min, max
          → (M → ℕ)
          → (ℕ → Msg)
          → Transform
          → SceneNode M Msg
```

---

## Toggles & Checkboxes

`Agdelte.WebGL.Controls.Toggles`

### Toggle Switch

```agda
record ToggleConfig : Set where
  field
    width  : Float
    height : Float
    depth  : Float

defaultToggleConfig : ToggleConfig

-- iOS-style toggle switch
toggle3D : ∀ {M Msg}
         → ControlTheme
         → ToggleConfig
         → (M → Bool)      -- is on?
         → Msg             -- toggle message
         → Transform
         → SceneNode M Msg

toggle : ∀ {M Msg}
       → ControlTheme → (M → Bool) → Msg → Transform
       → SceneNode M Msg

-- Toggle with label
labeledToggle : ∀ {M Msg}
              → ControlTheme → String → (M → Bool) → Msg → Transform
              → SceneNode M Msg
```

### Checkbox

```agda
record CheckboxConfig : Set where
  field
    size  : Float
    depth : Float

defaultCheckboxConfig : CheckboxConfig

checkbox3D : ∀ {M Msg}
           → ControlTheme
           → CheckboxConfig
           → (M → Bool)
           → Msg
           → Transform
           → SceneNode M Msg

checkbox : ∀ {M Msg}
         → ControlTheme → (M → Bool) → Msg → Transform
         → SceneNode M Msg

labeledCheckbox : ∀ {M Msg}
                → ControlTheme → String → (M → Bool) → Msg → Transform
                → SceneNode M Msg
```

### Radio Buttons

```agda
record RadioConfig : Set where
  field
    radius : Float
    depth  : Float

defaultRadioConfig : RadioConfig

-- Single radio button
radio3D : ∀ {M Msg}
        → ControlTheme
        → RadioConfig
        → (M → Bool)       -- is selected?
        → Msg              -- select message
        → Transform
        → SceneNode M Msg

labeledRadio : ∀ {M Msg}
             → ControlTheme → String → (M → Bool) → Msg → Transform
             → SceneNode M Msg

-- Radio group (vertical)
radioGroupVertical : ∀ {M Msg}
                   → ControlTheme
                   → Float                -- spacing
                   → (M → ℕ)              -- selected index
                   → (ℕ → Msg)            -- select handler
                   → List String          -- labels
                   → Transform
                   → SceneNode M Msg

-- Radio group (horizontal)
radioGroupHorizontal : ∀ {M Msg}
                     → ControlTheme
                     → Float
                     → (M → ℕ)
                     → (ℕ → Msg)
                     → List String
                     → Transform
                     → SceneNode M Msg
```

### Rocker Switch

```agda
-- Physical rocker-style switch
rockerSwitch3D : ∀ {M Msg}
               → ControlTheme
               → Float            -- size
               → (M → Bool)
               → Msg
               → Transform
               → SceneNode M Msg
```

---

## Menus

`Agdelte.WebGL.Controls.Menus`

### Menu Item

```agda
record MenuItem (Msg : Set) : Set where
  constructor menuItem
  field
    itemLabel   : String
    itemAction  : Msg
    itemEnabled : Bool

enabledItem  : ∀ {Msg} → String → Msg → MenuItem Msg
disabledItem : ∀ {Msg} → String → MenuItem Msg
```

### Dropdown Menu

```agda
record DropdownConfig : Set where
  field
    buttonWidth  : Float
    buttonHeight : Float
    itemHeight   : Float
    itemWidth    : Float

defaultDropdownConfig : DropdownConfig

dropdown3D : ∀ {M Msg}
           → ControlTheme
           → DropdownConfig
           → String               -- button label
           → (M → Bool)           -- is open?
           → Msg                  -- toggle message
           → List (MenuItem Msg)
           → Transform
           → SceneNode M Msg

dropdown : ∀ {M Msg}
         → ControlTheme → String → (M → Bool) → Msg
         → List (MenuItem Msg) → Transform
         → SceneNode M Msg
```

### Selection Dropdown

```agda
-- Dropdown that shows selected value
selectionDropdown : ∀ {M Msg}
                  → ControlTheme
                  → (M → ℕ)              -- selected index
                  → (M → Bool)           -- is open?
                  → Msg                  -- toggle
                  → (ℕ → Msg)            -- select handler
                  → List String          -- options
                  → Transform
                  → SceneNode M Msg
```

### Radial Menu

```agda
record RadialConfig : Set where
  field
    innerRadius : Float
    outerRadius : Float
    startAngle  : Float   -- radians
    sweepAngle  : Float   -- radians (2π for full circle)

defaultRadialConfig : RadialConfig

radialMenu3D : ∀ {M Msg}
             → ControlTheme
             → RadialConfig
             → (M → Bool)              -- is open?
             → List (MenuItem Msg)
             → Transform
             → SceneNode M Msg

radialMenu : ∀ {M Msg}
           → ControlTheme → (M → Bool) → List (MenuItem Msg) → Transform
           → SceneNode M Msg
```

### Context Menu

```agda
-- Appears at specified position
contextMenu3D : ∀ {M Msg}
              → ControlTheme
              → (M → Maybe Vec3)     -- position (Nothing = hidden)
              → List (MenuItem Msg)
              → SceneNode M Msg
```

---

## Tabs & Navigation

`Agdelte.WebGL.Controls.Tabs`

### Tab Bar

```agda
record TabBarConfig : Set where
  field
    tabWidth   : Float
    tabHeight  : Float
    tabDepth   : Float
    spacing    : Float
    horizontal : Bool    -- true = horizontal, false = vertical

defaultTabBarConfig    : TabBarConfig
verticalTabBarConfig   : TabBarConfig

tabBar3D : ∀ {M Msg}
         → ControlTheme
         → TabBarConfig
         → (M → ℕ)              -- active tab index
         → (ℕ → Msg)            -- select handler
         → List String          -- tab labels
         → Transform
         → SceneNode M Msg

tabBar : ∀ {M Msg}
       → ControlTheme → (M → ℕ) → (ℕ → Msg) → List String → Transform
       → SceneNode M Msg

verticalTabBar : ∀ {M Msg}
               → ControlTheme → (M → ℕ) → (ℕ → Msg) → List String → Transform
               → SceneNode M Msg
```

### Tab Panel

```agda
-- Tab bar with content panels (only active content rendered)
tabPanel : ∀ {M Msg}
         → ControlTheme
         → (M → ℕ)                            -- active index
         → (ℕ → Msg)                          -- select handler
         → List (String × SceneNode M Msg)    -- (label, content) pairs
         → Transform
         → SceneNode M Msg
```

### Segmented Control

```agda
-- iOS-style segmented control
segmentedControl : ∀ {M Msg}
                 → ControlTheme
                 → (M → ℕ)
                 → (ℕ → Msg)
                 → List String
                 → Transform
                 → SceneNode M Msg
```

### Pagination Dots

```agda
-- Page indicator dots (like carousel)
paginationDots : ∀ {M Msg}
               → ControlTheme
               → ℕ                   -- total count
               → (M → ℕ)             -- current index
               → (ℕ → Msg)           -- select handler
               → Transform
               → SceneNode M Msg
```

---

## Module Structure

```
Agdelte/WebGL/Controls.agda           -- re-exports all
Agdelte/WebGL/Controls/
  Theme.agda                          -- ControlTheme, themes
  State.agda                          -- ControlState
  Text.agda                           -- label, dynamicLabel
  Buttons.agda                        -- button, fabButton
  Sliders.agda                        -- hslider, vslider, dial
  Toggles.agda                        -- toggle, checkbox, radio
  Menus.agda                          -- dropdown, radialMenu
  Tabs.agda                           -- tabBar, tabPanel
```

---

## Example Usage

```agda
module MyWebGLApp where

open import Agdelte.WebGL
open import Agdelte.WebGL.Controls

-- Model
record Model : Set where
  field
    volume     : Float
    isMuted    : Bool
    activeTab  : ℕ

data Msg : Set where
  SetVolume  : Float → Msg
  ToggleMute : Msg
  SelectTab  : ℕ → Msg

-- View
view : Model → SceneNode Model Msg
view m =
  let theme = darkTheme
      t1 = mkTransform (vec3 0.0 0.5 0.0) identityQuat (vec3 1.0 1.0 1.0)
      t2 = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      t3 = mkTransform (vec3 0.0 -0.5 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group identityTransform
       ( labeledSlider theme "Volume" Model.volume SetVolume formatPercent t1
       ∷ labeledToggle theme "Mute" Model.isMuted ToggleMute t2
       ∷ tabBar theme Model.activeTab SelectTab ("Tab 1" ∷ "Tab 2" ∷ []) t3
       ∷ [])
  where
    formatPercent : Float → String
    formatPercent f = show (round (f * 100.0)) ++ "%"
```

---

## Input Fields

`Agdelte.WebGL.Controls.Input`

### Text Input

```agda
record InputConfig : Set where
  field
    width     : Float
    height    : Float
    depth     : Float
    maxLength : ℕ

defaultInputConfig : InputConfig

textInput3D : ∀ {M Msg}
            → ControlTheme
            → InputConfig
            → (M → String)          -- current value
            → (String → Msg)        -- onChange
            → Transform
            → SceneNode M Msg

textInput : ∀ {M Msg}
          → ControlTheme → (M → String) → (String → Msg) → Transform
          → SceneNode M Msg
```

### Number Input

```agda
numberInput3D : ∀ {M Msg}
              → ControlTheme
              → InputConfig
              → (M → Float)
              → (Float → Msg)
              → Transform
              → SceneNode M Msg
```

### Color Picker

```agda
record ColorPickerConfig : Set where
  field
    size  : Float
    depth : Float

colorPicker3D : ∀ {M Msg}
              → ControlTheme
              → ColorPickerConfig
              → (M → GlColor)
              → (GlColor → Msg)
              → Transform
              → SceneNode M Msg
```

---

## Charts

### Bar Chart 3D

`Agdelte.WebGL.Controls.Charts.Bar3D`

```agda
record BarData : Set where
  field
    barLabel : String
    barValue : Float
    barColor : GlColor

record BarChartConfig : Set where
  field
    width       : Float
    height      : Float
    depth       : Float
    barWidth    : Float
    barSpacing  : Float

barChart3D : ∀ {M Msg}
           → ControlTheme
           → BarChartConfig
           → (M → List BarData)
           → Transform
           → SceneNode M Msg
```

### Scatter Plot 3D

`Agdelte.WebGL.Controls.Charts.Scatter3D`

```agda
record ScatterPoint : Set where
  field
    pointX     : Float
    pointY     : Float
    pointZ     : Float
    pointColor : GlColor
    pointSize  : Float

scatterPlot3D : ∀ {M Msg}
              → ControlTheme
              → ScatterConfig
              → (M → List ScatterPoint)
              → Transform
              → SceneNode M Msg
```

### Surface Plot

`Agdelte.WebGL.Controls.Charts.Surface`

```agda
surfacePlot3D : ∀ {M Msg}
              → ControlTheme
              → SurfaceConfig
              → (M → ℕ → ℕ → Float)    -- height function (x, z) → y
              → (Float → GlColor)       -- color mapping
              → Transform
              → SceneNode M Msg
```

### Network Graph 3D

`Agdelte.WebGL.Controls.Charts.Network3D`

```agda
record NetworkNode : Set where
  field
    nodeId       : ℕ
    nodeLabel    : String
    nodePosition : Vec3
    nodeColor    : GlColor

record NetworkEdge : Set where
  field
    edgeFrom  : ℕ
    edgeTo    : ℕ
    edgeColor : GlColor

networkGraph3D : ∀ {M Msg}
               → ControlTheme
               → NetworkConfig
               → (M → List NetworkNode)
               → (M → List NetworkEdge)
               → (ℕ → Msg)             -- node click handler
               → Transform
               → SceneNode M Msg
```

---

## Audio Visualization

### Frequency Spectrum

`Agdelte.WebGL.Controls.Audio.Spectrum`

```agda
frequencyBars3D : ∀ {M Msg}
                → ControlTheme
                → SpectrumConfig
                → (M → List Float)     -- frequency magnitudes (0-1)
                → Transform
                → SceneNode M Msg

circularSpectrum3D : ∀ {M Msg}
                   → ControlTheme
                   → CircularSpectrumConfig
                   → (M → List Float)
                   → Transform
                   → SceneNode M Msg
```

### Waveform Display

`Agdelte.WebGL.Controls.Audio.Waveform`

```agda
oscilloscope3D : ∀ {M Msg}
               → ControlTheme
               → WaveformConfig
               → GlColor
               → (M → List Float)      -- samples (-1 to 1)
               → Transform
               → SceneNode M Msg

multiChannelWaveform3D : ∀ {M Msg}
                       → ControlTheme
                       → MultiChannelConfig
                       → List GlColor         -- channel colors
                       → (M → List (List Float))
                       → Transform
                       → SceneNode M Msg

lissajous3D : ∀ {M Msg}
            → ControlTheme
            → LissajousConfig
            → GlColor
            → (M → List Float)         -- X channel
            → (M → List Float)         -- Y channel
            → Transform
            → SceneNode M Msg

vuMeter3D : ∀ {M Msg}
          → ControlTheme
          → VUMeterConfig
          → (M → Float)                -- level (0-1)
          → Transform
          → SceneNode M Msg
```

---

## Gizmos

### Transform Gizmo

`Agdelte.WebGL.Controls.Gizmos.Transform`

```agda
data GizmoMode : Set where
  Translate : GizmoMode
  Rotate    : GizmoMode
  Scale     : GizmoMode

translateGizmo : ∀ {M Msg}
               → GizmoStyle
               → (Vec3 → Msg)          -- position change handler
               → Transform
               → SceneNode M Msg

rotateGizmo : ∀ {M Msg}
            → GizmoStyle
            → (Quaternion → Msg)       -- rotation change handler
            → Transform
            → SceneNode M Msg

scaleGizmo : ∀ {M Msg}
           → GizmoStyle
           → (Vec3 → Msg)              -- scale change handler
           → Transform
           → SceneNode M Msg

combinedGizmo : ∀ {M Msg}
              → GizmoStyle
              → (M → GizmoMode)
              → (Vec3 → Msg)
              → (Quaternion → Msg)
              → (Vec3 → Msg)
              → Transform
              → SceneNode M Msg
```

### Selection Gizmo

`Agdelte.WebGL.Controls.Gizmos.Selection`

```agda
record SelectionStyle : Set where
  field
    lineColor   : GlColor
    lineWidth   : Float
    handleColor : GlColor
    handleSize  : Float
    fillColor   : GlColor
    dashLength  : Float

boundingBox3D : ∀ {M Msg}
              → SelectionStyle
              → (M → Maybe (Vec3 × Vec3))    -- min/max corners
              → SceneNode M Msg

selectionBox3D : ∀ {M Msg}
               → SelectionStyle
               → (M → Maybe (Vec3 × Vec3))
               → (Vec3 → Vec3 → Msg)          -- resize handler
               → SceneNode M Msg

highlightOutline : ∀ {M Msg}
                 → SelectionStyle
                 → Vec3                       -- size
                 → Transform
                 → SceneNode M Msg

selectionBrackets : ∀ {M Msg}
                  → SelectionStyle
                  → Vec3
                  → Transform
                  → SceneNode M Msg
```

### Measurement Gizmo

`Agdelte.WebGL.Controls.Gizmos.Measure`

```agda
distanceGizmo : ∀ {M Msg}
              → MeasureStyle
              → (M → Vec3)              -- start point
              → (M → Vec3)              -- end point
              → Transform
              → SceneNode M Msg

angleGizmo : ∀ {M Msg}
           → MeasureStyle
           → (M → Vec3)                 -- vertex
           → (M → Vec3)                 -- arm 1
           → (M → Vec3)                 -- arm 2
           → Transform
           → SceneNode M Msg

gridPlane : ∀ {M Msg}
          → MeasureStyle
          → Float                       -- size
          → Float                       -- spacing
          → Transform
          → SceneNode M Msg

ruler3D : ∀ {M Msg}
        → MeasureStyle
        → (M → Vec3)
        → (M → Vec3)
        → Float                         -- major tick interval
        → Float                         -- minor tick interval
        → Transform
        → SceneNode M Msg
```

---

## Module Structure

```
Agdelte/WebGL/Controls.agda           -- re-exports all
Agdelte/WebGL/Controls/
  Theme.agda                          -- ControlTheme, themes
  State.agda                          -- ControlState
  Text.agda                           -- label, dynamicLabel
  Buttons.agda                        -- button, fabButton
  Sliders.agda                        -- hslider, vslider, dial
  Toggles.agda                        -- toggle, checkbox, radio
  Menus.agda                          -- dropdown, radialMenu
  Tabs.agda                           -- tabBar, tabPanel
  Input.agda                          -- textInput, numberInput, colorPicker
  Charts/
    Bar3D.agda                        -- barChart3D
    Scatter3D.agda                    -- scatterPlot3D
    Surface.agda                      -- surfacePlot3D
    Network3D.agda                    -- networkGraph3D
  Audio/
    Spectrum.agda                     -- frequencyBars3D, circularSpectrum3D
    Waveform.agda                     -- oscilloscope3D, vuMeter3D, lissajous3D
  Gizmos/
    Transform.agda                    -- translateGizmo, rotateGizmo, scaleGizmo
    Selection.agda                    -- boundingBox3D, selectionBox3D
    Measure.agda                      -- distanceGizmo, angleGizmo, ruler3D
```
