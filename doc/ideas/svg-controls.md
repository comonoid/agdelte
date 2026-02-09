# SVG Controls Library (Agdelte.Svg.Controls)

Pure Agda library for data visualization and SVG-based UI components.
Built on top of `Agdelte.Svg` module. Returns `Node M A`, composable with HTML controls.

## Design Principles

1. **Declarative** — describe data, not drawing commands
2. **Reactive** — automatic updates when model changes
3. **Composable** — combine charts, add annotations, embed in HTML
4. **Responsive** — ViewBox-based scaling, works at any size
5. **Animated** — smooth transitions via `whenT` and SMIL

## Charts

### Line Chart
Time series, trends, continuous data.

```agda
record LineChartConfig : Set where
  constructor mkLineChartConfig
  field
    width       : Float
    height      : Float
    xLabel      : Maybe String
    yLabel      : Maybe String
    showGrid    : Bool
    showDots    : Bool
    animate     : Bool

record DataPoint : Set where
  constructor mkDataPoint
  field x : Float ; y : Float

record LineSeries (M : Set) (A : Set) : Set where
  constructor mkLineSeries
  field
    name   : String
    color  : Color
    data   : M → List DataPoint
    onClick : Maybe (DataPoint → A)

lineChart : ∀ {M A}
          → LineChartConfig
          → List (LineSeries M A)
          → Node M A

-- Simple version for single series
simpleLineChart : ∀ {M A}
                → Float → Float              -- width, height
                → Color
                → (M → List DataPoint)
                → Node M A
```

### Area Chart
Like line chart but filled area underneath.

```agda
areaChart : ∀ {M A}
          → LineChartConfig
          → List (LineSeries M A)
          → Node M A

-- Stacked area
stackedAreaChart : ∀ {M A}
                 → LineChartConfig
                 → List (LineSeries M A)
                 → Node M A
```

### Bar Chart
Categorical comparisons.

```agda
record BarData (A : Set) : Set where
  constructor mkBarData
  field
    label   : String
    value   : Float
    color   : Maybe Color        -- override default
    onClick : Maybe A

barChart : ∀ {M A}
         → Float → Float         -- width, height
         → Bool                  -- horizontal?
         → (M → List (BarData A))
         → Node M A

-- Grouped bars (multiple series per category)
groupedBarChart : ∀ {M A}
                → Float → Float
                → List String              -- series names
                → List Color               -- series colors
                → (M → List (List Float))  -- data[category][series]
                → Node M A

-- Stacked bars
stackedBarChart : ∀ {M A}
                → Float → Float
                → List String
                → List Color
                → (M → List (List Float))
                → Node M A
```

### Pie / Donut Chart
Part-to-whole relationships.

```agda
record PieSlice (A : Set) : Set where
  constructor mkPieSlice
  field
    label   : String
    value   : Float
    color   : Color
    onClick : Maybe A

pieChart : ∀ {M A}
         → Float                           -- radius
         → (M → List (PieSlice A))
         → Node M A

donutChart : ∀ {M A}
           → Float → Float                 -- outer, inner radius
           → (M → List (PieSlice A))
           → Node M A

-- With center content (e.g., total value)
donutWithCenter : ∀ {M A}
                → Float → Float
                → (M → List (PieSlice A))
                → Node M A                 -- center content
                → Node M A
```

### Scatter Plot
Correlation, distribution of points.

```agda
record ScatterPoint (A : Set) : Set where
  constructor mkScatterPoint
  field
    x       : Float
    y       : Float
    size    : Maybe Float        -- bubble size
    color   : Maybe Color
    label   : Maybe String
    onClick : Maybe A

scatterPlot : ∀ {M A}
            → Float → Float      -- width, height
            → (M → List (ScatterPoint A))
            → Node M A

-- Bubble chart (scatter with size dimension)
bubbleChart : ∀ {M A}
            → Float → Float
            → (M → List (ScatterPoint A))
            → Node M A
```

### Radar / Spider Chart
Multi-dimensional comparison.

```agda
record RadarAxis : Set where
  constructor mkRadarAxis
  field
    name : String
    max  : Float

record RadarSeries : Set where
  constructor mkRadarSeries
  field
    name   : String
    color  : Color
    values : List Float          -- one per axis

radarChart : ∀ {M A}
           → Float               -- radius
           → List RadarAxis
           → (M → List RadarSeries)
           → Node M A
```

### Spectrum Visualization

```agda
-- Frequency spectrum (audio, signal analysis)
spectrum : ∀ {M A}
         → Float → Float          -- width, height
         → (M → List Float)       -- frequency bins (magnitudes)
         → Color
         → Node M A

-- Spectrum with gradient coloring (by intensity)
spectrumGradient : ∀ {M A}
                 → Float → Float
                 → (Float → Color)  -- magnitude to color
                 → (M → List Float)
                 → Node M A

-- Mirrored spectrum (like audio visualizers)
mirroredSpectrum : ∀ {M A}
                 → Float → Float
                 → Color
                 → (M → List Float)
                 → Node M A

-- Circular spectrum (radial bars)
radialSpectrum : ∀ {M A}
               → Float → Float    -- inner, outer radius
               → Color
               → (M → List Float)
               → Node M A

-- Waveform display (time domain)
waveform : ∀ {M A}
         → Float → Float
         → Color
         → (M → List Float)       -- samples
         → Node M A

-- Oscilloscope style (with grid, trigger)
oscilloscope : ∀ {M A}
             → Float → Float
             → Color
             → Bool               -- show grid
             → (M → List Float)
             → Node M A

-- Spectrogram (2D: time × frequency, color = magnitude)
-- Static snapshot or scrolling
spectrogram : ∀ {M A}
            → Float → Float
            → (Float → Color)     -- magnitude to color
            → (M → List (List Float))  -- time × frequency bins
            → Node M A
```

### Audio Meters & Monitoring

```agda
-- Peak meter with hold indicator
peakMeter : ∀ {M A}
          → Float → Float         -- width, height
          → (M → Float)           -- current level (0-1)
          → (M → Float)           -- peak hold
          → Node M A

-- Classic VU meter (needle style)
vuMeter : ∀ {M A}
        → Float                   -- radius
        → (M → Float)             -- level in dB (-20 to +3)
        → Node M A

-- Stereo level meter (L/R bars)
stereoMeter : ∀ {M A}
            → Float → Float
            → (M → Float × Float) -- left, right levels
            → Node M A

-- Loudness meter (LUFS standard)
loudnessMeter : ∀ {M A}
              → Float → Float
              → (M → Float)       -- momentary LUFS
              → (M → Float)       -- short-term LUFS
              → (M → Float)       -- integrated LUFS
              → Node M A

-- Goniometer / Vectorscope (stereo phase visualization)
goniometer : ∀ {M A}
           → Float                -- size
           → Color
           → (M → List (Float × Float))  -- L/R sample pairs
           → Node M A

-- Stereo correlation meter (-1 to +1)
correlationMeter : ∀ {M A}
                 → Float → Float
                 → (M → Float)    -- correlation coefficient
                 → Node M A

-- Phase meter (simple left/right indicator)
phaseMeter : ∀ {M A}
           → Float → Float
           → (M → Float)          -- -1 (out of phase) to +1 (in phase)
           → Node M A
```

### MIDI & Musical

```agda
-- Piano roll (MIDI note display)
pianoRoll : ∀ {M A}
          → Float → Float
          → ℕ → ℕ                 -- note range (low, high)
          → (M → List (Float × Float × ℕ × Float))  -- start, duration, note, velocity
          → Maybe (ℕ → Float → A) -- note click (note, time)
          → Node M A

-- Piano keyboard (interactive)
pianoKeyboard : ∀ {M A}
              → Float             -- total width
              → ℕ → ℕ             -- start/end octave
              → (M → List ℕ)      -- currently pressed notes (MIDI numbers)
              → (ℕ → A)           -- note on/off
              → Node M A

-- Drum grid / Step sequencer
stepSequencer : ∀ {M A}
              → Float → Float
              → ℕ                 -- steps
              → List String       -- row labels (instruments)
              → (M → List (List Bool))  -- grid state
              → (ℕ → ℕ → A)       -- toggle (row, step)
              → (M → ℕ)           -- current step (playhead)
              → Node M A

-- Chord diagram (guitar/ukulele style)
chordDiagram : ∀ {M A}
             → Float
             → ℕ                  -- strings
             → ℕ                  -- frets shown
             → (M → List (ℕ × ℕ)) -- (string, fret) fingerings
             → Node M A

-- Circle of fifths
circleOfFifths : ∀ {M A}
               → Float            -- radius
               → (M → Maybe String)  -- highlighted key
               → (String → A)     -- select key
               → Node M A
```

### Synthesis & Processing

```agda
-- EQ curve display (frequency response)
eqCurve : ∀ {M A}
        → Float → Float
        → (M → List (Float × Float × Float))  -- freq (Hz), gain (dB), Q
        → Node M A

-- Parametric EQ with draggable points
parametricEQ : ∀ {M A}
             → Float → Float
             → (M → List (Float × Float × Float))
             → (ℕ → Float → Float → Float → A)  -- update band
             → Node M A

-- Compressor transfer curve
compressorCurve : ∀ {M A}
                → Float → Float
                → (M → Float)     -- threshold (dB)
                → (M → Float)     -- ratio
                → (M → Float)     -- knee (dB)
                → (M → Float)     -- current input level (for dot)
                → Node M A

-- Compressor gain reduction meter
gainReductionMeter : ∀ {M A}
                   → Float → Float
                   → (M → Float)  -- GR in dB (negative)
                   → Node M A

-- ADSR envelope display
envelopeDisplay : ∀ {M A}
                → Float → Float
                → (M → Float × Float × Float × Float)  -- A, D, S level, R times
                → (M → Maybe Float)  -- current envelope position
                → Node M A

-- ADSR envelope editor (draggable points)
envelopeEditor : ∀ {M A}
               → Float → Float
               → (M → Float × Float × Float × Float)
               → (Float → Float → Float → Float → A)  -- update ADSR
               → Node M A

-- LFO waveform selector/display
lfoDisplay : ∀ {M A}
           → Float → Float
           → (M → String)         -- waveform type (sine, saw, square, etc.)
           → (M → Float)          -- rate
           → (M → Float)          -- current phase
           → Node M A

-- Filter frequency response
filterCurve : ∀ {M A}
            → Float → Float
            → (M → String)        -- type (lowpass, highpass, bandpass, etc.)
            → (M → Float)         -- cutoff
            → (M → Float)         -- resonance/Q
            → Node M A
```

### Waveform Editing

```agda
-- Waveform display with selection
waveformEditor : ∀ {M A}
               → Float → Float
               → Color
               → (M → List Float)           -- samples
               → (M → Maybe (Float × Float)) -- selection (start, end as 0-1)
               → (Float → Float → A)         -- select region
               → Node M A

-- Waveform with markers/cues
waveformWithMarkers : ∀ {M A}
                    → Float → Float
                    → Color
                    → (M → List Float)
                    → (M → List (Float × String × Color))  -- position, label, color
                    → (Float → A)            -- click at position
                    → Node M A

-- Zoomed waveform (with scroll position)
zoomableWaveform : ∀ {M A}
                 → Float → Float
                 → Color
                 → (M → List Float)
                 → (M → Float × Float)       -- view range (start, end as 0-1)
                 → (Float → Float → A)       -- set view range
                 → Node M A

-- Multi-track waveform display
multiTrackWaveform : ∀ {M A}
                   → Float → Float           -- total size
                   → List (String × Color)   -- track names and colors
                   → (M → List (List Float)) -- samples per track
                   → (M → ℕ)                 -- selected track
                   → (ℕ → A)                 -- select track
                   → Node M A
```

### Heatmap
2D density/intensity visualization.

```agda
heatmap : ∀ {M A}
        → Float → Float                    -- width, height
        → List String                      -- x labels
        → List String                      -- y labels
        → (Float → Color)                  -- value to color
        → (M → List (List Float))          -- data[row][col]
        → Maybe (ℕ → ℕ → A)                -- onClick (row, col)
        → Node M A
```

### Treemap
Hierarchical data as nested rectangles.

```agda
record TreemapNode (A : Set) : Set where
  constructor mkTreemapNode
  field
    label    : String
    value    : Float
    color    : Maybe Color
    children : List (TreemapNode A)
    onClick  : Maybe A

treemap : ∀ {M A}
        → Float → Float
        → (M → TreemapNode A)
        → Node M A
```

### Sankey Diagram
Flow/transfer between nodes.

```agda
record SankeyNode : Set where
  constructor mkSankeyNode
  field
    id    : String
    label : String

record SankeyLink : Set where
  constructor mkSankeyLink
  field
    source : String              -- node id
    target : String              -- node id
    value  : Float

sankeyDiagram : ∀ {M A}
              → Float → Float
              → (M → List SankeyNode)
              → (M → List SankeyLink)
              → Node M A
```

## Gauges & Indicators

### Gauge / Meter
Single value display with min/max.

```agda
record GaugeConfig : Set where
  constructor mkGaugeConfig
  field
    min       : Float
    max       : Float
    thresholds : List (Float × Color)  -- (value, color) for zones
    label     : Maybe String
    showValue : Bool

gauge : ∀ {M A}
      → Float                    -- radius
      → GaugeConfig
      → (M → Float)              -- current value
      → Node M A

-- Half-circle gauge
semicircleGauge : ∀ {M A}
                → Float → GaugeConfig → (M → Float) → Node M A

-- Linear gauge (horizontal/vertical)
linearGauge : ∀ {M A}
            → Float → Float      -- width, height
            → Bool               -- horizontal?
            → GaugeConfig
            → (M → Float)
            → Node M A
```

### Sparkline
Tiny inline chart.

```agda
sparkline : ∀ {M A}
          → Float → Float        -- width, height
          → Color
          → (M → List Float)     -- values
          → Node M A

sparklineBar : ∀ {M A}
             → Float → Float → Color → (M → List Float) → Node M A
```

### KPI Card
Key metric with trend indicator.

```agda
data Trend : Set where
  Up Down Flat : Trend

kpiCard : ∀ {M A}
        → String                 -- label
        → (M → String)           -- value (formatted)
        → (M → Trend)
        → (M → String)           -- change text ("+5%")
        → Node M A
```

### Progress Ring
Circular progress indicator.

```agda
progressRing : ∀ {M A}
             → Float             -- radius
             → Float             -- stroke width
             → Color
             → (M → Float)       -- 0.0 to 1.0
             → Node M A

-- With center label
progressRingLabeled : ∀ {M A}
                    → Float → Float → Color
                    → (M → Float)
                    → (M → String)  -- center text
                    → Node M A
```

## Diagrams

### Network Graph
Nodes and edges, force-directed or fixed layout.

```agda
record GraphNode (A : Set) : Set where
  constructor mkGraphNode
  field
    id      : String
    label   : String
    x       : Maybe Float        -- fixed position (Nothing = auto)
    y       : Maybe Float
    color   : Color
    size    : Float
    onClick : Maybe A

record GraphEdge : Set where
  constructor mkGraphEdge
  field
    source    : String
    target    : String
    label     : Maybe String
    directed  : Bool
    weight    : Float            -- affects thickness

networkGraph : ∀ {M A}
             → Float → Float
             → (M → List (GraphNode A))
             → (M → List GraphEdge)
             → Node M A
```

### Flowchart
Process flow with shaped nodes.

```agda
data FlowShape : Set where
  Rectangle Rounded Diamond Oval Parallelogram : FlowShape

record FlowNode (A : Set) : Set where
  constructor mkFlowNode
  field
    id      : String
    label   : String
    shape   : FlowShape
    x       : Float
    y       : Float
    onClick : Maybe A

record FlowEdge : Set where
  constructor mkFlowEdge
  field
    source : String
    target : String
    label  : Maybe String

flowchart : ∀ {M A}
          → Float → Float
          → (M → List (FlowNode A))
          → (M → List FlowEdge)
          → Node M A
```

### Timeline
Events along a time axis.

```agda
record TimelineEvent (A : Set) : Set where
  constructor mkTimelineEvent
  field
    time    : Float              -- x position (timestamp or index)
    label   : String
    detail  : Maybe String
    color   : Color
    onClick : Maybe A

timeline : ∀ {M A}
         → Float → Float
         → Bool                  -- horizontal?
         → (M → List (TimelineEvent A))
         → Node M A
```

### Org Chart
Hierarchical tree structure.

```agda
record OrgNode (A : Set) : Set where
  constructor mkOrgNode
  field
    id       : String
    label    : String
    sublabel : Maybe String
    children : List (OrgNode A)
    onClick  : Maybe A

orgChart : ∀ {M A}
         → Float → Float
         → (M → OrgNode A)
         → Node M A
```

## Geographic

### Simple Map
SVG-based map with regions.

```agda
record MapRegion (A : Set) : Set where
  constructor mkMapRegion
  field
    id      : String             -- region code
    path    : String             -- SVG path data
    value   : Maybe Float        -- for choropleth coloring
    onClick : Maybe A

choroplethMap : ∀ {M A}
              → Float → Float
              → (Float → Color)  -- value to color
              → List (MapRegion A)
              → Node M A

-- Pre-built maps (paths included)
worldMap : ∀ {M A} → Float → Float → (String → M → Float) → (String → A) → Node M A
usaMap   : ∀ {M A} → Float → Float → (String → M → Float) → (String → A) → Node M A
europeMap : ∀ {M A} → Float → Float → (String → M → Float) → (String → A) → Node M A
```

## SVG UI Widgets

Controls designed for use **inside** SVG scenes (on diagrams, charts, maps).
Not a duplication of HTML controls — these serve different purposes:

- Embedded in SVG ViewBox (consistent scaling with the visualization)
- Unusual shapes impossible in HTML (radial, curved, along path)
- Unified styling with surrounding SVG graphics

For regular rectangular UI, use `Agdelte.Html.Controls` instead.

### Buttons & Toolbars

```agda
-- Simple button (for toolbars on diagrams)
svgButton : ∀ {M A}
          → Float → Float        -- width, height
          → String               -- label
          → A                    -- click message
          → SvgNode M A

-- Icon button
svgIconButton : ∀ {M A}
              → Float            -- size
              → IconName
              → A
              → SvgNode M A

-- Toolbar (horizontal/vertical group of buttons)
svgToolbar : ∀ {M A}
           → Bool                -- horizontal?
           → List (SvgNode M A)  -- buttons
           → SvgNode M A

-- Floating action button (circular)
fab : ∀ {M A} → Float → IconName → Color → A → SvgNode M A
```

### Zoom & Pan Controls

```agda
-- Standard zoom controls (+, -, reset)
zoomControls : ∀ {M A}
             → A → A → A         -- zoomIn, zoomOut, reset
             → SvgNode M A

-- Zoom slider (vertical)
zoomSlider : ∀ {M A}
           → Float               -- height
           → (M → Float)         -- zoom level 0.0-1.0
           → (Float → A)
           → SvgNode M A

-- Mini-map for pan navigation
miniMap : ∀ {M A}
        → Float → Float          -- size
        → SvgNode M A            -- thumbnail content
        → (M → Float × Float)    -- viewport position
        → (Float → Float → A)    -- pan to
        → SvgNode M A
```

### Radial & Circular

```agda
-- Radial/pie menu (appears around a point)
radialMenu : ∀ {M A}
           → Float               -- radius
           → (M → Bool)          -- isOpen
           → List (String × IconName × A)  -- items
           → SvgNode M A

-- Arc tabs (tabs arranged in an arc)
arcTabs : ∀ {M A}
        → Float                  -- radius
        → Float → Float          -- start/end angle (radians)
        → (M → ℕ)                -- active tab
        → (ℕ → A)                -- select tab
        → List String            -- labels
        → SvgNode M A

-- Circular slider (knob)
dialKnob : ∀ {M A}
         → Float                 -- radius
         → Float → Float         -- min, max value
         → (M → Float)           -- current value
         → (Float → A)
         → SvgNode M A

-- Ring selector (choose from segments)
ringSelector : ∀ {M A}
             → Float → Float     -- outer, inner radius
             → (M → ℕ)           -- selected
             → (ℕ → A)
             → List (String × Color)
             → SvgNode M A
```

### Sliders & Inputs

```agda
-- Linear slider (for settings on chart)
svgSlider : ∀ {M A}
          → Float                -- length
          → Bool                 -- horizontal?
          → Float → Float        -- min, max
          → (M → Float)
          → (Float → A)
          → SvgNode M A

-- Range slider (two handles)
svgRangeSlider : ∀ {M A}
               → Float → Bool → Float → Float
               → (M → Float × Float)
               → (Float → Float → A)
               → SvgNode M A

-- Toggle switch
svgToggle : ∀ {M A}
          → Float                -- width
          → (M → Bool)
          → A                    -- toggle message
          → SvgNode M A
```

### Context Menu & Tooltips

```agda
-- Context menu (right-click or long-press)
svgContextMenu : ∀ {M A}
               → (M → Maybe (Float × Float))  -- position (Nothing = hidden)
               → A                             -- close message
               → List (String × A)             -- items
               → SvgNode M A

-- Rich tooltip (positioned near element)
svgTooltip : ∀ {M A}
           → (M → Maybe (Float × Float × String))  -- (x, y, content)
           → SvgNode M A

-- Popover with custom content
svgPopover : ∀ {M A}
           → (M → Maybe (Float × Float))
           → A                                 -- close
           → SvgNode M A                       -- content
           → SvgNode M A
```

### Annotations & Overlays

```agda
-- Callout (label with line pointing to something)
callout : ∀ {M A}
        → Float × Float          -- target point
        → Float × Float          -- label position
        → String                 -- text
        → SvgNode M A

-- Measurement line (with dimension)
measureLine : ∀ {M A}
            → Float × Float → Float × Float
            → (Float → String)   -- formatter
            → SvgNode M A

-- Selection rectangle (for area selection)
selectionRect : ∀ {M A}
              → (M → Maybe (Float × Float × Float × Float))  -- x, y, w, h
              → SvgNode M A

-- Crosshair cursor
crosshair : ∀ {M A}
          → (M → Maybe (Float × Float))
          → SvgNode M A
```

### Legends & Labels

```agda
-- Chart legend (list of series with colors)
legend : ∀ {M A}
       → Bool                    -- horizontal?
       → List (String × Color)
       → SvgNode M A

-- Interactive legend (click to toggle series)
interactiveLegend : ∀ {M A}
                  → Bool
                  → (M → List Bool)        -- which are enabled
                  → (ℕ → A)                -- toggle
                  → List (String × Color)
                  → SvgNode M A

-- Axis labels (for custom positioning)
axisLabel : ∀ {M A}
          → String
          → Float                -- rotation (degrees)
          → SvgNode M A
```

### Creative / Exotic Controls

Controls that are **impossible or impractical in HTML** — leveraging SVG's unique
capabilities: arbitrary shapes, curves, transforms, masks.

#### Path-based Controls

```agda
-- Dropdown with items arranged along a curve
curvedDropdown : ∀ {M A}
               → Path              -- bezier/arc path for item placement
               → (M → Bool)        -- isOpen
               → (M → ℕ)           -- selected
               → (ℕ → A)
               → List String
               → SvgNode M A

-- Slider along arbitrary path (not just straight line)
pathSlider : ∀ {M A}
           → Path
           → (M → Float)          -- position 0.0-1.0 along path
           → (Float → A)
           → SvgNode M A

-- Text input that flows along a curve
curvedInput : ∀ {M A}
            → Path
            → (M → String)
            → (String → A)
            → SvgNode M A

-- Tabs arranged along a wave/sine curve
waveTabs : ∀ {M A}
         → Float                  -- width
         → Float                  -- amplitude
         → Float                  -- frequency
         → (M → ℕ) → (ℕ → A)
         → List String
         → SvgNode M A
```

#### Non-rectangular Layouts

```agda
-- Hexagonal grid menu (strategy games style)
hexMenu : ∀ {M A}
        → Float                   -- cell size
        → ℕ                       -- rings (1 = just center, 2 = center + 6, etc.)
        → List (IconName × String × A)
        → SvgNode M A

-- Circular/radial dropdown (items in a ring)
circularDropdown : ∀ {M A}
                 → Float           -- radius
                 → (M → Bool)      -- isOpen
                 → (M → ℕ)
                 → (ℕ → A)
                 → List (String × IconName)
                 → SvgNode M A

-- Triangular button grid
triangleGrid : ∀ {M A}
             → Float              -- size
             → List (List (Maybe (String × A)))  -- rows of triangles
             → SvgNode M A

-- Voronoi-based menu (organic cell shapes)
voronoiMenu : ∀ {M A}
            → Float → Float       -- width, height
            → List (String × A)   -- items (positions auto-calculated)
            → SvgNode M A
```

#### Spiral & Orbital

```agda
-- Tabs along a spiral (expanding outward)
spiralTabs : ∀ {M A}
           → Float → Float        -- inner/outer radius
           → Float                -- number of turns
           → (M → ℕ) → (ℕ → A)
           → List String
           → SvgNode M A

-- Orbital menu (items orbit around center, can be animated)
orbitalMenu : ∀ {M A}
            → Float               -- radius
            → (M → Float)         -- rotation angle (for animation)
            → (M → ℕ)             -- selected
            → (ℕ → A)
            → List (IconName × String)
            → SvgNode M A

-- Concentric ring selector (multiple rings, click to select)
concentricSelector : ∀ {M A}
                   → List Float   -- ring radii
                   → (M → ℕ × ℕ)  -- (ring, segment)
                   → (ℕ → ℕ → A)
                   → List (List (String × Color))  -- items per ring
                   → SvgNode M A
```

#### Morphing & Animated

```agda
-- Button that morphs shape on hover/click
morphButton : ∀ {M A}
            → Path → Path         -- normal, hovered shapes
            → String              -- label
            → A
            → SvgNode M A

-- Accordion with smooth path morphing (not just height)
morphAccordion : ∀ {M A}
               → (M → ℕ)          -- open section (-1 = none)
               → (ℕ → A)
               → List (String × SvgNode M A)
               → SvgNode M A

-- Liquid/blob button (organic shape that wobbles)
blobButton : ∀ {M A}
           → Float               -- base size
           → String → A
           → SvgNode M A
```

#### 3D-ish Effects (2.5D)

```agda
-- Isometric button grid
isometricButtons : ∀ {M A}
                 → Float          -- cell size
                 → ℕ × ℕ          -- grid dimensions
                 → (ℕ → ℕ → M → String)  -- label at (x,y)
                 → (ℕ → ℕ → A)
                 → SvgNode M A

-- Carousel with perspective (items scale/fade at edges)
perspectiveCarousel : ∀ {M A}
                    → Float → Float
                    → (M → ℕ)     -- center item
                    → (ℕ → A)     -- select
                    → List (SvgNode M A)  -- items
                    → SvgNode M A

-- Flip card (front/back with 3D flip animation)
flipCard : ∀ {M A}
         → Float → Float
         → (M → Bool)             -- isFlipped
         → A                      -- flip message
         → SvgNode M A            -- front
         → SvgNode M A            -- back
         → SvgNode M A
```

#### Artistic / Decorative

```agda
-- Neon-glow button
neonButton : ∀ {M A}
           → String → Color       -- label, glow color
           → A
           → SvgNode M A

-- Hand-drawn style button (wobbly edges)
sketchyButton : ∀ {M A}
              → Float → Float
              → String → A
              → SvgNode M A

-- Stamp/seal button (circular with decorative border)
stampButton : ∀ {M A}
            → Float               -- radius
            → String → A
            → SvgNode M A

-- Ribbon/banner label
ribbonLabel : ∀ {M A}
            → Float               -- width
            → String
            → Color
            → SvgNode M A
```

These controls demonstrate SVG's power for creative UI — things that would require
complex CSS hacks or canvas drawing in HTML, but are natural in SVG.

## Icons & Decorative

### Icon Library
Common SVG icons.

```agda
data IconName : Set where
  Check Cross Plus Minus Arrow ChevronLeft ChevronRight
  Menu Close Search Settings User Home Mail Phone
  Edit Delete Save Download Upload Refresh
  Play Pause Stop Forward Backward
  Star Heart Bell Flag Warning Info
  -- ... many more

icon : ∀ {M A} → IconName → Float → Color → Node M A

-- Clickable icon
iconButton : ∀ {M A} → IconName → Float → Color → A → Node M A
```

### Badges & Labels
Status indicators.

```agda
badge : ∀ {M A} → String → Color → Node M A
statusDot : ∀ {M A} → Color → Node M A
```

## Module Structure

```
Agdelte/
  Svg/
    Controls.agda              -- re-exports all
    Controls/
      Charts/
        Line.agda
        Area.agda
        Bar.agda
        Pie.agda
        Scatter.agda
        Radar.agda
        Heatmap.agda
        Treemap.agda
        Sankey.agda
      Gauges/
        Gauge.agda
        Sparkline.agda
        KPI.agda
        ProgressRing.agda
      Diagrams/
        Network.agda
        Flowchart.agda
        Timeline.agda
        OrgChart.agda
      Geo/
        Map.agda
        WorldMap.agda
        USAMap.agda
      Icons/
        Icons.agda
        IconSet.agda           -- icon path data
      Common/
        Axis.agda              -- shared axis rendering
        Legend.agda            -- shared legend
        Tooltip.agda           -- SVG tooltip
        Scale.agda             -- linear, log, ordinal scales
        Color.agda             -- palettes, gradients
```

## Animation Strategy

Charts use two animation approaches:

1. **SMIL** (via `Agdelte.Svg.Smil`) — for continuous animations
   - Spinning spinners
   - Pulsing dots
   - Looping indicators

2. **Reactive transitions** (via model changes) — for data updates
   - Bar heights animate when data changes
   - Pie slices rotate/resize
   - Line paths morph (via `Agdelte.Svg.Path.Morph`)

```agda
-- Example: animated bar chart
animatedBarChart : ∀ {M A}
                 → Float → Float
                 → Duration                -- transition duration
                 → (M → List (BarData A))
                 → Node M A
```

## Implementation Priority

### Phase 1: Essential Charts
1. Line Chart
2. Bar Chart
3. Pie/Donut Chart
4. Sparkline

### Phase 2: More Charts
5. Area Chart
6. Scatter Plot
7. Gauge
8. Progress Ring

### Phase 3: Complex Visualizations
9. Heatmap
10. Radar Chart
11. Treemap
12. Network Graph

### Phase 4: Specialized
13. Sankey Diagram
14. Timeline
15. Geographic Maps
16. Org Chart / Flowchart

## Integration with HTML Controls

SVG controls return `Node M A`, same as HTML controls:

```agda
open import Agdelte.Html.Controls
open import Agdelte.Svg.Controls

dashboard : Node Model Msg
dashboard =
  div [ class "dashboard" ]
    ( -- HTML: Tab navigation
      tabBar activeTab SelectTab
        ( mkTab "Sales" (
            div [ class "charts" ]
              ( -- SVG: Line chart
                lineChart config salesSeries
              ∷ -- SVG: Pie chart
                pieChart 100.0 categoryData
              ∷ -- HTML: Data table below
                dataGrid tableConfig salesList
              ∷ [] ))
        ∷ mkTab "KPIs" (
            div [ class "kpis" ]
              ( -- SVG: Gauge
                gauge 80.0 gaugeConfig revenueValue
              ∷ -- SVG: Sparklines
                sparkline 100.0 30.0 blue weeklyTrend
              ∷ [] ))
        ∷ [] )
    ∷ [] )
```

## Open Questions

1. **Axis tick calculation** — smart tick placement algorithm?
   - Nice numbers (1, 2, 5, 10, 20, 50...)
   - Date/time axis formatting

2. **Tooltips** — HTML overlay vs SVG `<title>` vs custom?
   - HTML gives more flexibility
   - SVG is simpler

3. **Legends** — auto-generate from series or manual?

4. **Responsive** — ViewBox handles scaling, but what about:
   - Hiding labels when too small?
   - Different layouts at different sizes?

5. **Large datasets** — path simplification for 10k+ points?
   - Douglas-Peucker algorithm in Agda?
   - Or limit in API?

6. **Color palettes** — built-in palettes?
   - Categorical (distinct colors)
   - Sequential (light to dark)
   - Diverging (two-color gradient through neutral)
