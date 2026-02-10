# Agdelte.Svg.Controls

Pure Agda library for SVG-based data visualization and UI components.
All components return `Node M A` and compose with HTML and other SVG elements.

## Design Principles

1. **Declarative** — describe data, not drawing commands
2. **Reactive** — automatic updates when model changes
3. **Composable** — combine charts, add annotations, embed in HTML
4. **Responsive** — ViewBox-based scaling

## Quick Start

```agda
open import Agdelte.Svg.Controls

-- Use charts and controls
view = svg [ viewBox "0 0 400 300" ]
         ( lineChart 400.0 300.0 "#3b82f6" True getData
         ∷ [] )
```

## Charts

### Line Chart

Time series, trends, continuous data.

```agda
record DataPoint : Set where
  constructor mkDataPoint
  field x : Float ; y : Float

record LineConfig : Set where
  field
    width height : Float
    color        : String
    strokeWidth  : Float
    showDots     : Bool
    showGrid     : Bool
    showAxes     : Bool

lineChart : Float → Float → String → Bool → (M → List DataPoint) → Node M A
-- width, height, color, showDots, getData

lineChartConfig : LineConfig → (M → List DataPoint) → Node M A

multiLineChart : Float → Float → Bool → List (String × String) → (M → List (List DataPoint)) → Node M A
-- width, height, showDots, (name, color) pairs, getData per series
```

### Area Chart

Filled area under line.

```agda
areaChart : Float → Float → String → Float → (M → List DataPoint) → Node M A
-- width, height, color, opacity, getData

stackedArea : Float → Float → List (String × String) → (M → List (List DataPoint)) → Node M A
```

### Bar Chart

Categorical comparisons.

```agda
record BarData (A : Set) : Set where
  constructor mkBarData
  field
    label   : String
    value   : Float
    color   : Maybe String
    onClick : Maybe A

barChart : Float → Float → Bool → (M → List (BarData A)) → Node M A
-- width, height, horizontal?, getData

groupedBars : Float → Float → List (String × String) → List String → (M → List (List Float)) → Node M A
stackedBars : Float → Float → List (String × String) → List String → (M → List (List Float)) → Node M A
```

### Pie / Donut Chart

Part-to-whole relationships.

```agda
record PieSlice (A : Set) : Set where
  constructor mkPieSlice
  field
    label   : String
    value   : Float
    color   : String
    onClick : Maybe A

pieChart : Float → Float → Float → (M → List (PieSlice A)) → Node M A
-- cx, cy, radius, getData

donutChart : Float → Float → Float → Float → (M → List (PieSlice A)) → Node M A
-- cx, cy, outerRadius, innerRadius, getData
```

### Scatter Plot

Correlation, distribution.

```agda
record ScatterPoint (A : Set) : Set where
  constructor mkScatterPoint
  field
    x y     : Float
    size    : Maybe Float
    color   : Maybe String
    label   : Maybe String
    onClick : Maybe A

scatterPlot : Float → Float → (M → List (ScatterPoint A)) → Node M A
bubbleChart : Float → Float → (M → List (ScatterPoint A)) → Node M A
```

### Radar / Spider Chart

Multi-dimensional comparison.

```agda
record RadarAxis : Set where
  field name : String ; max : Float

record RadarSeries : Set where
  field name : String ; color : String ; values : List Float

radarChart : Float → Float → Float → List RadarAxis → (M → List RadarSeries) → Node M A
```

### Heatmap

2D density/intensity.

```agda
heatmap : Float → Float → List String → List String → (Float → String) → (M → List (List Float)) → Maybe (ℕ → ℕ → A) → Node M A
-- width, height, xLabels, yLabels, valueToColor, getData, onClick
```

### Timeline

Events along time axis.

```agda
record TimelineEvent (A : Set) : Set where
  field
    time label : String
    color      : String
    onClick    : Maybe A

timeline : Float → Float → Bool → (M → List (TimelineEvent A)) → Node M A
-- width, height, horizontal?, getData
```

### Network Graph

Nodes and edges.

```agda
record GraphNode (A : Set) : Set where
  field id label : String ; x y : Float ; color : String ; size : Float ; onClick : Maybe A

record GraphEdge : Set where
  field source target : String ; label : Maybe String ; directed : Bool

networkGraph : Float → Float → (M → List (GraphNode A)) → (M → List GraphEdge) → Node M A
```

### Treemap

Hierarchical rectangles.

```agda
record TreemapNode (A : Set) : Set where
  inductive
  field
    label value : Float
    color       : Maybe String
    children    : List (TreemapNode A)
    onClick     : Maybe A

treemap : Float → Float → (M → TreemapNode A) → Node M A
```

### Flowchart

Process flow.

```agda
data FlowShape : Set where
  Rectangle Rounded Diamond Oval Parallelogram : FlowShape

record FlowNode (A : Set) : Set where
  field id label : String ; shape : FlowShape ; x y : Float ; onClick : Maybe A

record FlowEdge : Set where
  field source target : String ; label : Maybe String

flowchart : Float → Float → (M → List (FlowNode A)) → (M → List FlowEdge) → Node M A
```

### Org Chart

Hierarchical tree structure.

```agda
record OrgNode (A : Set) : Set where
  inductive
  field
    id label sublabel : String
    children          : List (OrgNode A)
    onClick           : Maybe A

orgChart : Float → Float → (M → OrgNode A) → Node M A
```

### Sankey Diagram

Flow between nodes.

```agda
record SankeyNode : Set where
  field snId snLabel : String ; snColor : Maybe String

record SankeyLink : Set where
  field slSource slTarget : String ; slValue : Float ; slColor : Maybe String

sankeyDiagram : Float → Float → Float → Float → Float → List SankeyNode → List SankeyLink → Node M A
simpleSankey : Float → Float → Float → Float → List (String × String × Float) → Node M A
```

## Gauges & Indicators

### Gauge

Speedometer-style.

```agda
record GaugeConfig : Set where
  field
    min max        : Float
    label          : Maybe String
    showValue      : Bool
    colorZones     : List (Float × Float × String)  -- start, end, color

gauge : Float → Float → GaugeConfig → (M → Float) → Node M A
semicircleGauge : Float → Float → Float → Float → String → (M → Float) → Node M A
linearGauge : Float → Float → Float → Float → String → (M → Float) → Node M A
```

### Sparkline

Tiny inline chart.

```agda
sparkline : Float → Float → Float → Float → String → List Float → Node M A
sparklineArea : Float → Float → Float → Float → String → Float → List Float → Node M A
sparklineBar : Float → Float → Float → Float → String → Float → List Float → Node M A
sparklineWinLoss : Float → Float → Float → Float → String → String → List Float → Node M A
```

### Progress Ring

Circular progress.

```agda
progressRing : Float → Float → Float → Float → String → Float → Node M A
-- cx, cy, radius, strokeWidth, color, progress (0-1)

progressRingLabeled : Float → Float → Float → Float → String → Float → String → Node M A
multiProgressRing : Float → Float → Float → Float → List (Float × String) → Node M A
concentricRings : Float → Float → Float → Float → Float → List (Float × String) → Node M A
```

## Form Controls (SVG-based)

### Button

```agda
svgButton : Float → Float → Float → Float → String → A → Node M A
-- x, y, width, height, label, clickMsg
```

### Slider

```agda
svgSlider : Float → Float → Float → Float → Float → Float → (M → Float) → (Float → A) → Node M A
-- x, y, width, min, max, step, getValue, onChange

svgRangeSlider : Float → Float → Float → Float → Float → (M → Float × Float) → (Float → Float → A) → Node M A
```

### Toggle

```agda
svgToggle : Float → Float → Float → (M → Bool) → A → Node M A
```

### Checkbox

```agda
svgCheckbox : Float → Float → Float → (M → Bool) → A → Node M A
```

### RadioGroup

```agda
svgRadioGroup : Float → Float → List String → (M → ℕ) → (ℕ → A) → Node M A
```

### Knob (Rotary Dial)

```agda
knob : Float → Float → Float → Float → Float → (M → Float) → (Float → A) → Node M A
-- cx, cy, radius, min, max, getValue, onChange
```

## Chart Components

### Legend

```agda
legend : Float → Float → Bool → List (String × String) → Node M A
-- x, y, horizontal?, items (label, color)

interactiveLegend : Float → Float → Bool → List (String × String) → (M → List Bool) → (ℕ → A) → Node M A
```

### Axis

```agda
xAxis : Float → Float → Float → Float → Float → Maybe String → Node M A
-- x, y, width, min, max, label

yAxis : Float → Float → Float → Float → Float → Maybe String → Node M A
```

### Tooltip

```agda
svgTooltip : Float → Float → String → Node M A
tooltipPositioned : (M → Maybe (Float × Float × String)) → Node M A
```

## Layout & Interaction

### Connector

Lines between elements for diagrams.

```agda
data ConnectorStyle : Set where
  Straight Curved Elbow Arrow ArrowBoth : ConnectorStyle

connector : Float → Float → Float → Float → ConnectorStyle → String → Node M A
```

### Draggable

Drag handles for interactive diagrams.

```agda
dragHandle : Float → Float → Float → (Float → Float → A) → Node M A
selectionBox : Float → Float → Float → Float → Node M A
```

## Icons

Common SVG icons for UI.

```agda
data IconName : Set where
  Check Cross Plus Minus Arrow ChevronLeft ChevronRight
  Menu Close Search Settings User Home ...

svgIcon : IconName → Float → Float → Float → String → Node M A
-- icon, x, y, size, color
```

## Module Structure

```
Agdelte/Svg/Controls.agda            -- re-exports all
Agdelte/Svg/Controls/
  Button.agda
  Slider.agda
  RangeSlider.agda
  Checkbox.agda
  Toggle.agda
  RadioGroup.agda
  Knob.agda
  Progress.agda
  Gauge.agda
  Sparkline.agda
  Legend.agda
  Axis.agda
  Tooltip.agda
  Connector.agda
  Draggable.agda
  Icons.agda
  Charts.agda                        -- re-exports all charts
  Charts/
    Line.agda
    Area.agda
    Bar.agda
    Pie.agda
    Scatter.agda
    Radar.agda
    Heatmap.agda
    Timeline.agda
    Network.agda
    Treemap.agda
    Flowchart.agda
    OrgChart.agda
    Sankey.agda
  Gauges.agda                        -- re-exports gauges
  Gauges/
    Gauge.agda
    Sparkline.agda
    ProgressRing.agda
```

## Integration with HTML

SVG controls return `Node M A`, composable with HTML:

```agda
open import Agdelte.Html.Controls
open import Agdelte.Svg.Controls

dashboard : Node Model Msg
dashboard =
  div [ class "dashboard" ]
    ( tabBar activeTab SelectTab
        ( mkTab "Charts" (
            div [ class "charts" ]
              ( svg [ viewBox "0 0 400 200" ]
                  ( lineChart 400.0 200.0 "#3b82f6" True getSeries
                  ∷ [] )
              ∷ [] ))
        ∷ mkTab "Metrics" (
            div [ class "kpis" ]
              ( svg [ viewBox "0 0 200 200" ]
                  ( gauge 100.0 100.0 gaugeConfig getValue
                  ∷ [] )
              ∷ [] ))
        ∷ [] )
    ∷ [] )
```

## CSS for SVG Controls

SVG controls use class names for styling:

```css
.svg-button { cursor: pointer; }
.svg-button:hover rect { fill: #dbeafe; }

.svg-slider-track { stroke: #e5e7eb; }
.svg-slider-fill { stroke: #3b82f6; }
.svg-slider-thumb { fill: white; stroke: #3b82f6; }
```
