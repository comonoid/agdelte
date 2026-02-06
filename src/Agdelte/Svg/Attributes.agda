{-# OPTIONS --without-K #-}

-- SVG Attribute Helpers
-- Typed constructors for SVG attributes

module Agdelte.Svg.Attributes where

open import Data.String using (String; _++_)
open import Data.Float using (Float)
open import Agdelte.Reactive.Node using (Attr; attr)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Css.Color using (Color; showColor)

------------------------------------------------------------------------
-- Geometry: positioning
------------------------------------------------------------------------

x_ y_ : ∀ {M Msg} → String → Attr M Msg
x_ = attr "x"
y_ = attr "y"

cx_ cy_ : ∀ {M Msg} → String → Attr M Msg
cx_ = attr "cx"
cy_ = attr "cy"

-- Float variants
xF yF : ∀ {M Msg} → Float → Attr M Msg
xF v = attr "x" (showFloat v)
yF v = attr "y" (showFloat v)

cxF cyF : ∀ {M Msg} → Float → Attr M Msg
cxF v = attr "cx" (showFloat v)
cyF v = attr "cy" (showFloat v)

------------------------------------------------------------------------
-- Geometry: dimensions
------------------------------------------------------------------------

width_ height_ : ∀ {M Msg} → String → Attr M Msg
width_ = attr "width"
height_ = attr "height"

widthF heightF : ∀ {M Msg} → Float → Attr M Msg
widthF v = attr "width" (showFloat v)
heightF v = attr "height" (showFloat v)

r_ : ∀ {M Msg} → String → Attr M Msg
r_ = attr "r"

rF : ∀ {M Msg} → Float → Attr M Msg
rF v = attr "r" (showFloat v)

rx_ ry_ : ∀ {M Msg} → String → Attr M Msg
rx_ = attr "rx"
ry_ = attr "ry"

rxF ryF : ∀ {M Msg} → Float → Attr M Msg
rxF v = attr "rx" (showFloat v)
ryF v = attr "ry" (showFloat v)

------------------------------------------------------------------------
-- Geometry: line endpoints
------------------------------------------------------------------------

x1_ y1_ x2_ y2_ : ∀ {M Msg} → String → Attr M Msg
x1_ = attr "x1"
y1_ = attr "y1"
x2_ = attr "x2"
y2_ = attr "y2"

x1F y1F x2F y2F : ∀ {M Msg} → Float → Attr M Msg
x1F v = attr "x1" (showFloat v)
y1F v = attr "y1" (showFloat v)
x2F v = attr "x2" (showFloat v)
y2F v = attr "y2" (showFloat v)

------------------------------------------------------------------------
-- Geometry: polygon/polyline
------------------------------------------------------------------------

points_ : ∀ {M Msg} → String → Attr M Msg
points_ = attr "points"

------------------------------------------------------------------------
-- Geometry: path
------------------------------------------------------------------------

d_ : ∀ {M Msg} → String → Attr M Msg
d_ = attr "d"

------------------------------------------------------------------------
-- Geometry: viewBox and preserveAspectRatio
------------------------------------------------------------------------

viewBox_ : ∀ {M Msg} → String → Attr M Msg
viewBox_ = attr "viewBox"

preserveAspectRatio_ : ∀ {M Msg} → String → Attr M Msg
preserveAspectRatio_ = attr "preserveAspectRatio"

------------------------------------------------------------------------
-- Presentation: fill and stroke
------------------------------------------------------------------------

fill_ stroke_ : ∀ {M Msg} → String → Attr M Msg
fill_ = attr "fill"
stroke_ = attr "stroke"

-- Typed Color variants
fillC strokeC : ∀ {M Msg} → Color → Attr M Msg
fillC c = attr "fill" (showColor c)
strokeC c = attr "stroke" (showColor c)

strokeWidth_ : ∀ {M Msg} → String → Attr M Msg
strokeWidth_ = attr "stroke-width"

strokeWidthF : ∀ {M Msg} → Float → Attr M Msg
strokeWidthF v = attr "stroke-width" (showFloat v)

fillOpacity_ strokeOpacity_ opacity_ : ∀ {M Msg} → String → Attr M Msg
fillOpacity_ = attr "fill-opacity"
strokeOpacity_ = attr "stroke-opacity"
opacity_ = attr "opacity"

fillOpacityF strokeOpacityF opacityF : ∀ {M Msg} → Float → Attr M Msg
fillOpacityF v = attr "fill-opacity" (showFloat v)
strokeOpacityF v = attr "stroke-opacity" (showFloat v)
opacityF v = attr "opacity" (showFloat v)

------------------------------------------------------------------------
-- Presentation: stroke dashing
------------------------------------------------------------------------

strokeDasharray_ strokeDashoffset_ : ∀ {M Msg} → String → Attr M Msg
strokeDasharray_ = attr "stroke-dasharray"
strokeDashoffset_ = attr "stroke-dashoffset"

strokeDasharrayF strokeDashoffsetF : ∀ {M Msg} → Float → Attr M Msg
strokeDasharrayF v = attr "stroke-dasharray" (showFloat v)
strokeDashoffsetF v = attr "stroke-dashoffset" (showFloat v)

------------------------------------------------------------------------
-- Presentation: stroke line caps and joins
------------------------------------------------------------------------

strokeLinecap_ strokeLinejoin_ : ∀ {M Msg} → String → Attr M Msg
strokeLinecap_ = attr "stroke-linecap"
strokeLinejoin_ = attr "stroke-linejoin"

fillRule_ : ∀ {M Msg} → String → Attr M Msg
fillRule_ = attr "fill-rule"

------------------------------------------------------------------------
-- Presentation: transform
------------------------------------------------------------------------

transform_ : ∀ {M Msg} → String → Attr M Msg
transform_ = attr "transform"

------------------------------------------------------------------------
-- References
------------------------------------------------------------------------

href_ : ∀ {M Msg} → String → Attr M Msg
href_ = attr "href"

xlinkHref_ : ∀ {M Msg} → String → Attr M Msg
xlinkHref_ = attr "xlink:href"

------------------------------------------------------------------------
-- Markers
------------------------------------------------------------------------

markerStart_ markerMid_ markerEnd_ : ∀ {M Msg} → String → Attr M Msg
markerStart_ = attr "marker-start"
markerMid_ = attr "marker-mid"
markerEnd_ = attr "marker-end"

------------------------------------------------------------------------
-- Filters and clipping
------------------------------------------------------------------------

filter_ : ∀ {M Msg} → String → Attr M Msg
filter_ = attr "filter"

clipPath_ : ∀ {M Msg} → String → Attr M Msg
clipPath_ = attr "clip-path"

mask_ : ∀ {M Msg} → String → Attr M Msg
mask_ = attr "mask"

------------------------------------------------------------------------
-- Gradient stops
------------------------------------------------------------------------

offset_ : ∀ {M Msg} → String → Attr M Msg
offset_ = attr "offset"

offsetF : ∀ {M Msg} → Float → Attr M Msg
offsetF v = attr "offset" (showFloat v)

stopColor_ stopOpacity_ : ∀ {M Msg} → String → Attr M Msg
stopColor_ = attr "stop-color"
stopOpacity_ = attr "stop-opacity"

stopColorC : ∀ {M Msg} → Color → Attr M Msg
stopColorC c = attr "stop-color" (showColor c)

stopOpacityF : ∀ {M Msg} → Float → Attr M Msg
stopOpacityF v = attr "stop-opacity" (showFloat v)

------------------------------------------------------------------------
-- Text attributes
------------------------------------------------------------------------

textAnchor_ : ∀ {M Msg} → String → Attr M Msg
textAnchor_ = attr "text-anchor"

dominantBaseline_ : ∀ {M Msg} → String → Attr M Msg
dominantBaseline_ = attr "dominant-baseline"

dx_ dy_ : ∀ {M Msg} → String → Attr M Msg
dx_ = attr "dx"
dy_ = attr "dy"

dxF dyF : ∀ {M Msg} → Float → Attr M Msg
dxF v = attr "dx" (showFloat v)
dyF v = attr "dy" (showFloat v)

textLength_ : ∀ {M Msg} → String → Attr M Msg
textLength_ = attr "textLength"

lengthAdjust_ : ∀ {M Msg} → String → Attr M Msg
lengthAdjust_ = attr "lengthAdjust"

fontSize_ : ∀ {M Msg} → String → Attr M Msg
fontSize_ = attr "font-size"

fontFamily_ : ∀ {M Msg} → String → Attr M Msg
fontFamily_ = attr "font-family"

fontWeight_ : ∀ {M Msg} → String → Attr M Msg
fontWeight_ = attr "font-weight"

------------------------------------------------------------------------
-- Marker element attributes
------------------------------------------------------------------------

refX_ refY_ : ∀ {M Msg} → String → Attr M Msg
refX_ = attr "refX"
refY_ = attr "refY"

markerWidth_ markerHeight_ : ∀ {M Msg} → String → Attr M Msg
markerWidth_ = attr "markerWidth"
markerHeight_ = attr "markerHeight"

markerUnits_ : ∀ {M Msg} → String → Attr M Msg
markerUnits_ = attr "markerUnits"

orient_ : ∀ {M Msg} → String → Attr M Msg
orient_ = attr "orient"

------------------------------------------------------------------------
-- Pattern attributes
------------------------------------------------------------------------

patternUnits_ patternContentUnits_ : ∀ {M Msg} → String → Attr M Msg
patternUnits_ = attr "patternUnits"
patternContentUnits_ = attr "patternContentUnits"

patternTransform_ : ∀ {M Msg} → String → Attr M Msg
patternTransform_ = attr "patternTransform"

------------------------------------------------------------------------
-- Gradient attributes
------------------------------------------------------------------------

gradientUnits_ : ∀ {M Msg} → String → Attr M Msg
gradientUnits_ = attr "gradientUnits"

gradientTransform_ : ∀ {M Msg} → String → Attr M Msg
gradientTransform_ = attr "gradientTransform"

spreadMethod_ : ∀ {M Msg} → String → Attr M Msg
spreadMethod_ = attr "spreadMethod"

------------------------------------------------------------------------
-- Filter primitive attributes
------------------------------------------------------------------------

result_ inAttr_ in2_ : ∀ {M Msg} → String → Attr M Msg
result_ = attr "result"
inAttr_ = attr "in"
in2_ = attr "in2"

stdDeviation_ : ∀ {M Msg} → String → Attr M Msg
stdDeviation_ = attr "stdDeviation"

mode_ : ∀ {M Msg} → String → Attr M Msg
mode_ = attr "mode"

type_ : ∀ {M Msg} → String → Attr M Msg
type_ = attr "type"

values_ : ∀ {M Msg} → String → Attr M Msg
values_ = attr "values"

------------------------------------------------------------------------
-- Accessibility (see also Agdelte.Svg.Accessibility for more)
------------------------------------------------------------------------

-- role_, ariaLabel_, ariaHidden_, focusable_ are in Accessibility module

------------------------------------------------------------------------
-- General (id and class are in Agdelte.Reactive.Node)
------------------------------------------------------------------------

svgId_ : ∀ {M Msg} → String → Attr M Msg
svgId_ = attr "id"
