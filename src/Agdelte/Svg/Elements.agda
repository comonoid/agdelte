{-# OPTIONS --without-K #-}

-- SVG Element Constructors
-- Smart constructors for SVG elements, mirroring HTML element helpers

module Agdelte.Svg.Elements where

open import Data.List using (List; [])
open import Agdelte.Reactive.Node using (Node; Attr; elem)

------------------------------------------------------------------------
-- Container elements (attrs + children)
------------------------------------------------------------------------

svg : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
svg = elem "svg"

g : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
g = elem "g"

defs : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
defs = elem "defs"

symbol' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
symbol' = elem "symbol"

marker' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
marker' = elem "marker"

clipPath' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
clipPath' = elem "clipPath"

mask' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
mask' = elem "mask"

pattern' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
pattern' = elem "pattern"

a' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
a' = elem "a"

switch' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
switch' = elem "switch"

------------------------------------------------------------------------
-- Shape elements (attrs + children for SMIL animations)
------------------------------------------------------------------------

circle' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
circle' = elem "circle"

rect' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
rect' = elem "rect"

ellipse' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
ellipse' = elem "ellipse"

line' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
line' = elem "line"

polyline' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
polyline' = elem "polyline"

polygon' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
polygon' = elem "polygon"

path' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
path' = elem "path"

------------------------------------------------------------------------
-- Text elements (attrs + children for tspan nesting)
------------------------------------------------------------------------

svgText : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
svgText = elem "text"

tspan' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
tspan' = elem "tspan"

textPath' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
textPath' = elem "textPath"

------------------------------------------------------------------------
-- Gradients (attrs + children for stops)
------------------------------------------------------------------------

linearGradient' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
linearGradient' = elem "linearGradient"

radialGradient' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
radialGradient' = elem "radialGradient"

stop' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
stop' = elem "stop"

------------------------------------------------------------------------
-- Filters (attrs + children for filter primitives)
------------------------------------------------------------------------

filter' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
filter' = elem "filter"

feGaussianBlur' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feGaussianBlur' = elem "feGaussianBlur"

feOffset' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feOffset' = elem "feOffset"

feBlend' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feBlend' = elem "feBlend"

feColorMatrix' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feColorMatrix' = elem "feColorMatrix"

feMerge' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feMerge' = elem "feMerge"

feMergeNode' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feMergeNode' = elem "feMergeNode"

feFlood' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feFlood' = elem "feFlood"

feComposite' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feComposite' = elem "feComposite"

feDropShadow' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feDropShadow' = elem "feDropShadow"

------------------------------------------------------------------------
-- Embedding (attrs + children)
------------------------------------------------------------------------

image' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
image' = elem "image"

use' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
use' = elem "use"

foreignObject' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
foreignObject' = elem "foreignObject"

------------------------------------------------------------------------
-- SMIL animation elements (for completeness, used as children)
------------------------------------------------------------------------

animate' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
animate' = elem "animate"

animateTransform' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
animateTransform' = elem "animateTransform"

animateMotion' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
animateMotion' = elem "animateMotion"

set' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
set' = elem "set"

mpath' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
mpath' = elem "mpath"

------------------------------------------------------------------------
-- Accessibility elements
------------------------------------------------------------------------

title' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
title' = elem "title"

desc' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
desc' = elem "desc"
