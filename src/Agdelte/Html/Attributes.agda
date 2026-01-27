{-# OPTIONS --without-K #-}

-- Html Attributes: атрибуты HTML элементов

module Agdelte.Html.Attributes where

open import Data.String using (String; _++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false)

open import Agdelte.Html.Types

private
  variable
    Msg : Set

------------------------------------------------------------------------
-- Global attributes
------------------------------------------------------------------------

id : String → Attr Msg
id = attr "id"

class : String → Attr Msg
class = attr "class"

title : String → Attr Msg
title = attr "title"

lang : String → Attr Msg
lang = attr "lang"

dir : String → Attr Msg
dir = attr "dir"

tabindex : ℕ → Attr Msg
tabindex n = attr "tabindex" (show n)

hidden : Attr Msg
hidden = boolAttr "hidden"

draggable : Bool → Attr Msg
draggable true  = attr "draggable" "true"
draggable false = attr "draggable" "false"

contenteditable : Bool → Attr Msg
contenteditable true  = attr "contenteditable" "true"
contenteditable false = attr "contenteditable" "false"

------------------------------------------------------------------------
-- Links and navigation
------------------------------------------------------------------------

href : String → Attr Msg
href = attr "href"

target : String → Attr Msg
target = attr "target"

rel : String → Attr Msg
rel = attr "rel"

download : String → Attr Msg
download = attr "download"

------------------------------------------------------------------------
-- Form attributes
------------------------------------------------------------------------

name : String → Attr Msg
name = attr "name"

value : String → Attr Msg
value = attr "value"

placeholder : String → Attr Msg
placeholder = attr "placeholder"

type' : String → Attr Msg
type' = attr "type"

disabled : Attr Msg
disabled = boolAttr "disabled"

readonly : Attr Msg
readonly = boolAttr "readonly"

required : Attr Msg
required = boolAttr "required"

checked : Attr Msg
checked = boolAttr "checked"

selected : Attr Msg
selected = boolAttr "selected"

autofocus : Attr Msg
autofocus = boolAttr "autofocus"

autocomplete : String → Attr Msg
autocomplete = attr "autocomplete"

multiple : Attr Msg
multiple = boolAttr "multiple"

maxlength : ℕ → Attr Msg
maxlength n = attr "maxlength" (show n)

minlength : ℕ → Attr Msg
minlength n = attr "minlength" (show n)

pattern' : String → Attr Msg
pattern' = attr "pattern"

min : String → Attr Msg
min = attr "min"

max : String → Attr Msg
max = attr "max"

step : String → Attr Msg
step = attr "step"

for : String → Attr Msg
for = attr "for"

form' : String → Attr Msg
form' = attr "form"

action : String → Attr Msg
action = attr "action"

method : String → Attr Msg
method = attr "method"

enctype : String → Attr Msg
enctype = attr "enctype"

novalidate : Attr Msg
novalidate = boolAttr "novalidate"

------------------------------------------------------------------------
-- Media attributes
------------------------------------------------------------------------

src : String → Attr Msg
src = attr "src"

alt : String → Attr Msg
alt = attr "alt"

width : String → Attr Msg
width = attr "width"

height : String → Attr Msg
height = attr "height"

autoplay : Attr Msg
autoplay = boolAttr "autoplay"

controls : Attr Msg
controls = boolAttr "controls"

loop : Attr Msg
loop = boolAttr "loop"

muted : Attr Msg
muted = boolAttr "muted"

poster : String → Attr Msg
poster = attr "poster"

preload : String → Attr Msg
preload = attr "preload"

------------------------------------------------------------------------
-- Table attributes
------------------------------------------------------------------------

colspan : ℕ → Attr Msg
colspan n = attr "colspan" (show n)

rowspan : ℕ → Attr Msg
rowspan n = attr "rowspan" (show n)

scope : String → Attr Msg
scope = attr "scope"

------------------------------------------------------------------------
-- ARIA attributes
------------------------------------------------------------------------

role : String → Attr Msg
role = attr "role"

ariaLabel : String → Attr Msg
ariaLabel = attr "aria-label"

ariaHidden : Bool → Attr Msg
ariaHidden true  = attr "aria-hidden" "true"
ariaHidden false = attr "aria-hidden" "false"

ariaExpanded : Bool → Attr Msg
ariaExpanded true  = attr "aria-expanded" "true"
ariaExpanded false = attr "aria-expanded" "false"

ariaDisabled : Bool → Attr Msg
ariaDisabled true  = attr "aria-disabled" "true"
ariaDisabled false = attr "aria-disabled" "false"

ariaDescribedby : String → Attr Msg
ariaDescribedby = attr "aria-describedby"

ariaLabelledby : String → Attr Msg
ariaLabelledby = attr "aria-labelledby"

------------------------------------------------------------------------
-- Data attributes
------------------------------------------------------------------------

data' : String → String → Attr Msg
data' name' val = attr ("data-" ++ name') val

------------------------------------------------------------------------
-- Styles
------------------------------------------------------------------------

-- Инлайн стили
styles : String → String → Attr Msg
styles = style

-- Удобные хелперы для частых стилей
backgroundColor : String → Attr Msg
backgroundColor = style "background-color"

color : String → Attr Msg
color = style "color"

fontSize : String → Attr Msg
fontSize = style "font-size"

fontWeight : String → Attr Msg
fontWeight = style "font-weight"

margin : String → Attr Msg
margin = style "margin"

padding : String → Attr Msg
padding = style "padding"

border : String → Attr Msg
border = style "border"

display : String → Attr Msg
display = style "display"

position : String → Attr Msg
position = style "position"

flexDirection : String → Attr Msg
flexDirection = style "flex-direction"

justifyContent : String → Attr Msg
justifyContent = style "justify-content"

alignItems : String → Attr Msg
alignItems = style "align-items"

gap : String → Attr Msg
gap = style "gap"

cursor : String → Attr Msg
cursor = style "cursor"

opacity : String → Attr Msg
opacity = style "opacity"

transform : String → Attr Msg
transform = style "transform"

transition : String → Attr Msg
transition = style "transition"

------------------------------------------------------------------------
-- Key for diffing
------------------------------------------------------------------------

keyAttr : String → Attr Msg
keyAttr = key
