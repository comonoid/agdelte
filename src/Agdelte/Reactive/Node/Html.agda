{-# OPTIONS --without-K #-}

-- Smart constructors for HTML elements, event handlers, and attributes.
-- Re-exported by Agdelte.Reactive.Node for backward compatibility.

module Agdelte.Reactive.Node.Html where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)

open import Agdelte.Reactive.Node.Core using
  ( Node; Attr; Binding
  ; elem; bind; attr; attrBind; on; onValue; onValueScreen; onKeyFiltered
  ; style; styleBind
  ; stringBinding; boolBinding
  )

------------------------------------------------------------------------
-- Binding helper
------------------------------------------------------------------------

bindF : ∀ {Model Msg} → (Model → String) → Node Model Msg
bindF f = bind (stringBinding f)

------------------------------------------------------------------------
-- Common HTML elements
------------------------------------------------------------------------

div : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
div = elem "div"

span : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
span = elem "span"

button : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
button = elem "button"

p : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
p = elem "p"

h1 : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
h1 = elem "h1"

h2 : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
h2 = elem "h2"

h3 : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
h3 = elem "h3"

input : ∀ {Model Msg} → List (Attr Model Msg) → Node Model Msg
input attrs = elem "input" attrs []

ul : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
ul = elem "ul"

li : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
li = elem "li"

label : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
label = elem "label"

nav : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
nav = elem "nav"

a : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
a = elem "a"

pre : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
pre = elem "pre"

------------------------------------------------------------------------
-- Event handler helpers
------------------------------------------------------------------------

onClick : ∀ {Model Msg} → Msg → Attr Model Msg
onClick = on "click"

onDoubleClick : ∀ {Model Msg} → Msg → Attr Model Msg
onDoubleClick = on "dblclick"

onInput : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onInput = onValue "input"

onKeyDown : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onKeyDown = onValue "keydown"

onKeyUp : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onKeyUp = onValue "keyup"

onKeyDownFiltered : ∀ {Model Msg} → List String → (String → Msg) → Attr Model Msg
onKeyDownFiltered = onKeyFiltered

onChange : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onChange = onValue "change"

onSubmit : ∀ {Model Msg} → Msg → Attr Model Msg
onSubmit = on "submit"

onFocus : ∀ {Model Msg} → Msg → Attr Model Msg
onFocus = on "focus"

onBlur : ∀ {Model Msg} → Msg → Attr Model Msg
onBlur = on "blur"

onMouseEnter : ∀ {Model Msg} → Msg → Attr Model Msg
onMouseEnter = on "mouseenter"

onMouseLeave : ∀ {Model Msg} → Msg → Attr Model Msg
onMouseLeave = on "mouseleave"

onMouseMove : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onMouseMove = onValue "mousemove"

onMouseDown : ∀ {Model Msg} → Msg → Attr Model Msg
onMouseDown = on "mousedown"

onMouseUp : ∀ {Model Msg} → Msg → Attr Model Msg
onMouseUp = on "mouseup"

onTouchStart : ∀ {Model Msg} → Msg → Attr Model Msg
onTouchStart = on "touchstart"

onTouchEnd : ∀ {Model Msg} → Msg → Attr Model Msg
onTouchEnd = on "touchend"

------------------------------------------------------------------------
-- Attribute helpers
------------------------------------------------------------------------

class : ∀ {Model Msg} → String → Attr Model Msg
class = attr "class"

classBind : ∀ {Model Msg} → (Model → String) → Attr Model Msg
classBind f = attrBind "class" (stringBinding f)

id' : ∀ {Model Msg} → String → Attr Model Msg
id' = attr "id"

value : ∀ {Model Msg} → String → Attr Model Msg
value = attr "value"

valueBind : ∀ {Model Msg} → (Model → String) → Attr Model Msg
valueBind f = attrBind "value" (stringBinding f)

placeholder : ∀ {Model Msg} → String → Attr Model Msg
placeholder = attr "placeholder"

type' : ∀ {Model Msg} → String → Attr Model Msg
type' = attr "type"

href : ∀ {Model Msg} → String → Attr Model Msg
href = attr "href"

disabled : ∀ {Model Msg} → Attr Model Msg
disabled = attr "disabled" "true"

disabledBind : ∀ {Model Msg} → (Model → Bool) → Attr Model Msg
disabledBind f = attrBind "disabled" (boolBinding f)

checked : ∀ {Model Msg} → Attr Model Msg
checked = attr "checked" "true"

checkedBind : ∀ {Model Msg} → (Model → Bool) → Attr Model Msg
checkedBind f = attrBind "checked" (boolBinding f)

keyAttr : ∀ {Model Msg} → String → Attr Model Msg
keyAttr = attr "data-key"

styles : ∀ {Model Msg} → String → String → Attr Model Msg
styles = style

-- Two-way binding: valueBind + onInput in one step
vmodel : ∀ {Model Msg} → (Model → String) → (String → Msg) → List (Attr Model Msg)
vmodel get msg = valueBind get ∷ onInput msg ∷ []
