{-# OPTIONS --without-K #-}

-- Reactive Node: Template with automatic bindings
-- No Virtual DOM - bindings track which parts of DOM need updating
--
-- Key insight: Instead of view : Model → Html (function that rebuilds tree),
-- we have template : Node Model Msg (data structure with bindings)

module Agdelte.Reactive.Node where

open import Data.String using (String; _++_; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Binding: a reactive connection from Model to DOM
------------------------------------------------------------------------

-- A Binding captures how to extract a value from the model
-- and how to detect changes
record Binding (Model : Set) (A : Set) : Set where
  constructor mkBinding
  field
    extract : Model → A           -- get value from model
    equals  : A → A → Bool        -- check if value changed

open Binding public

-- String binding with string equality
stringBinding : ∀ {Model} → (Model → String) → Binding Model String
stringBinding f = mkBinding f eqString
  where
    eqString : String → String → Bool
    eqString a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

------------------------------------------------------------------------
-- Node: Reactive template structure
------------------------------------------------------------------------

-- Attribute types
data Attr (Model Msg : Set) : Set₁ where
  -- Static attribute
  attr : String → String → Attr Model Msg
  -- Dynamic attribute (bound to model)
  attrBind : String → Binding Model String → Attr Model Msg
  -- Event handler
  on : String → Msg → Attr Model Msg
  -- Event with value (e.g., onInput)
  onValue : String → (String → Msg) → Attr Model Msg
  -- Style
  style : String → String → Attr Model Msg
  -- Dynamic style
  styleBind : String → Binding Model String → Attr Model Msg

-- Node: the reactive template
data Node (Model Msg : Set) : Set₁ where
  -- Static text (never changes)
  text : String → Node Model Msg

  -- Dynamic text bound to model - THIS IS THE KEY!
  -- When model changes, runtime checks if binding changed and updates DOM
  bind : Binding Model String → Node Model Msg

  -- Element with attributes and children
  elem : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg

  -- Empty node (renders nothing)
  empty : Node Model Msg

  -- Conditional rendering: when condition is true, render the node
  when : (Model → Bool) → Node Model Msg → Node Model Msg

  -- Dynamic list of children (for Todo-like lists)
  -- Runtime rebuilds this section when list changes
  foreach : ∀ {A : Set} → (Model → List A) → (A → ℕ → Node Model Msg) → Node Model Msg

------------------------------------------------------------------------
-- Smart constructors for common patterns
------------------------------------------------------------------------

-- Bind with a function (most common case)
bindF : ∀ {Model Msg} → (Model → String) → Node Model Msg
bindF f = bind (stringBinding f)

-- Common elements
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

input : ∀ {Model Msg} → List (Attr Model Msg) → Node Model Msg
input attrs = elem "input" attrs []

-- More elements
ul : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
ul = elem "ul"

li : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
li = elem "li"

h2 : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
h2 = elem "h2"

h3 : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
h3 = elem "h3"

label : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
label = elem "label"

nav : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
nav = elem "nav"

a : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
a = elem "a"

pre : ∀ {Model Msg} → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
pre = elem "pre"

-- Event helpers
onClick : ∀ {Model Msg} → Msg → Attr Model Msg
onClick = on "click"

onInput : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onInput = onValue "input"

onKeyDown : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onKeyDown = onValue "keydown"

onChange : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onChange = onValue "change"

-- Attribute helpers
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
disabledBind f = attrBind "disabled" (mkBinding (λ m → if f m then "true" else "") eqStr)
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

checked : ∀ {Model Msg} → Attr Model Msg
checked = attr "checked" "true"

checkedBind : ∀ {Model Msg} → (Model → Bool) → Attr Model Msg
checkedBind f = attrBind "checked" (mkBinding (λ m → if f m then "true" else "") eqStr)
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

keyAttr : ∀ {Model Msg} → String → Attr Model Msg
keyAttr = attr "data-key"

styles : ∀ {Model Msg} → String → String → Attr Model Msg
styles = style

------------------------------------------------------------------------
-- ReactiveApp: Application with reactive template
------------------------------------------------------------------------

-- Simple app without subscriptions
record ReactiveApp (Model Msg : Set) : Set₁ where
  constructor mkReactiveApp
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg        -- NOT a function! Structure with bindings

open ReactiveApp public

-- For apps with subscriptions (Timer, WebSocket, etc.):
-- Use ReactiveApp + separate subs function in your module, e.g.:
--   app : ReactiveApp Model Msg
--   subs : Model → Event Msg

------------------------------------------------------------------------
-- Focus: zoom into part of model (like lens)
------------------------------------------------------------------------

-- Transform binding to work with larger model
focusBinding : ∀ {Model Model' A} → (Model → Model') → Binding Model' A → Binding Model A
focusBinding get b = mkBinding (extract b ∘ get) (equals b)

-- Transform node to work with larger model
{-# TERMINATING #-}  -- mutual recursion with lists
focusNode : ∀ {Model Model' Msg} → (Model → Model') → Node Model' Msg → Node Model Msg
focusNode get (text s) = text s
focusNode get (bind b) = bind (focusBinding get b)
focusNode get (elem tag attrs children) =
  elem tag (map (focusAttr get) attrs) (map (focusNode get) children)
  where
    focusAttr : ∀ {Model Model' Msg} → (Model → Model') → Attr Model' Msg → Attr Model Msg
    focusAttr get (attr name val) = attr name val
    focusAttr get (attrBind name b) = attrBind name (focusBinding get b)
    focusAttr get (on event msg) = on event msg
    focusAttr get (onValue event handler) = onValue event handler
    focusAttr get (style name val) = style name val
    focusAttr get (styleBind name b) = styleBind name (focusBinding get b)
focusNode get empty = empty
focusNode get (when cond node) = when (cond ∘ get) (focusNode get node)
focusNode get (foreach {A} getList render) =
  foreach (getList ∘ get) (λ a i → focusNode get (render a i))

------------------------------------------------------------------------
-- How the runtime works (conceptually):
--
-- 1. FIRST RENDER:
--    - Walk the Node tree, create real DOM
--    - For each `bind`, remember (DOMNode, Binding)
--    - For each `attrBind`/`styleBind`, remember (DOMNode, attrName, Binding)
--
-- 2. ON MODEL CHANGE:
--    - For each remembered binding:
--      - Compute old = extract(oldModel), new = extract(newModel)
--      - If equals(old, new) = false, update the DOM node
--    - NO tree diffing! Direct updates to tracked nodes.
--
-- This is exactly what Svelte does at compile time,
-- but we do it at runtime with the binding structure.
------------------------------------------------------------------------
