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

-- String equality as Bool (used by all string bindings)
private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

-- String binding with string equality
stringBinding : ∀ {Model} → (Model → String) → Binding Model String
stringBinding f = mkBinding f eqStr

-- Bool-to-String binding (for disabled, checked, etc.)
boolBinding : ∀ {Model} → (Model → Bool) → Binding Model String
boolBinding f = mkBinding (λ m → if f m then "true" else "") eqStr

------------------------------------------------------------------------
-- Transition: enter/leave animations for when
------------------------------------------------------------------------

record Transition : Set where
  constructor mkTransition
  field
    enterClass : String    -- CSS class added on enter
    leaveClass : String    -- CSS class added on leave
    duration   : ℕ         -- ms to wait before removing DOM on leave

open Transition public

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

  -- Keyed dynamic list: key-based reconciliation (add/remove/reorder)
  -- Items with same key reuse DOM nodes; new keys get fresh renders
  foreachKeyed : ∀ {A : Set} → (Model → List A) → (A → String) → (A → ℕ → Node Model Msg) → Node Model Msg

  -- Conditional rendering with enter/leave CSS transitions
  whenT : (Model → Bool) → Transition → Node Model Msg → Node Model Msg

  -- Scope cutoff (manual): string fingerprint for subtree skipping.
  -- If fingerprint(oldModel) ≡ fingerprint(newModel), skip updating this subtree.
  scope : (Model → String) → Node Model Msg → Node Model Msg

  -- Scope cutoff (automatic): projection function for subtree skipping.
  -- Runtime uses deep structural equality on Scott-encoded values via Proxy.
  -- Used automatically by zoomNode — no manual fingerprint needed.
  scopeProj : ∀ {M' : Set} → (Model → M') → Node Model Msg → Node Model Msg

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
-- Usage: input (vmodel getText SetText) []
vmodel : ∀ {Model Msg} → (Model → String) → (String → Msg) → List (Attr Model Msg)
vmodel get msg = valueBind get ∷ onInput msg ∷ []

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
-- Internal: transform binding to work with larger model
------------------------------------------------------------------------

focusBinding : ∀ {Model Model' A} → (Model → Model') → Binding Model' A → Binding Model A
focusBinding get b = mkBinding (extract b ∘ get) (equals b)

------------------------------------------------------------------------
-- Zoom: transform both Model AND Msg (full lens composition)
------------------------------------------------------------------------

-- Transform attribute: remap model and messages
zoomAttr : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Attr M' Msg' → Attr M Msg
zoomAttr get wrap (attr name val) = attr name val
zoomAttr get wrap (attrBind name b) = attrBind name (focusBinding get b)
zoomAttr get wrap (on event msg) = on event (wrap msg)
zoomAttr get wrap (onValue event handler) = onValue event (wrap ∘ handler)
zoomAttr get wrap (style name val) = style name val
zoomAttr get wrap (styleBind name b) = styleBind name (focusBinding get b)

-- Internal: remap node without adding scope wrapper (used by zoomNode)
{-# TERMINATING #-}
zoomNode' : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNode' get wrap (text s) = text s
zoomNode' get wrap (bind b) = bind (focusBinding get b)
zoomNode' get wrap (elem tag attrs children) =
  elem tag (map (zoomAttr get wrap) attrs) (map (zoomNode' get wrap) children)
zoomNode' get wrap empty = empty
zoomNode' get wrap (when cond node) = when (cond ∘ get) (zoomNode' get wrap node)
zoomNode' get wrap (foreach {A} getList render) =
  foreach (getList ∘ get) (λ a i → zoomNode' get wrap (render a i))
zoomNode' get wrap (foreachKeyed {A} getList keyFn render) =
  foreachKeyed (getList ∘ get) keyFn (λ a i → zoomNode' get wrap (render a i))
zoomNode' get wrap (whenT cond trans node) =
  whenT (cond ∘ get) trans (zoomNode' get wrap node)
zoomNode' get wrap (scope fp node) =
  scope (fp ∘ get) (zoomNode' get wrap node)
zoomNode' get wrap (scopeProj proj node) =
  scopeProj (proj ∘ get) (zoomNode' get wrap node)

-- Transform node: remap model/message AND wrap in automatic scopeProj cutoff.
-- Every zoomNode call gets free subtree-skipping via deepEqual.
zoomNode : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNode get wrap node = scopeProj get (zoomNode' get wrap node)

------------------------------------------------------------------------
-- Zoom with Lens + Prism (Phase 6: typed component composition)
------------------------------------------------------------------------

open import Agdelte.Reactive.Optic using (Prism; Lens; get; build)

-- zoomNode with explicit Lens (model) + Prism (messages)
-- Same as zoomNode but with structured optic types
zoomNodeL : ∀ {M M' Msg Msg'} → Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomNodeL l p = zoomNode (get l) (build p)

-- zoomNode with explicit string fingerprint (overrides automatic scopeProj)
zoomNodeS : ∀ {M M' Msg Msg'} → (M → M') → (M' → String) → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNodeS get' fp wrap node = scope (fp ∘ get') (zoomNode' get' wrap node)

-- zoomNodeLS: Lens + Prism + fingerprint
zoomNodeLS : ∀ {M M' Msg Msg'} → Lens M M' → (M' → String) → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomNodeLS l fp p = zoomNodeS (get l) fp (build p)

-- zoomAttr with Lens + Prism
zoomAttrL : ∀ {M M' Msg Msg'} → Lens M M' → Prism Msg Msg' → Attr M' Msg' → Attr M Msg
zoomAttrL l p = zoomAttr (get l) (build p)

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
