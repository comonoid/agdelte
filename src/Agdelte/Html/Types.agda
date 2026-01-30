{-# OPTIONS --without-K #-}

-- Html Types: base types for virtual DOM

module Agdelte.Html.Types where

open import Data.String using (String)
open import Data.List using (List; []; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; not)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Attributes
------------------------------------------------------------------------

-- HTML element attribute
data Attr (Msg : Set) : Set where
  -- Regular attribute (name="value")
  attr : String → String → Attr Msg
  -- Boolean attribute (disabled, checked, etc.)
  boolAttr : String → Attr Msg
  -- CSS style
  style : String → String → Attr Msg
  -- Event handler
  on : String → Msg → Attr Msg
  -- Event handler with preventDefault (for navigation)
  onPrevent : String → Msg → Attr Msg
  -- Event handler with data (for input)
  onInput : (String → Msg) → Attr Msg
  -- Key event handler
  onKey : String → (String → Msg) → Attr Msg
  -- Key for efficient diffing
  key : String → Attr Msg

-- FFI for Attr constructors
-- Msg parameter is erased at compile time
{-# COMPILE JS attr = name => value => ({ type: 'attr', name, value }) #-}
{-# COMPILE JS boolAttr = name => ({ type: 'boolAttr', name }) #-}
{-# COMPILE JS style = name => value => ({ type: 'style', name, value }) #-}
{-# COMPILE JS on = name => value => ({ type: 'on', name, value }) #-}
{-# COMPILE JS onPrevent = name => value => ({ type: 'onPrevent', name, value }) #-}
{-# COMPILE JS onInput = handler => ({ type: 'onInput', handler }) #-}
{-# COMPILE JS onKey = name => handler => ({ type: 'onKey', name, handler }) #-}
{-# COMPILE JS key = value => ({ type: 'key', value }) #-}

------------------------------------------------------------------------
-- HTML elements
------------------------------------------------------------------------

-- Virtual DOM node
data Html (Msg : Set) : Set where
  -- Element: tag, attributes, children
  node : String → List (Attr Msg) → List (Html Msg) → Html Msg
  -- Text node
  text : String → Html Msg
  -- Keyed element (for lists)
  keyed : String → List (Attr Msg) → List (String × Html Msg) → Html Msg
  -- NOTE: lazy requires Set₁, removed from MVP
  -- lazy : ∀ {A : Set} → A → (A → Html Msg) → Html Msg

-- FFI for Html constructors
-- Msg parameter is erased at compile time
{-# COMPILE JS node = tag => attrs => children => ({ tag, attrs, children }) #-}
{-# COMPILE JS text = s => ({ tag: 'TEXT', text: s }) #-}
{-# COMPILE JS keyed = tag => attrs => children => ({ tag, attrs, children, keyed: true }) #-}

------------------------------------------------------------------------
-- Functor for Attr and Html
------------------------------------------------------------------------

-- Transform messages in Attr
mapAttr : ∀ {A B : Set} → (A → B) → Attr A → Attr B
mapAttr f (attr name value) = attr name value
mapAttr f (boolAttr name) = boolAttr name
mapAttr f (style prop value) = style prop value
mapAttr f (on event msg) = on event (f msg)
mapAttr f (onPrevent event msg) = onPrevent event (f msg)
mapAttr f (onInput handler) = onInput (f ∘ handler)
mapAttr f (onKey event handler) = onKey event (f ∘ handler)
mapAttr f (key k) = key k

-- FFI for mapAttr (works with plain objects)
{-# COMPILE JS mapAttr = _ => _ => f => attr => {
  if (!attr) return attr;
  switch (attr.type) {
    case 'on': return { type: 'on', name: attr.name, value: f(attr.value) };
    case 'onPrevent': return { type: 'onPrevent', name: attr.name, value: f(attr.value) };
    case 'onInput': return { type: 'onInput', handler: x => f(attr.handler(x)) };
    case 'onKey': return { type: 'onKey', name: attr.name, handler: x => f(attr.handler(x)) };
    default: return attr;
  }
} #-}

-- Transform messages in Html
{-# TERMINATING #-}
mapHtml : ∀ {A B : Set} → (A → B) → Html A → Html B
mapHtml f (node tag attrs children) =
  node tag (map (mapAttr f) attrs) (map (mapHtml f) children)
mapHtml f (text s) = text s
mapHtml f (keyed tag attrs children) =
  keyed tag (map (mapAttr f) attrs) (map (λ p → proj₁ p , mapHtml f (proj₂ p)) children)

-- FFI for mapHtml (works with plain objects)
{-# COMPILE JS mapHtml = _ => _ => f => html => {
  if (!html) return html;
  if (html.tag === 'TEXT') return html;
  const mapA = attr => {
    if (!attr) return attr;
    switch (attr.type) {
      case 'on': return { type: 'on', name: attr.name, value: f(attr.value) };
      case 'onPrevent': return { type: 'onPrevent', name: attr.name, value: f(attr.value) };
      case 'onInput': return { type: 'onInput', handler: x => f(attr.handler(x)) };
      case 'onKey': return { type: 'onKey', name: attr.name, handler: x => f(attr.handler(x)) };
      default: return attr;
    }
  };
  const mapH = h => {
    if (!h) return h;
    if (h.tag === 'TEXT') return h;
    return {
      tag: h.tag,
      attrs: Array.isArray(h.attrs) ? h.attrs.map(mapA) : h.attrs,
      children: Array.isArray(h.children) ? h.children.map(mapH) : h.children,
      keyed: h.keyed
    };
  };
  return mapH(html);
} #-}

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Empty element
empty : ∀ {Msg : Set} → Html Msg
empty = text ""

-- Grouping without wrapper (fragment)
fragment : ∀ {Msg : Set} → List (Html Msg) → Html Msg
fragment children = node "div" [] children  -- In practice we use Fragment

-- Conditional rendering
when : ∀ {Msg : Set} → Bool → Html Msg → Html Msg
when true  h = h
when false _ = empty

-- Unless
unless : ∀ {Msg : Set} → Bool → Html Msg → Html Msg
unless b = when (not b)
