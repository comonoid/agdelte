{-# OPTIONS --without-K #-}

-- Widget Lenses: UI without Virtual DOM
-- The core goal of Agdelte: Svelte-style direct updates through lenses

module Agdelte.Lens.Widget where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map; length) renaming (_++_ to _++L_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- DOM Path: location in the DOM tree
------------------------------------------------------------------------

-- Path to a DOM node
data Path : Set where
  here : Path                           -- current node
  child : ℕ → Path → Path               -- nth child, then follow path
  attr : String → Path                  -- attribute at current node
  text : Path                           -- text content at current node

-- DOM Mutation: what to do at a path
data Mutation : Set where
  setText : String → Mutation           -- set text content
  setAttr : String → String → Mutation  -- set attribute value
  remove : Mutation                     -- remove node
  -- More mutations can be added: insert, replace, etc.

------------------------------------------------------------------------
-- Widget: lens from Model to DOM
------------------------------------------------------------------------

-- A Widget describes how to render and update a piece of UI
-- Key difference from Html: Widget knows HOW to update, not just WHAT to show
record Widget (Model Msg : Set) : Set₁ where
  constructor mkWidget
  field
    -- Initial DOM structure (like current view)
    -- Returns list of (path, initial-text/attr) pairs
    -- Runtime uses this for first render
    template : List (Path × String)

    -- Which paths need updating when model changes
    -- Given old and new model, return list of mutations
    -- This is the key: no diffing, just direct computation!
    diff : Model → Model → List (Path × Mutation)

    -- Event handlers: path → handler that produces Msg
    handlers : List (Path × String × (String → Msg))  -- path, event-name, handler

open Widget public

------------------------------------------------------------------------
-- Simple Widget constructors
------------------------------------------------------------------------

-- Static text (never changes)
staticText : ∀ {Model Msg} → String → Widget Model Msg
staticText s = mkWidget
  ((text , s) ∷ [])
  (λ _ _ → [])  -- no updates ever
  []

-- Dynamic text that shows model (for simple cases)
-- showFn converts model to string
dynamicText : ∀ {Msg} → (ℕ → String) → Widget ℕ Msg
dynamicText showFn = mkWidget
  ((text , "") ∷ [])  -- initial empty, will be set
  (λ old new → if old ≡? new then [] else (text , setText (showFn new)) ∷ [])
  []
  where
    _≡?_ : ℕ → ℕ → Bool
    zero ≡? zero = true
    suc m ≡? suc n = m ≡? n
    _ ≡? _ = false

------------------------------------------------------------------------
-- Widget combinators
------------------------------------------------------------------------

-- Wrap widget in an element
element : ∀ {Model Msg} → String → List (String × String) → Widget Model Msg → Widget Model Msg
element tag attrs inner = mkWidget
  (map (λ { (p , s) → (child 0 p , s) }) (template inner))
  (λ old new → map (λ { (p , m) → (child 0 p , m) }) (diff inner old new))
  (map (λ { (p , e , h) → (child 0 p , e , h) }) (handlers inner))

-- Combine widgets side by side
beside : ∀ {Model Msg} → Widget Model Msg → Widget Model Msg → Widget Model Msg
beside w1 w2 = mkWidget
  (map (λ { (p , s) → (child 0 p , s) }) (template w1)
   ++L
   map (λ { (p , s) → (child 1 p , s) }) (template w2))
  (λ old new →
    map (λ { (p , m) → (child 0 p , m) }) (diff w1 old new)
    ++L
    map (λ { (p , m) → (child 1 p , m) }) (diff w2 old new))
  (map (λ { (p , e , h) → (child 0 p , e , h) }) (handlers w1)
   ++L
   map (λ { (p , e , h) → (child 1 p , e , h) }) (handlers w2))

------------------------------------------------------------------------
-- Focus: zoom into part of model
------------------------------------------------------------------------

-- Focus widget on part of model using getter
focus : ∀ {Model Model' Msg} → (Model → Model') → Widget Model' Msg → Widget Model Msg
focus get w = mkWidget
  (template w)
  (λ old new → diff w (get old) (get new))
  (handlers w)

------------------------------------------------------------------------
-- Widget App: application using Widget instead of view
------------------------------------------------------------------------

record WidgetApp (Model Msg : Set) : Set₁ where
  constructor mkWidgetApp
  field
    init : Model
    update : Msg → Model → Model
    widget : Widget Model Msg

open WidgetApp public

------------------------------------------------------------------------
-- Polynomial Connection: Widget as IncLens
------------------------------------------------------------------------

-- DOM as a polynomial:
-- - Pos: the possible DOM states (rendered views)
-- - Dir: mutations that can be applied (Path × Mutation)
--
-- Model as a polynomial:
-- - Pos: the possible model states
-- - Dir: messages that update the model
--
-- Widget is essentially: IncLens ModelPoly DOMPoly
-- - onPos: model → view (initial render)
-- - onDir: Msg → [Path × Mutation] (how to update DOM when message arrives)
-- - onDelta: (m₁ → m₂) → [Path × Mutation] (how model change affects DOM)
--
-- The key insight: we compute mutations DIRECTLY from model changes,
-- not by diffing the view output. This is the Svelte approach!

------------------------------------------------------------------------
-- FFI: Runtime for Widget (no Virtual DOM!)
-- All conversion happens in JavaScript - see runtime/widget.js
------------------------------------------------------------------------

-- The runtime interprets:
-- - Path as navigation: here=root, child n p=nth child then p, text=textContent, attr=attribute
-- - Mutation as DOM operation: setText, setAttr, remove
-- - Widget.diff(oldModel, newModel) returns mutations to apply
-- - Widget.handlers provides event bindings
--
-- This completely bypasses the Virtual DOM - no diffing, just direct mutation!
