{-# OPTIONS --without-K #-}

-- Reactive Node: Template with automatic bindings
-- No Virtual DOM - bindings track which parts of DOM need updating
--
-- Key insight: Instead of view : Model → Html (function that rebuilds tree),
-- we have template : Node Model Msg (data structure with bindings)
--
-- This module re-exports everything from submodules for backward compatibility:
--   Core.agda — Binding, Transition, Attr, Node, ReactiveApp
--   Html.agda — smart constructors for elements, events, attributes
--   Zoom.agda — zoom/lens composition for Node and Attr

module Agdelte.Reactive.Node where

open import Agdelte.Reactive.Node.Core public
open import Agdelte.Reactive.Node.Html public
open import Agdelte.Reactive.Node.Zoom public

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
