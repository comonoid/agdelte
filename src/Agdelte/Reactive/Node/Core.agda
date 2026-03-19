{-# OPTIONS --without-K #-}

-- Core types: Binding, Transition, Attr, Node, ReactiveApp.
-- Re-exported by Agdelte.Reactive.Node for backward compatibility.

module Agdelte.Reactive.Node.Core where

open import Data.String using (String; _++_; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)
open import Relation.Nullary using (yes; no)

open import Agdelte.Core.Event using (Event; never)
open import Agdelte.Core.Cmd using (Cmd; ε)

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
-- "" (not "false") is intentional: HTML boolean attributes are presence-based.
-- The runtime removes the attribute when the value is "", adds it when "true".
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

-- NO_UNIVERSE_CHECK: constructors like foreach/foreachKeyed/glCanvas quantify
-- over (A : Set), which would lift Attr/Node to Set₁. We use NO_UNIVERSE_CHECK
-- to keep them in Set, consistent with Event's approach. Safe for the JS backend
-- (Scott encoding erases universe levels).
{-# NO_UNIVERSE_CHECK #-}
data Attr (Model Msg : Set) : Set where
  -- Static attribute
  attr : String → String → Attr Model Msg
  -- Dynamic attribute (bound to model)
  attrBind : String → Binding Model String → Attr Model Msg
  -- Event handler
  on : String → Msg → Attr Model Msg
  -- Event with value (e.g., onInput)
  onValue : String → (String → Msg) → Attr Model Msg
  -- Event with custom property path (e.g., "target.currentTime", "target.duration")
  onValueFrom : String → String → (String → Msg) → Attr Model Msg
  -- Event with screen coordinates (for drag/pan - no SVG conversion)
  onValueScreen : String → (String → Msg) → Attr Model Msg
  -- Keyboard event filtered to specific keys; calls preventDefault
  onKeyFiltered : List String → (String → Msg) → Attr Model Msg
  -- Style
  style : String → String → Attr Model Msg
  -- Dynamic style
  styleBind : String → Binding Model String → Attr Model Msg

-- Node: the reactive template
{-# NO_UNIVERSE_CHECK #-}
data Node (Model Msg : Set) : Set where
  -- Static text (never changes)
  text : String → Node Model Msg

  -- Dynamic text bound to model
  bind : Binding Model String → Node Model Msg

  -- Element with attributes and children
  elem : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg

  -- Empty node (renders nothing)
  empty : Node Model Msg

  -- Conditional rendering: when condition is true, render the node
  when : (Model → Bool) → Node Model Msg → Node Model Msg

  -- Dynamic list of children
  foreach : ∀ {A : Set} → (Model → List A) → (A → ℕ → Node Model Msg) → Node Model Msg

  -- Keyed dynamic list: key-based reconciliation
  foreachKeyed : ∀ {A : Set} → (Model → List A) → (A → String) → (A → ℕ → Node Model Msg) → Node Model Msg

  -- Conditional rendering with enter/leave CSS transitions
  whenT : (Model → Bool) → Transition → Node Model Msg → Node Model Msg

  -- Scope cutoff (manual): string fingerprint for subtree skipping
  scope : (Model → String) → Node Model Msg → Node Model Msg

  -- Scope cutoff (automatic): projection function for subtree skipping
  scopeProj : ∀ {M' : Set} → (Model → M') → Node Model Msg → Node Model Msg

  -- Runtime-deferred zoom
  zoomRT : ∀ {M' Msg' : Set} → (Model → M') → (Msg' → Msg) → Node M' Msg' → Node Model Msg

  -- WebGL canvas: DOM attributes + opaque scene data
  glCanvas : ∀ {S : Set} → List (Attr Model Msg) → S → Node Model Msg

------------------------------------------------------------------------
-- ReactiveApp: Application with reactive template (full TEA)
------------------------------------------------------------------------

record ReactiveApp (Model Msg : Set) : Set where
  constructor mkReactiveApp
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg
    cmd      : Msg → Model → Cmd Msg
    subs     : Model → Event Msg

open ReactiveApp public

-- Simple app constructor (no commands or subscriptions)
simpleApp : ∀ {Model Msg} → Model → (Msg → Model → Model) → Node Model Msg → ReactiveApp Model Msg
simpleApp init' update' template' = mkReactiveApp init' update' template' (λ _ _ → ε) (const never)
