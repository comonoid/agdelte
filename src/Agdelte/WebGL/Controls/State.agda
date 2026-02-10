{-# OPTIONS --without-K #-}

-- WebGL Controls State
--
-- Manages control states (normal, hover, active, disabled)
-- and provides state-aware styling.

module Agdelte.WebGL.Controls.State where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Controls.Theme

------------------------------------------------------------------------
-- Control state
------------------------------------------------------------------------

data ControlState : Set where
  Normal   : ControlState
  Hovered  : ControlState
  Active   : ControlState
  Disabled : ControlState

------------------------------------------------------------------------
-- State-based styling
------------------------------------------------------------------------

-- Get material for current state
stateMaterial : ControlTheme → ControlState → Material
stateMaterial theme Normal   = normalMaterial theme
stateMaterial theme Hovered  = hoverMaterial theme
stateMaterial theme Active   = activeMaterial theme
stateMaterial theme Disabled = disabledMaterial theme

-- Get text color for current state
stateTextColor : ControlTheme → ControlState → GlColor
stateTextColor theme Normal   = ControlTheme.foregroundColor theme
stateTextColor theme Hovered  = ControlTheme.foregroundColor theme
stateTextColor theme Active   = ControlTheme.foregroundColor theme
stateTextColor theme Disabled = ControlTheme.disabledColor theme

-- Get accent color for current state
stateAccentColor : ControlTheme → ControlState → GlColor
stateAccentColor theme Normal   = ControlTheme.primaryColor theme
stateAccentColor theme Hovered  = ControlTheme.hoverColor theme
stateAccentColor theme Active   = ControlTheme.activeColor theme
stateAccentColor theme Disabled = ControlTheme.disabledColor theme

------------------------------------------------------------------------
-- State transitions
------------------------------------------------------------------------

-- Hover changes state unless disabled
applyHover : ControlState → Bool → ControlState
applyHover Disabled _ = Disabled
applyHover _ true     = Hovered
applyHover _ false    = Normal

-- Active state (pressed)
applyActive : ControlState → Bool → ControlState
applyActive Disabled _ = Disabled
applyActive _ true     = Active
applyActive s false    = s

------------------------------------------------------------------------
-- Stateful control record
--
-- Used for controls that need to track hover/active state in the model.
------------------------------------------------------------------------

record StatefulControl (Msg : Set) : Set where
  constructor mkStateful
  field
    state        : ControlState
    hoverHandler : Bool → Msg
    activeHandler : Bool → Msg

-- Create initial stateful control
initStateful : ∀ {Msg} → (Bool → Msg) → (Bool → Msg) → StatefulControl Msg
initStateful hoverMsg activateMsg = mkStateful Normal hoverMsg activateMsg

-- Get state from model with hover/active tracking
-- Usage: bindMaterial (λ m → stateMaterial theme (getCtrlState m)) ...
getCtrlState : ∀ {Msg} → StatefulControl Msg → ControlState
getCtrlState = StatefulControl.state

-- Update state on hover
updateHover : ∀ {Msg} → Bool → StatefulControl Msg → StatefulControl Msg
updateHover hovered ctrl = record ctrl { state = applyHover (StatefulControl.state ctrl) hovered }

-- Update state on active
updateActive : ∀ {Msg} → Bool → StatefulControl Msg → StatefulControl Msg
updateActive active ctrl = record ctrl { state = applyActive (StatefulControl.state ctrl) active }

------------------------------------------------------------------------
-- State equality
------------------------------------------------------------------------

eqControlState : ControlState → ControlState → Bool
eqControlState Normal   Normal   = true
eqControlState Hovered  Hovered  = true
eqControlState Active   Active   = true
eqControlState Disabled Disabled = true
eqControlState _ _               = false
