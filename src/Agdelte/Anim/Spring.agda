{-# OPTIONS --without-K #-}

-- Anim.Spring: spring physics for model-driven animation
--
-- The killer feature CSS can't do. A spring is real physics:
-- position is driven by force = stiffness * (target - pos) - damping * velocity.
--
-- Usage:
--   let s = gentle 0.0 1.0        -- smooth spring from 0 to 1
--       s' = tickSpring s 16       -- advance by 16ms
--   -- Spring.position s' is the current value
--
-- Presets:
--   gentle  — iOS-like smooth (stiffness 120, damping 14)
--   snappy  — quick, minimal overshoot (stiffness 400, damping 28)
--   bouncy  — playful bounce (stiffness 180, damping 8)

module Agdelte.Anim.Spring where

open import Data.Nat using (ℕ; zero; suc; _/_; _%_)
open import Data.Bool using (Bool; _∧_)

import Data.Float as F
import Data.Float.Base as FB

------------------------------------------------------------------------
-- Spring
------------------------------------------------------------------------

record Spring : Set where
  constructor mkSpring
  field
    position  : F.Float
    velocity  : F.Float
    target    : F.Float
    stiffness : F.Float    -- spring constant (higher = snappier)
    damping   : F.Float    -- friction (higher = less bounce)

------------------------------------------------------------------------
-- Tick (Euler integration)
------------------------------------------------------------------------

tickSpring : Spring → ℕ → Spring
tickSpring s dt =
  let dtSec = FB.fromℕ dt F.÷ 1000.0
      force = Spring.stiffness s F.* (Spring.target s F.- Spring.position s)
              F.- Spring.damping s F.* Spring.velocity s
      v' = Spring.velocity s F.+ force F.* dtSec
      p' = Spring.position s F.+ v' F.* dtSec
  in mkSpring p' v' (Spring.target s) (Spring.stiffness s) (Spring.damping s)

------------------------------------------------------------------------
-- Fixed-step tick (stable for stiff springs and large dt)
------------------------------------------------------------------------

-- Subdivide dt into steps of at most 4ms to prevent Euler divergence
-- on stiff springs or after tab-backgrounding (dt > 100ms).
-- Raw tickSpring remains available when the caller controls dt directly.

private
  steps : ℕ → Spring → Spring
  steps zero    s = s
  steps (suc n) s = steps n (tickSpring s 4)

tickSpringStable : Spring → ℕ → Spring
tickSpringStable s dt =
  let full = dt / 4
      rem  = dt % 4
  in tickSpring (steps full s) rem

------------------------------------------------------------------------
-- Query
------------------------------------------------------------------------

private
  absF : F.Float → F.Float
  absF x = if x FB.<ᵇ 0.0 then FB.- x else x
    where open import Data.Bool using (if_then_else_)

isSettled : Spring → Bool
isSettled s =
  (absF (Spring.position s F.- Spring.target s) FB.<ᵇ 0.01)
  ∧ (absF (Spring.velocity s) FB.<ᵇ 0.01)

------------------------------------------------------------------------
-- Retarget (interrupt mid-flight, velocity carries over)
------------------------------------------------------------------------

retarget : F.Float → Spring → Spring
retarget newTarget s =
  mkSpring (Spring.position s) (Spring.velocity s) newTarget
           (Spring.stiffness s) (Spring.damping s)

------------------------------------------------------------------------
-- Presets
------------------------------------------------------------------------

-- iOS-like smooth spring
gentle : F.Float → F.Float → Spring
gentle from to = mkSpring from 0.0 to 120.0 14.0

-- Snappy, minimal overshoot
snappy : F.Float → F.Float → Spring
snappy from to = mkSpring from 0.0 to 400.0 28.0

-- Bouncy, playful
bouncy : F.Float → F.Float → Spring
bouncy from to = mkSpring from 0.0 to 180.0 8.0
