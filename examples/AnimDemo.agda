{-# OPTIONS --without-K #-}

-- AnimDemo: model-driven animations (Tween + Spring)
--
-- These produce Float values, not CSS strings. In a real app they'd
-- drive styleBind (e.g. "opacity" bound to tween output), but here
-- we export computed values for compile-time verification.

module AnimDemo where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import Data.Float as F
import Data.Float.Base as FB

open import Agdelte.Css.Easing using (linearFn; easeOutFn; easeInOutFn)
open import Agdelte.Anim.Tween
open import Agdelte.Anim.Spring

------------------------------------------------------------------------
-- Tween examples
------------------------------------------------------------------------

-- Opacity fade: 0.0 → 1.0 over 300ms with easeOut
opacityTween : Tween F.Float
opacityTween = mkTween 0 300 0.0 1.0 easeOutFn floatLerp

-- Advance 150ms (halfway)
opacityMid : Tween F.Float × F.Float
opacityMid = tickTween opacityTween 150

-- The tween at midpoint (should be > 0.5 due to easeOut)
opacityMidValue : F.Float
opacityMidValue = proj₂ opacityMid

-- Advance to completion
opacityEnd : Tween F.Float × F.Float
opacityEnd = tickTween (proj₁ opacityMid) 150

opacityEndValue : F.Float
opacityEndValue = proj₂ opacityEnd

opacityDone : Bool
opacityDone = isComplete (proj₁ opacityEnd)

-- Retarget mid-flight: was going 0→1, now go to 0.5 from current pos
retargeted : Tween F.Float
retargeted = retargetTween 0.5 (proj₁ opacityMid)

retargetedFrom : F.Float
retargetedFrom = Tween.from retargeted  -- should be ≈ opacityMidValue

-- Linear tween for comparison
linearTween : Tween F.Float
linearTween = mkTween 0 100 0.0 100.0 linearFn floatLerp

-- currentValue at start = 0
linearStart : F.Float
linearStart = currentValue linearTween

------------------------------------------------------------------------
-- Spring examples
------------------------------------------------------------------------

-- Gentle spring: dialog sliding in (0 → 1)
dialogSpring : Spring
dialogSpring = gentle 0.0 1.0

-- After one 16ms frame
dialogFrame1 : Spring
dialogFrame1 = tickSpring dialogSpring 16

dialogPos1 : F.Float
dialogPos1 = Spring.position dialogFrame1

-- Simulate 80 frames (≈1.3 seconds) with stable tick
dialogAfter1s : Spring
dialogAfter1s = simulate 80 dialogSpring
  where
    simulate : ℕ → Spring → Spring
    simulate ℕ.zero    s = s
    simulate (ℕ.suc n) s = simulate n (tickSpringStable s 16)

dialogSettled : Bool
dialogSettled = isSettled dialogAfter1s

dialogFinalPos : F.Float
dialogFinalPos = Spring.position dialogAfter1s

-- Bouncy spring: notification badge
badgeSpring : Spring
badgeSpring = bouncy 0.0 1.0

-- Retarget: user clicks again before spring settles
retargetedSpring : Spring
retargetedSpring = retarget 2.0 (tickSpring badgeSpring 50)

retargetedTarget : F.Float
retargetedTarget = Spring.target retargetedSpring

-- Custom spring parameters
customSpring : Spring
customSpring = mkSpring 0.0 0.0 100.0 300.0 20.0

-- Snappy spring for tab switching
tabSpring : Spring
tabSpring = snappy 0.0 200.0
