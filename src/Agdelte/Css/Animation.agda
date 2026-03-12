{-# OPTIONS --without-K #-}

-- Css.Animation: typed CSS animation shorthand
--
-- Usage:
--   animation' (anim "fadeIn" (ms 300))
--   → "animation" ∶ "fadeIn 300ms ease"
--
--   animations (anim "fadeIn" (ms 300) ∷ anim "slideUp" (ms 200) ∷ [])
--   → "animation" ∶ "fadeIn 300ms ease, slideUp 200ms ease"

module Agdelte.Css.Animation where

open import Data.Nat using (ℕ; _*_; _⊓_)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)

open import Agdelte.Css.Decl using (Decl; Style; _∶_)
open import Agdelte.Css.Easing using (Easing; Duration; showEasing; showDuration; renderDelay; ms; ease)
open import Agdelte.Css.Stylesheet using (Rule; rule; keyframe)

------------------------------------------------------------------------
-- Keyframe stop
------------------------------------------------------------------------

data Stop : Set where
  at   : ℕ → Stop
  from : Stop
  to   : Stop

-- `at` values are clamped to 0-100 (valid CSS @keyframes range).
showStop : Stop → String
showStop (at n) = show (n ⊓ 100) ++ "%"
showStop from   = "from"
showStop to     = "to"

------------------------------------------------------------------------
-- Keyframes (typed wrapper)
------------------------------------------------------------------------

record Keyframes : Set where
  constructor mkKeyframes
  field
    name  : String
    stops : List (Stop × Style)

-- Convert typed Keyframes to a Stylesheet Rule
private
  mapStops : List (Stop × Style) → List (String × Style)
  mapStops []              = []
  mapStops ((s , st) ∷ ss) = (showStop s , st) ∷ mapStops ss

keyframeRule : Keyframes → Rule
keyframeRule kf = keyframe (Keyframes.name kf) (mapStops (Keyframes.stops kf))

------------------------------------------------------------------------
-- Fill mode
------------------------------------------------------------------------

data FillMode : Set where
  fmNone fmForwards fmBackwards fmBoth : FillMode

showFillMode : FillMode → String
showFillMode fmNone      = "none"
showFillMode fmForwards  = "forwards"
showFillMode fmBackwards = "backwards"
showFillMode fmBoth      = "both"

------------------------------------------------------------------------
-- Direction
------------------------------------------------------------------------

data Direction : Set where
  normal reverse alternate alternateReverse : Direction

showDirection : Direction → String
showDirection normal           = "normal"
showDirection reverse          = "reverse"
showDirection alternate        = "alternate"
showDirection alternateReverse = "alternate-reverse"

------------------------------------------------------------------------
-- Iteration count
------------------------------------------------------------------------

data IterCount : Set where
  times    : ℕ → IterCount
  infinite : IterCount

showIterCount : IterCount → String
showIterCount (times n) = show n
showIterCount infinite  = "infinite"

------------------------------------------------------------------------
-- Animation
------------------------------------------------------------------------

record Animation : Set where
  constructor mkAnim
  field
    animName  : String
    dur       : Duration
    easing    : Easing
    delay     : Duration
    count     : IterCount
    direction : Direction
    fillMode  : FillMode

-- Convenience: sensible defaults
anim : String → Duration → Animation
anim n d = mkAnim n d ease (ms 0) (times 1) normal fmNone

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

private
  renderCount : IterCount → String
  renderCount (times 1) = ""
  renderCount c         = " " ++ showIterCount c

  renderDir : Direction → String
  renderDir normal = ""
  renderDir d      = " " ++ showDirection d

  renderFill : FillMode → String
  renderFill fmNone = ""
  renderFill f      = " " ++ showFillMode f

  -- CSS animation shorthand: name LAST to avoid keyword collision.
  -- If name appears first and matches a CSS keyword (e.g. "reverse", "ease",
  -- "none", "infinite"), the browser parses it as a property value, not a name.
  -- CSS spec recommends <custom-ident> last in the shorthand.
  renderAnim : Animation → String
  renderAnim a =
    showDuration (Animation.dur a) ++ " "
    ++ showEasing (Animation.easing a)
    ++ renderDelay (Animation.delay a)
    ++ renderCount (Animation.count a)
    ++ renderDir (Animation.direction a)
    ++ renderFill (Animation.fillMode a)
    ++ " " ++ Animation.animName a

  renderAnims : List Animation → String
  renderAnims []       = "none"
  renderAnims (a ∷ []) = renderAnim a
  renderAnims (a ∷ as) = renderAnim a ++ ", " ++ renderAnims as

------------------------------------------------------------------------
-- Decl constructors
------------------------------------------------------------------------

animation' : Animation → Decl
animation' a = "animation" ∶ renderAnim a

animations : List Animation → Decl
animations as = "animation" ∶ renderAnims as

-- Stagger helper: animation-delay for foreach items
staggerDelay : ℕ → ℕ → Decl
staggerDelay index stepMs = "animation-delay" ∶ showDuration (ms (index * stepMs))
