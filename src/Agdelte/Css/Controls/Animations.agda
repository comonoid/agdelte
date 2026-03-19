{-# OPTIONS --without-K #-}

-- CSS animations, transition classes, and utility classes for controls

module Agdelte.Css.Controls.Animations where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; keyframe; Stylesheet)

------------------------------------------------------------------------
-- Keyframes
------------------------------------------------------------------------

animationKeyframes : Stylesheet
animationKeyframes =
    keyframe "agdelte-fade-in"
      ( ("from" , "opacity" ∶ "0" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-scale-in"
      ( ("from" , "opacity" ∶ "0" ∷ "transform" ∶ "scale(0.95)" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ "transform" ∶ "scale(1)" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-slide-down"
      ( ("from" , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-8px)" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-slide-in-right"
      ( ("from" , "opacity" ∶ "0" ∷ "transform" ∶ "translateX(100%)" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ "transform" ∶ "translateX(0)" ∷ [])
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Transition classes (for whenT)
------------------------------------------------------------------------

transitionClasses : Stylesheet
transitionClasses =
  -- Fade transition
    rule ".agdelte-enter-fade"
      ( "animation" ∶ "agdelte-fade-in var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-leave-fade"
      ( "animation" ∶ "agdelte-fade-in var(--agdelte-transition) reverse"
      ∷ [])
  -- Scale transition
  ∷ rule ".agdelte-enter-scale"
      ( "animation" ∶ "agdelte-scale-in var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-leave-scale"
      ( "animation" ∶ "agdelte-scale-in var(--agdelte-transition) reverse"
      ∷ [])
  -- Slide down transition
  ∷ rule ".agdelte-enter-slide-down"
      ( "animation" ∶ "agdelte-slide-down var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-leave-slide-down"
      ( "animation" ∶ "agdelte-slide-down var(--agdelte-transition) reverse"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Utility classes
------------------------------------------------------------------------

utilityRules : Stylesheet
utilityRules =
  -- List truncation marker (injected by reactive.js at runtime)
    rule ".agdelte-list-truncated"
      ( "color" ∶ "var(--agdelte-error)"
      ∷ "font-style" ∶ "italic"
      ∷ "list-style" ∶ "none"
      ∷ "padding" ∶ "4px 0"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Combined
------------------------------------------------------------------------

animationsRules : Stylesheet
animationsRules = animationKeyframes ++ transitionClasses ++ utilityRules
