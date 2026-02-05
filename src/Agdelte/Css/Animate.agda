{-# OPTIONS --without-K #-}

-- Css.Animate: ready-made keyframe presets
--
-- Prebuilt animations for common UI patterns.
-- Use with Stylesheet:
--
--   appCSS =
--       keyframeRule fadeIn
--     ∷ keyframeRule slideInUp
--     ∷ rule ".enter" (animation' (anim "fadeIn" (ms 300)) ∷ [])
--     ∷ []

module Agdelte.Css.Animate where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Animation using (Stop; at; from; to; Keyframes; mkKeyframes)

------------------------------------------------------------------------
-- Entrances
------------------------------------------------------------------------

fadeIn : Keyframes
fadeIn = mkKeyframes "fadeIn"
  ( (from , "opacity" ∶ "0" ∷ [])
  ∷ (to   , "opacity" ∶ "1" ∷ [])
  ∷ [])

fadeInUp : Keyframes
fadeInUp = mkKeyframes "fadeInUp"
  ( (from , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(20px)" ∷ [])
  ∷ (to   , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"   ∷ [])
  ∷ [])

fadeInDown : Keyframes
fadeInDown = mkKeyframes "fadeInDown"
  ( (from , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-20px)" ∷ [])
  ∷ (to   , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"    ∷ [])
  ∷ [])

fadeInLeft : Keyframes
fadeInLeft = mkKeyframes "fadeInLeft"
  ( (from , "opacity" ∶ "0" ∷ "transform" ∶ "translateX(-20px)" ∷ [])
  ∷ (to   , "opacity" ∶ "1" ∷ "transform" ∶ "translateX(0)"    ∷ [])
  ∷ [])

fadeInRight : Keyframes
fadeInRight = mkKeyframes "fadeInRight"
  ( (from , "opacity" ∶ "0" ∷ "transform" ∶ "translateX(20px)" ∷ [])
  ∷ (to   , "opacity" ∶ "1" ∷ "transform" ∶ "translateX(0)"   ∷ [])
  ∷ [])

slideInUp : Keyframes
slideInUp = mkKeyframes "slideInUp"
  ( (from , "transform" ∶ "translateY(100%)" ∷ [])
  ∷ (to   , "transform" ∶ "translateY(0)"   ∷ [])
  ∷ [])

slideInDown : Keyframes
slideInDown = mkKeyframes "slideInDown"
  ( (from , "transform" ∶ "translateY(-100%)" ∷ [])
  ∷ (to   , "transform" ∶ "translateY(0)"    ∷ [])
  ∷ [])

slideInLeft : Keyframes
slideInLeft = mkKeyframes "slideInLeft"
  ( (from , "transform" ∶ "translateX(-100%)" ∷ [])
  ∷ (to   , "transform" ∶ "translateX(0)"    ∷ [])
  ∷ [])

slideInRight : Keyframes
slideInRight = mkKeyframes "slideInRight"
  ( (from , "transform" ∶ "translateX(100%)" ∷ [])
  ∷ (to   , "transform" ∶ "translateX(0)"   ∷ [])
  ∷ [])

scaleIn : Keyframes
scaleIn = mkKeyframes "scaleIn"
  ( (from , "transform" ∶ "scale(0)" ∷ "opacity" ∶ "0" ∷ [])
  ∷ (to   , "transform" ∶ "scale(1)" ∷ "opacity" ∶ "1" ∷ [])
  ∷ [])

zoomIn : Keyframes
zoomIn = mkKeyframes "zoomIn"
  ( (from , "transform" ∶ "scale(0.3)" ∷ "opacity" ∶ "0" ∷ [])
  ∷ (to   , "transform" ∶ "scale(1)"   ∷ "opacity" ∶ "1" ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Exits
------------------------------------------------------------------------

fadeOut : Keyframes
fadeOut = mkKeyframes "fadeOut"
  ( (from , "opacity" ∶ "1" ∷ [])
  ∷ (to   , "opacity" ∶ "0" ∷ [])
  ∷ [])

fadeOutUp : Keyframes
fadeOutUp = mkKeyframes "fadeOutUp"
  ( (from , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"    ∷ [])
  ∷ (to   , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-20px)" ∷ [])
  ∷ [])

fadeOutDown : Keyframes
fadeOutDown = mkKeyframes "fadeOutDown"
  ( (from , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"   ∷ [])
  ∷ (to   , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(20px)" ∷ [])
  ∷ [])

slideOutUp : Keyframes
slideOutUp = mkKeyframes "slideOutUp"
  ( (from , "transform" ∶ "translateY(0)"    ∷ [])
  ∷ (to   , "transform" ∶ "translateY(-100%)" ∷ [])
  ∷ [])

slideOutDown : Keyframes
slideOutDown = mkKeyframes "slideOutDown"
  ( (from , "transform" ∶ "translateY(0)"   ∷ [])
  ∷ (to   , "transform" ∶ "translateY(100%)" ∷ [])
  ∷ [])

scaleOut : Keyframes
scaleOut = mkKeyframes "scaleOut"
  ( (from , "transform" ∶ "scale(1)" ∷ "opacity" ∶ "1" ∷ [])
  ∷ (to   , "transform" ∶ "scale(0)" ∷ "opacity" ∶ "0" ∷ [])
  ∷ [])

zoomOut : Keyframes
zoomOut = mkKeyframes "zoomOut"
  ( (from , "transform" ∶ "scale(1)"   ∷ "opacity" ∶ "1" ∷ [])
  ∷ (to   , "transform" ∶ "scale(0.3)" ∷ "opacity" ∶ "0" ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Attention seekers
------------------------------------------------------------------------

pulse : Keyframes
pulse = mkKeyframes "pulse"
  ( (from , "transform" ∶ "scale(1)"    ∷ [])
  ∷ (at 50 , "transform" ∶ "scale(1.05)" ∷ [])
  ∷ (to   , "transform" ∶ "scale(1)"    ∷ [])
  ∷ [])

bounce : Keyframes
bounce = mkKeyframes "bounce"
  ( (from  , "transform" ∶ "translateY(0)"    ∷ [])
  ∷ (at 40 , "transform" ∶ "translateY(-30px)" ∷ [])
  ∷ (at 60 , "transform" ∶ "translateY(-15px)" ∷ [])
  ∷ (to    , "transform" ∶ "translateY(0)"    ∷ [])
  ∷ [])

shake : Keyframes
shake = mkKeyframes "shake"
  ( (at 0  , "transform" ∶ "translateX(0)"    ∷ [])
  ∷ (at 25 , "transform" ∶ "translateX(-4px)" ∷ [])
  ∷ (at 50 , "transform" ∶ "translateX(4px)"  ∷ [])
  ∷ (at 75 , "transform" ∶ "translateX(-4px)" ∷ [])
  ∷ (at 100 , "transform" ∶ "translateX(0)"    ∷ [])
  ∷ [])

wobble : Keyframes
wobble = mkKeyframes "wobble"
  ( (at 0  , "transform" ∶ "rotate(0deg)"   ∷ [])
  ∷ (at 25 , "transform" ∶ "rotate(-5deg)"  ∷ [])
  ∷ (at 50 , "transform" ∶ "rotate(3deg)"   ∷ [])
  ∷ (at 75 , "transform" ∶ "rotate(-2deg)"  ∷ [])
  ∷ (at 100 , "transform" ∶ "rotate(0deg)"   ∷ [])
  ∷ [])

flash : Keyframes
flash = mkKeyframes "flash"
  ( (from  , "opacity" ∶ "1" ∷ [])
  ∷ (at 25 , "opacity" ∶ "0" ∷ [])
  ∷ (at 50 , "opacity" ∶ "1" ∷ [])
  ∷ (at 75 , "opacity" ∶ "0" ∷ [])
  ∷ (to    , "opacity" ∶ "1" ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Loops
------------------------------------------------------------------------

spin : Keyframes
spin = mkKeyframes "spin"
  ( (from , "transform" ∶ "rotate(0deg)"   ∷ [])
  ∷ (to   , "transform" ∶ "rotate(360deg)" ∷ [])
  ∷ [])
