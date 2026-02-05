{-# OPTIONS --without-K #-}

-- Css.Transition: typed CSS transition shorthand
--
-- Usage:
--   transition' (trans "opacity" (ms 300) ease ∷ trans "transform" (ms 200) easeOut ∷ [])
--   → "transition" ∶ "opacity 300ms ease, transform 200ms ease-out"

module Agdelte.Css.Transition where

open import Data.Nat using (ℕ; zero)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Agdelte.Css.Decl using (Decl; _∶_)
open import Agdelte.Css.Easing using (Easing; Duration; showEasing; showDuration; ms)

------------------------------------------------------------------------
-- TransSpec
------------------------------------------------------------------------

record TransSpec : Set where
  constructor mkTransSpec
  field
    property : String
    dur      : Duration
    easing   : Easing
    delay    : Duration

-- Convenience: no delay
trans : String → Duration → Easing → TransSpec
trans p d e = mkTransSpec p d e (ms 0)

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

private
  renderDelay : Duration → String
  renderDelay (ms zero) = ""
  renderDelay d         = " " ++ showDuration d

  renderSpec : TransSpec → String
  renderSpec t =
    TransSpec.property t ++ " "
    ++ showDuration (TransSpec.dur t) ++ " "
    ++ showEasing (TransSpec.easing t)
    ++ renderDelay (TransSpec.delay t)

  renderSpecs : List TransSpec → String
  renderSpecs []       = ""
  renderSpecs (s ∷ []) = renderSpec s
  renderSpecs (s ∷ ss) = renderSpec s ++ ", " ++ renderSpecs ss

------------------------------------------------------------------------
-- Decl constructor
------------------------------------------------------------------------

transition' : List TransSpec → Decl
transition' specs = "transition" ∶ renderSpecs specs
