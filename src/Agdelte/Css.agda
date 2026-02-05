{-# OPTIONS --without-K #-}

-- Css: re-export all CSS modules
--
-- Stylesheet, Animate are not re-exported (separate build-time concern).
-- Import Agdelte.Css.Stylesheet and Agdelte.Css.Animate directly.
-- Anim.Tween and Anim.Spring are also separate (model-driven animation).

module Agdelte.Css where

open import Agdelte.Css.Decl public
open import Agdelte.Css.Show public
open import Agdelte.Css.Length public
open import Agdelte.Css.Color public
open import Agdelte.Css.Properties public
open import Agdelte.Css.Layout public
open import Agdelte.Css.Variables public
open import Agdelte.Css.Easing public
open import Agdelte.Css.Transition public
open import Agdelte.Css.Animation public
open import Agdelte.Css.Conditional public
