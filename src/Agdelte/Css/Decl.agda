{-# OPTIONS --without-K #-}

-- Css.Decl: Style as composable list of declarations
--
-- Core idea: Style = List Decl, where Decl = prop ∶ val.
-- Convert to List (Attr Model Msg) via toAttrs.
-- Compose via _<>_ (list append — later declarations win in CSS).
-- String escape hatch: Decl is just String × String.

module Agdelte.Css.Decl where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map; _++_)

open import Agdelte.Reactive.Node using (Attr; style)

------------------------------------------------------------------------
-- Declaration: a single CSS property-value pair
------------------------------------------------------------------------

record Decl : Set where
  constructor _∶_
  field
    prop : String
    val  : String

open Decl public

------------------------------------------------------------------------
-- Style: composable list of declarations
------------------------------------------------------------------------

Style : Set
Style = List Decl

------------------------------------------------------------------------
-- Composition: merge two styles (later declarations win in CSS)
------------------------------------------------------------------------

_<>_ : Style → Style → Style
_<>_ = _++_

infixr 5 _<>_

------------------------------------------------------------------------
-- Convert to reactive node attributes
------------------------------------------------------------------------

toAttrs : ∀ {Model Msg : Set} → Style → List (Attr Model Msg)
toAttrs = map (λ d → style (prop d) (val d))

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Single declaration as style
singleton : Decl → Style
singleton d = d ∷ []

-- Empty style
none : Style
none = []
