{-# OPTIONS --without-K #-}

-- Css.Stylesheet: static CSS rule generation
--
-- Compile-time stylesheet from typed rules:
--   rule ".card" (padding' (px 16) ∷ background' (hex "#fff") ∷ [])
--   media "(max-width: 768px)" (rule ".card" (padding' (px 8) ∷ []) ∷ [])
--   keyframe "fadeIn" (("from" , "opacity" ∶ "0" ∷ []) ∷ ("to" , "opacity" ∶ "1" ∷ []) ∷ [])
--
-- renderStylesheet produces a CSS string for <style> mount or .css file.
-- rawRule provides escape hatch for arbitrary CSS text.

module Agdelte.Css.Stylesheet where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Decl; Style; prop; val)

------------------------------------------------------------------------
-- Rule
------------------------------------------------------------------------

data Rule : Set where
  rule     : String → Style → Rule                    -- .class { ... }
  media    : String → List Rule → Rule                -- @media (...) { ... }
  keyframe : String → List (String × Style) → Rule    -- @keyframes name { from {} to {} }
  rawRule  : String → Rule                             -- escape hatch

------------------------------------------------------------------------
-- Stylesheet
------------------------------------------------------------------------

Stylesheet : Set
Stylesheet = List Rule

------------------------------------------------------------------------
-- Rendering (mutual recursion for termination on nested rules)
------------------------------------------------------------------------

private
  renderDecl : String → Decl → String
  renderDecl ind d = ind ++ prop d ++ ": " ++ val d ++ ";"

  renderDecls : String → Style → String
  renderDecls ind []       = ""
  renderDecls ind (d ∷ []) = renderDecl ind d
  renderDecls ind (d ∷ ds) = renderDecl ind d ++ "\n" ++ renderDecls ind ds

  renderStop : String → (String × Style) → String
  renderStop ind (name , style) =
    ind ++ name ++ " {\n"
    ++ renderDecls (ind ++ "  ") style ++ "\n"
    ++ ind ++ "}"

  renderStops : String → List (String × Style) → String
  renderStops ind []       = ""
  renderStops ind (s ∷ []) = renderStop ind s
  renderStops ind (s ∷ ss) = renderStop ind s ++ "\n" ++ renderStops ind ss

mutual
  renderRuleAt : String → Rule → String
  renderRuleAt ind (rule sel style) =
    ind ++ sel ++ " {\n"
    ++ renderDecls (ind ++ "  ") style ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (media query rules) =
    ind ++ "@media " ++ query ++ " {\n"
    ++ renderRulesAt (ind ++ "  ") rules ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (keyframe name stops) =
    ind ++ "@keyframes " ++ name ++ " {\n"
    ++ renderStops (ind ++ "  ") stops ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (rawRule s) = ind ++ s

  renderRulesAt : String → List Rule → String
  renderRulesAt ind []       = ""
  renderRulesAt ind (r ∷ []) = renderRuleAt ind r
  renderRulesAt ind (r ∷ rs) = renderRuleAt ind r ++ "\n\n" ++ renderRulesAt ind rs

------------------------------------------------------------------------
-- Public API
------------------------------------------------------------------------

renderRule : Rule → String
renderRule = renderRuleAt ""

renderStylesheet : Stylesheet → String
renderStylesheet []       = ""
renderStylesheet (r ∷ []) = renderRule r ++ "\n"
renderStylesheet (r ∷ rs) = renderRule r ++ "\n\n" ++ renderStylesheet rs
