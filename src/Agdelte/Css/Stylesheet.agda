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
  variant  : String → Style → String → Style → Rule   -- (base sel, base style, variant sel, overrides) — guard: base ref prevents merging
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
  renderRuleAt ind (rule sel []) = ""
  renderRuleAt ind (rule sel style) =
    ind ++ sel ++ " {\n"
    ++ renderDecls (ind ++ "  ") style ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (variant baseSel [] varSel []) = ""
  renderRuleAt ind (variant baseSel [] varSel overrides) =
    ind ++ varSel ++ " {\n"
    ++ renderDecls (ind ++ "  ") overrides ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (variant baseSel baseStyle varSel []) =
    ind ++ baseSel ++ " {\n"
    ++ renderDecls (ind ++ "  ") baseStyle ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (variant baseSel baseStyle varSel overrides) =
    ind ++ baseSel ++ " {\n"
    ++ renderDecls (ind ++ "  ") baseStyle ++ "\n"
    ++ ind ++ "}\n\n"
    ++ ind ++ varSel ++ " {\n"
    ++ renderDecls (ind ++ "  ") overrides ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (media _ []) = ""
  renderRuleAt ind (media query rules) =
    ind ++ "@media " ++ query ++ " {\n"
    ++ renderRulesAt (ind ++ "  ") rules ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (keyframe _ []) = ""
  renderRuleAt ind (keyframe name stops) =
    ind ++ "@keyframes " ++ name ++ " {\n"
    ++ renderStops (ind ++ "  ") stops ++ "\n"
    ++ ind ++ "}"
  renderRuleAt ind (rawRule s) = ind ++ s

  -- NOTE: do NOT use `with renderRulesAt ind rs` here. The JS backend compiles a
  -- `with`-scrutinee as a non-memoised thunk and re-evaluates it per clause; when
  -- the scrutinee is the recursive call this is O(2ⁿ) (see
  -- doc/agda-with-scrutinee-bug.md). Instead: render+drop-empties (dispatching on
  -- the head render, not the recursion), then join (dispatching on the list spine).
  -- Each recursive result is used exactly once → linear.

  -- Render each rule and drop empty results. Dispatches on the head render string,
  -- never on the recursive call, which appears once per branch.
  collectNE : String → List Rule → List String
  collectNE ind []       = []
  collectNE ind (r ∷ rs) = consNE (renderRuleAt ind r) (collectNE ind rs)
    where
      consNE : String → List String → List String
      consNE ""  rest = rest
      consNE s   rest = s ∷ rest

  -- Join with a separator. Dispatches on the list spine (cheap), and the
  -- recursive call appears exactly once.
  intercalateS : String → List String → String
  intercalateS sep []        = ""
  intercalateS sep (s ∷ [])  = s
  intercalateS sep (s ∷ ss)  = s ++ sep ++ intercalateS sep ss

  renderRulesAt : String → List Rule → String
  renderRulesAt ind rs = intercalateS "\n\n" (collectNE ind rs)

------------------------------------------------------------------------
-- Public API
------------------------------------------------------------------------

renderRule : Rule → String
renderRule = renderRuleAt ""

-- Same fix as renderRulesAt: no `with` on the recursive call (that is O(2ⁿ) on the
-- JS backend — see doc/agda-with-scrutinee-bug.md). Collect non-empty renders,
-- then join. The recursive structure is consumed once by collectNE/intercalateS.
renderStylesheet : Stylesheet → String
renderStylesheet rs = finish (collectNE "" rs)
  where
    finish : List String → String
    finish []        = ""
    finish (p ∷ ps)  = intercalateS "\n\n" (p ∷ ps) ++ "\n"
