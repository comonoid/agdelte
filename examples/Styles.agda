{-# OPTIONS --without-K #-}

-- Common styles for Agdelte examples
-- Provides consistent look across all demos

module Styles where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_; _<>_)
open import Agdelte.Css.Length using (px; rem; pct; zero)
open import Agdelte.Css.Color using (hex; named; var)
open import Agdelte.Css.Properties using (padding'; margin'; margin2; backgroundColor';
                                          color'; fontSize'; borderRadius';
                                          gap'; maxWidth')
open import Agdelte.Css.Layout using (row; col; center; wrap; spaceBetween; grid; stack)
open import Agdelte.Css.Variables using (cssVar; varRef)
open import Agdelte.Css.Transition using (trans; transition')
open import Agdelte.Css.Easing using (ease; easeOut; ms; s)
open import Agdelte.Css.Animation using (anim; animation')
open import Agdelte.Css.Animate using (fadeIn; fadeOut; slideInUp; pulse; shake; spin)
open import Agdelte.Css.Stylesheet using (Rule; rule; media; keyframe; rawRule; Stylesheet)

------------------------------------------------------------------------
-- Container styles
------------------------------------------------------------------------

-- Main demo container
demoContainer : Style
demoContainer =
    maxWidth' (px 800)
  ∷ margin' (px 0)
  ∷ padding' (rem 1.0)
  ∷ []

-- Tab/section content panel
tabContent : Style
tabContent =
    padding' (rem 1.0)
  ∷ "min-height" ∶ "200px"
  ∷ []

-- Demo section with spacing
demoSection : Style
demoSection =
    "margin-bottom" ∶ "16px"
  ∷ []

------------------------------------------------------------------------
-- Button styles
------------------------------------------------------------------------

-- Base button (dark theme)
btn : Style
btn =
    padding' (px 10)
  ∷ margin' (px 4)
  ∷ borderRadius' (px 6)
  ∷ fontSize' (rem 1.0)
  ∷ "cursor" ∶ "pointer"
  ∷ "border" ∶ "none"
  ∷ backgroundColor' (hex "#3a3a5a")
  ∷ color' (hex "#eee")
  ∷ "transition" ∶ "transform 0.1s, background 0.2s"
  ∷ []

-- Button variants
btnInfo : Style
btnInfo = btn ++ (backgroundColor' (hex "#4a9eff") ∷ color' (named "white") ∷ [])

btnSuccess : Style
btnSuccess = btn ++ (backgroundColor' (hex "#4ade80") ∷ color' (hex "#1a1a2e") ∷ [])

btnWarning : Style
btnWarning = btn ++ (backgroundColor' (hex "#fbbf24") ∷ color' (hex "#1a1a2e") ∷ [])

btnError : Style
btnError = btn ++ (backgroundColor' (hex "#e94560") ∷ color' (named "white") ∷ [])

-- Button group
btnGroup : Style
btnGroup = row ++ wrap ++ (gap' (px 8) ∷ [])

------------------------------------------------------------------------
-- Display styles
------------------------------------------------------------------------

-- Selected/result display box (dark theme)
displayBox : Style
displayBox =
    "margin-top" ∶ "16px"
  ∷ padding' (px 12)
  ∷ backgroundColor' (hex "#1a3a2a")
  ∷ borderRadius' (px 6)
  ∷ "border" ∶ "1px solid #4ade80"
  ∷ color' (hex "#4ade80")
  ∷ "font-weight" ∶ "500"
  ∷ []

-- Input container (dark theme)
inputBox : Style
inputBox =
    "margin-bottom" ∶ "16px"
  ∷ padding' (px 12)
  ∷ backgroundColor' (hex "#0f0f23")
  ∷ borderRadius' (px 6)
  ∷ "border" ∶ "1px solid #30363d"
  ∷ color' (hex "#eee")
  ∷ []

-- Code block (dark theme)
codeBlock : Style
codeBlock =
    "background" ∶ "#0d1117"
  ∷ padding' (px 12)
  ∷ borderRadius' (px 6)
  ∷ "font-family" ∶ "monospace"
  ∷ "overflow-x" ∶ "auto"
  ∷ "border" ∶ "1px solid #30363d"
  ∷ color' (hex "#c9d1d9")
  ∷ []

------------------------------------------------------------------------
-- Theme variables (dark theme compatible with common.css)
-- Also override agdelte-controls variables for dark theme
------------------------------------------------------------------------

themeVars : Style
themeVars =
  -- Demo vars
    cssVar "demo-primary"   "#4a9eff"
  ∷ cssVar "demo-secondary" "#4ade80"
  ∷ cssVar "demo-warning"   "#fbbf24"
  ∷ cssVar "demo-error"     "#e94560"
  ∷ cssVar "demo-text"      "#eee"
  ∷ cssVar "demo-muted"     "#aaa"
  ∷ cssVar "demo-bg"        "#16213e"
  ∷ cssVar "demo-border"    "#30363d"
  -- Override agdelte-controls for dark theme
  ∷ cssVar "agdelte-bg"           "#16213e"
  ∷ cssVar "agdelte-bg-hover"     "#1a2744"
  ∷ cssVar "agdelte-bg-active"    "#1e2d4d"
  ∷ cssVar "agdelte-text"         "#eee"
  ∷ cssVar "agdelte-text-muted"   "#aaa"
  ∷ cssVar "agdelte-border"       "#30363d"
  ∷ cssVar "agdelte-primary"      "#4a9eff"
  ∷ cssVar "agdelte-primary-hover" "#3a8eef"
  ∷ cssVar "agdelte-success"      "#4ade80"
  ∷ cssVar "agdelte-warning"      "#fbbf24"
  ∷ cssVar "agdelte-error"        "#e94560"
  ∷ []

------------------------------------------------------------------------
-- Layout components
------------------------------------------------------------------------

-- Horizontal toolbar
toolbar : Style
toolbar = row <> center <> (gap' (px 12) ∷ [])

-- Sidebar layout
sidebar : Style
sidebar = col <> spaceBetween

-- Responsive card grid
cardGrid : Style
cardGrid = grid "repeat(auto-fill, minmax(280px, 1fr))" <> (gap' (rem 1.0) ∷ [])

-- Page layout
page : Style
page = stack (rem 2.0) <> (maxWidth' (px 960) ∷ margin2 zero (pct 50.0) ∷ [])

------------------------------------------------------------------------
-- Card component (dark theme)
------------------------------------------------------------------------

card : Style
card =
    padding' (rem 1.0)
  ∷ backgroundColor' (hex "#16213e")
  ∷ borderRadius' (px 8)
  ∷ "border" ∶ "1px solid #30363d"
  ∷ color' (hex "#eee")
  ∷ transition' (trans "box-shadow" (ms 200) ease ∷ trans "transform" (ms 200) easeOut ∷ [])
  ∷ []

cardHover : Style
cardHover =
    "box-shadow" ∶ "0 4px 12px rgba(0,0,0,0.4)"
  ∷ "transform" ∶ "translateY(-2px)"
  ∷ []

------------------------------------------------------------------------
-- Combined stylesheet
------------------------------------------------------------------------

examplesCSS : Stylesheet
examplesCSS =
  -- Theme
    rule ":root" themeVars
  -- Containers
  ∷ rule ".demo-container" demoContainer
  ∷ rule ".tab-content" tabContent
  ∷ rule ".demo-section" demoSection
  -- Buttons
  ∷ rule ".demo-btn" btn
  ∷ rule ".demo-btn.info" btnInfo
  ∷ rule ".demo-btn.success" btnSuccess
  ∷ rule ".demo-btn.warning" btnWarning
  ∷ rule ".demo-btn.error" btnError
  ∷ rule ".btn-group" btnGroup
  -- Display
  ∷ rule ".display-box" displayBox
  ∷ rule ".input-box" inputBox
  ∷ rule ".code-block" codeBlock
  -- Layout
  ∷ rule ".toolbar" toolbar
  ∷ rule ".sidebar" sidebar
  ∷ rule ".card-grid" cardGrid
  ∷ rule ".page" page
  -- Card
  ∷ rule ".card" card
  ∷ rule ".card:hover" cardHover
  -- Animations
  ∷ keyframe "fadeIn"    (("from" , "opacity" ∶ "0" ∷ []) ∷ ("to" , "opacity" ∶ "1" ∷ []) ∷ [])
  ∷ keyframe "fadeOut"   (("from" , "opacity" ∶ "1" ∷ []) ∷ ("to" , "opacity" ∶ "0" ∷ []) ∷ [])
  ∷ keyframe "slideInUp" (("from" , "transform" ∶ "translateY(20px)" ∷ "opacity" ∶ "0" ∷ [])
                        ∷ ("to"   , "transform" ∶ "translateY(0)" ∷ "opacity" ∶ "1" ∷ []) ∷ [])
  ∷ keyframe "pulse"     (("from" , "transform" ∶ "scale(1)" ∷ [])
                        ∷ ("50%"  , "transform" ∶ "scale(1.05)" ∷ [])
                        ∷ ("to"   , "transform" ∶ "scale(1)" ∷ []) ∷ [])
  -- Animation classes
  ∷ rule ".fade-in" ("animation" ∶ "fadeIn 300ms ease" ∷ [])
  ∷ rule ".fade-out" ("animation" ∶ "fadeOut 300ms ease" ∷ [])
  ∷ rule ".slide-in" ("animation" ∶ "slideInUp 300ms ease" ∷ [])
  -- Responsive
  ∷ media "(max-width: 768px)" (
        rule ".card" (padding' (px 8) ∷ [])
      ∷ rule ".demo-container" (padding' (px 8) ∷ [])
      ∷ [])
  -- DataGrid/Table dark theme overrides
  ∷ rule ".agdelte-grid" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-grid__cell" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-grid__header" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-table" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-table th" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-table td" (color' (var "agdelte-text") ∷ [])
  ∷ rule ".agdelte-table__row--selected" (backgroundColor' (hex "#1e3a5f") ∷ [])
  -- Dropdown dark theme override
  ∷ rule ".agdelte-dropdown__trigger" (color' (var "agdelte-text") ∷ [])
  -- Aliases (backwards compat)
  ∷ rule ".controls-demo" demoContainer
  ∷ rule ".toast-buttons" btnGroup
  ∷ rule ".selected-display" displayBox
  ∷ rule ".timeout-input" inputBox
  ∷ []
