{-# OPTIONS --without-K #-}

-- Common styles for Agdelte examples
-- Provides consistent look across all demos
--
-- This module absorbs examples_html/common.css into Agda.
-- Generated via: npm run build:styles && npm run css:examples

module Styles where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_; _<>_)
open import Agdelte.Css.Length using (px; rem; pct; vh; zero; auto)
open import Agdelte.Css.Color using (hex; named; var)
open import Agdelte.Css.Properties using (padding'; padding2; margin'; margin2; margin4;
                                          backgroundColor'; color'; fontSize';
                                          borderRadius'; gap'; maxWidth'; maxHeight';
                                          width'; height'; minWidth'; minHeight';
                                          lineHeight'; background')
open import Agdelte.Css.Layout using (row; col; center; wrap; spaceBetween; grid; stack)
open import Agdelte.Css.Variables using (cssVar; varRef)
open import Agdelte.Css.Transition using (trans; transition')
open import Agdelte.Css.Easing using (ease; easeOut; ms; s)
open import Agdelte.Css.Animation using (anim; animation')
open import Agdelte.Css.Animate using (fadeIn; fadeOut; slideInUp; pulse; shake; spin)
open import Agdelte.Css.Stylesheet using (Rule; rule; variant; media; keyframe; rawRule; Stylesheet)

------------------------------------------------------------------------
-- Section separator for readability in generated CSS
------------------------------------------------------------------------

sep : String → Rule
sep label = rawRule ("/* " ++ˢ label ++ˢ " */")

------------------------------------------------------------------------
-- 2.1  :root variables (from common.css lines 4-42)
------------------------------------------------------------------------

rootVars : Style
rootVars =
  -- Example theme colors
    cssVar "primary"        "#4a9eff"
  ∷ cssVar "primary-hover"  "#3a8eef"
  ∷ cssVar "bg"             "#1a1a2e"
  ∷ cssVar "card"           "#16213e"
  ∷ cssVar "text"           "#eee"
  ∷ cssVar "accent"         "#e94560"
  ∷ cssVar "accent-hover"   "#d13550"
  ∷ cssVar "success"        "#4ade80"
  ∷ cssVar "muted"          "#888"
  ∷ cssVar "muted-light"    "#aaa"
  ∷ cssVar "muted-dark"     "#666"
  ∷ cssVar "disabled"       "#555"
  ∷ cssVar "border"         "#30363d"
  -- Override agdelte-controls.css defaults to match example theme
  ∷ cssVar "agdelte-primary"       "var(--primary)"
  ∷ cssVar "agdelte-primary-hover" "var(--primary-hover)"
  ∷ cssVar "agdelte-bg"            "var(--card)"
  ∷ cssVar "agdelte-bg-hover"      "#1a2744"
  ∷ cssVar "agdelte-bg-active"     "#1e2d4d"
  ∷ cssVar "agdelte-text"          "var(--text)"
  ∷ cssVar "agdelte-text-muted"    "var(--muted-light)"
  ∷ cssVar "agdelte-text-light"    "#ffffff"
  ∷ cssVar "agdelte-border"        "var(--border)"
  ∷ cssVar "agdelte-success"       "var(--success)"
  ∷ cssVar "agdelte-warning"       "#fbbf24"
  ∷ cssVar "agdelte-error"         "var(--accent)"
  ∷ cssVar "agdelte-info"          "var(--primary)"
  -- Code blocks
  ∷ cssVar "code-bg"        "#0d1117"
  ∷ cssVar "code-text"      "#c9d1d9"
  -- Preview area (intentionally light for CSS previews)
  ∷ cssVar "preview-bg"     "#f8f9fa"
  ∷ cssVar "preview-text"   "#333"
  ∷ []

rootVarsRules : Stylesheet
rootVarsRules =
    rawRule "/* Note: Uses color-mix(in srgb, ...) \x2014 requires Chrome 111+, Firefox 113+, Safari 16.2+. */"
  ∷ rawRule "/* Agdelte Examples - Common Styles (generated from Agda) */"
  ∷ rule ":root" rootVars
  ∷ []

------------------------------------------------------------------------
-- 2.2  Base styles (from common.css lines 44-154)
------------------------------------------------------------------------

-- 2.2.1  Reset + focus-visible
resetRules : Stylesheet
resetRules =
    rule "*"
      ( "box-sizing" ∶ "border-box"
      ∷ margin' zero
      ∷ padding' zero
      ∷ [])
  ∷ rule ":focus-visible"
      ( "outline" ∶ "2px solid var(--primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ []

-- 2.2.2  body
bodyRules : Stylesheet
bodyRules =
    rule "body"
      ( "font-family" ∶ "-apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif"
      ∷ "background" ∶ "var(--bg)"
      ∷ color' (var "text")
      ∷ minHeight' (vh 100.0)
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "align-items" ∶ "center"
      ∷ padding' (rem 2.0)
      ∷ [])
  ∷ []

-- 2.2.3  .back link + responsive
backLinkRules : Stylesheet
backLinkRules =
    rule ".back"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "1rem"
      ∷ "left" ∶ "1rem"
      ∷ "color" ∶ "var(--primary)"
      ∷ "text-decoration" ∶ "none"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".back:hover"
      ( "text-decoration" ∶ "underline"
      ∷ [])
  ∷ media "(max-width: 400px)"
      ( rule ".back"
          ( "position" ∶ "static"
          ∷ "margin-bottom" ∶ "0.5rem"
          ∷ [])
      ∷ [])
  ∷ []

-- 2.2.4  header, main, header > h1, .subtitle
headerRules : Stylesheet
headerRules =
    rule "header"
      ( "text-align" ∶ "center"
      ∷ [])
  ∷ rule "main"
      ( "width" ∶ "100%"
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule "header > h1"
      ( fontSize' (rem 2.5)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ "background" ∶ "linear-gradient(135deg, var(--primary), var(--accent))"
      ∷ "-webkit-background-clip" ∶ "text"
      ∷ "background-clip" ∶ "text"
      ∷ "color" ∶ "transparent"
      ∷ [])
  ∷ rule ".subtitle"
      ( "color" ∶ "var(--muted)"
      ∷ "margin-bottom" ∶ "2rem"
      ∷ [])
  ∷ []

-- 2.2.5  .instructions
instructionsRules : Stylesheet
instructionsRules =
    rule ".instructions"
      ( maxWidth' (px 600)
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ "padding" ∶ "1rem 1.5rem"
      ∷ "background" ∶ "color-mix(in srgb, var(--primary) 8%, transparent)"
      ∷ "border-left" ∶ "3px solid var(--primary)"
      ∷ "border-radius" ∶ "0 8px 8px 0"
      ∷ "color" ∶ "var(--muted-light)"
      ∷ fontSize' (rem 0.9)
      ∷ lineHeight' (rem 1.5)
      ∷ [])
  ∷ rule ".instructions code"
      ( "background" ∶ "rgba(0,0,0,0.3)"
      ∷ "padding" ∶ "0.1rem 0.4rem"
      ∷ borderRadius' (px 3)
      ∷ fontSize' (rem 0.85)
      ∷ [])
  ∷ []

-- 2.2.6  #app container
appRules : Stylesheet
appRules =
    rule "#app"
      ( "background" ∶ "var(--card)"
      ∷ borderRadius' (px 12)
      ∷ padding' (rem 2.0)
      ∷ "width" ∶ "100%"
      ∷ maxWidth' (px 600)
      ∷ "box-shadow" ∶ "0 10px 40px rgba(0,0,0,0.3)"
      ∷ [])
  ∷ []

-- 2.2.7  .btn
btnBaseRules : Stylesheet
btnBaseRules =
    rule ".btn"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.75rem 1.5rem"
      ∷ fontSize' (rem 1.25)
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ [])
  ∷ rule ".btn:hover"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".btn:active"
      ( "transform" ∶ "translateY(0)"
      ∷ [])
  ∷ []

-- 2.2.8  .info, .error, .loading
infoErrorRules : Stylesheet
infoErrorRules =
    rule ".info"
      ( "margin-top" ∶ "2rem"
      ∷ "text-align" ∶ "center"
      ∷ "color" ∶ "var(--muted-dark)"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".info code"
      ( "background" ∶ "rgba(255,255,255,0.1)"
      ∷ "padding" ∶ "0.2rem 0.5rem"
      ∷ borderRadius' (px 4)
      ∷ "font-family" ∶ "monospace"
      ∷ [])
  ∷ rule ".error"
      ( "background" ∶ "color-mix(in srgb, var(--accent) 20%, transparent)"
      ∷ "border" ∶ "1px solid var(--accent)"
      ∷ padding' (rem 1.0)
      ∷ borderRadius' (px 8)
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".error pre"
      ( "margin-top" ∶ "0.5rem"
      ∷ fontSize' (rem 0.85)
      ∷ "overflow-x" ∶ "auto"
      ∷ [])
  ∷ rule ".loading"
      ( "color" ∶ "var(--muted)"
      ∷ "font-style" ∶ "italic"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 2.3  Demo-specific styles (from common.css lines 160-239)
------------------------------------------------------------------------

-- 2.3.1  [data-agdelte] > div
agdelteWrapperRules : Stylesheet
agdelteWrapperRules =
    rule "[data-agdelte] > div"
      ( "text-align" ∶ "center"
      ∷ [])
  ∷ rule "[data-agdelte] > div h1"
      ( fontSize' (rem 1.5)
      ∷ "margin-bottom" ∶ "1rem"
      ∷ "background" ∶ "none"
      ∷ color' (var "text")
      ∷ [])
  ∷ rule "[data-agdelte] > div p"
      ( "color" ∶ "var(--muted-light)"
      ∷ "margin-bottom" ∶ "0.75rem"
      ∷ [])
  ∷ []

-- 2.3.2  .display (counter, timer)
displayRules : Stylesheet
displayRules =
    rule ".demo .display, .counter .display, .timer .display"
      ( fontSize' (rem 3.0)
      ∷ "font-weight" ∶ "bold"
      ∷ "margin" ∶ "1.5rem 0"
      ∷ "color" ∶ "var(--primary)"
      ∷ [])
  ∷ rule ".counter .display"
      ( "font-size" ∶ "4rem"
      ∷ "margin" ∶ "1rem 0"
      ∷ [])
  ∷ rule ".timer .display"
      ( "font-family" ∶ "'SF Mono', 'Fira Code', 'Cascadia Code', Monaco, 'Courier New', monospace"
      ∷ [])
  ∷ []

-- 2.3.3  .controls, .buttons (button row)
controlsButtonsRules : Stylesheet
controlsButtonsRules =
    rule ".demo .controls, .demo .buttons, .counter .buttons, .timer .controls"
      ( "display" ∶ "flex"
      ∷ gap' (rem 1.0)
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".timer .btn"
      ( minWidth' (px 100)
      ∷ [])
  ∷ []

-- 2.3.4  .status block
statusRules : Stylesheet
statusRules =
    rule ".demo .status, .http-demo .status, .task-demo .status, .ws-demo .status"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ padding' (rem 1.0)
      ∷ borderRadius' (px 8)
      ∷ "font-family" ∶ "monospace"
      ∷ fontSize' (rem 0.85)
      ∷ "overflow-wrap" ∶ "break-word"
      ∷ maxHeight' (px 250)
      ∷ "overflow-y" ∶ "auto"
      ∷ "margin" ∶ "1rem 0"
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".demo .status pre, .task-demo .status pre"
      ( "white-space" ∶ "pre-wrap"
      ∷ margin' zero
      ∷ [])
  ∷ []

-- 2.3.5  .action-btn
actionBtnRules : Stylesheet
actionBtnRules =
    rule ".demo .action-btn, .http-demo .fetch-btn, .task-demo .fetch-btn, .ws-demo button, .router-demo button"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.75rem 1.5rem"
      ∷ fontSize' (rem 1.0)
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ [])
  ∷ rule ".demo .action-btn:hover:not(:disabled), .http-demo .fetch-btn:hover:not(:disabled), .task-demo .fetch-btn:hover:not(:disabled), .ws-demo button:hover:not(:disabled)"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".demo .action-btn:disabled, .http-demo .fetch-btn:disabled, .task-demo .fetch-btn:disabled, .ws-demo button:disabled"
      ( "background" ∶ "var(--disabled)"
      ∷ "cursor" ∶ "not-allowed"
      ∷ [])
  ∷ rule ".demo .action-btn.danger, .ws-demo .disconnect-btn"
      ( "background" ∶ "var(--accent)"
      ∷ [])
  ∷ rule ".demo .action-btn.danger:hover:not(:disabled), .ws-demo .disconnect-btn:hover:not(:disabled)"
      ( "background" ∶ "var(--accent-hover)"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 2.4  CSS / Anim Demo styles (from common.css lines 245-386)
------------------------------------------------------------------------

-- 2.4.1  .demo-grid, .demo-section
demoGridRules : Stylesheet
demoGridRules =
    rule ".demo-grid"
      ( "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "repeat(auto-fill, minmax(280px, 1fr))"
      ∷ "gap" ∶ "1.5rem"
      ∷ maxWidth' (px 900)
      ∷ "width" ∶ "100%"
      ∷ "margin-top" ∶ "1rem"
      ∷ [])
  ∷ rule ".demo-section"
      ( "background" ∶ "var(--card)"
      ∷ borderRadius' (px 12)
      ∷ "padding" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".demo-section h3"
      ( "color" ∶ "var(--primary)"
      ∷ "margin-bottom" ∶ "0.75rem"
      ∷ fontSize' (rem 1.0)
      ∷ [])
  ∷ rule ".demo-section pre"
      ( "background" ∶ "var(--code-bg)"
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 6)
      ∷ padding' (rem 1.0)
      ∷ "overflow-x" ∶ "auto"
      ∷ fontSize' (rem 0.8)
      ∷ lineHeight' (rem 1.4)
      ∷ "color" ∶ "var(--code-text)"
      ∷ [])
  ∷ rule ".demo-section .label"
      ( "display" ∶ "inline-block"
      ∷ "background" ∶ "color-mix(in srgb, var(--primary) 15%, transparent)"
      ∷ "color" ∶ "var(--primary)"
      ∷ "padding" ∶ "0.2rem 0.6rem"
      ∷ borderRadius' (px 4)
      ∷ fontSize' (rem 0.75)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ [])
  ∷ []

-- 2.4.2  .css-output, .full-css, .preview-box, .preview-area
cssOutputRules : Stylesheet
cssOutputRules =
    rule ".css-output"
      ( maxWidth' (px 700)
      ∷ "width" ∶ "100%"
      ∷ "margin-top" ∶ "1rem"
      ∷ [])
  ∷ rule ".css-output pre, .full-css pre"
      ( "background" ∶ "var(--code-bg)"
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "1.5rem"
      ∷ "overflow-x" ∶ "auto"
      ∷ fontSize' (rem 0.85)
      ∷ lineHeight' (rem 1.5)
      ∷ "color" ∶ "var(--code-text)"
      ∷ [])
  ∷ rule ".full-css"
      ( maxWidth' (px 900)
      ∷ "width" ∶ "100%"
      ∷ "margin-top" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".full-css pre"
      ( maxHeight' (px 500)
      ∷ [])
  ∷ rule ".preview-box"
      ( maxWidth' (px 900)
      ∷ "width" ∶ "100%"
      ∷ "margin-top" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".preview-box h3"
      ( "color" ∶ "var(--primary)"
      ∷ "margin-bottom" ∶ "0.75rem"
      ∷ [])
  ∷ rule ".preview-area"
      ( borderRadius' (px 8)
      ∷ padding' (rem 2.0)
      ∷ "background" ∶ "var(--preview-bg)"
      ∷ "color" ∶ "var(--preview-text)"
      ∷ [])
  ∷ rule ".preview-area button"
      ( "padding" ∶ "0.4rem 1rem"
      ∷ "border" ∶ "1px solid #ccc"
      ∷ borderRadius' (px 4)
      ∷ "background" ∶ "#fff"
      ∷ "color" ∶ "var(--preview-text)"
      ∷ "cursor" ∶ "pointer"
      ∷ [])
  ∷ []

-- 2.4.3  Data tables (AnimDemo)
dataTableRules : Stylesheet
dataTableRules =
    rule ".demo-section table"
      ( "width" ∶ "100%"
      ∷ "border-collapse" ∶ "collapse"
      ∷ fontSize' (rem 0.85)
      ∷ [])
  ∷ rule ".demo-section th"
      ( "text-align" ∶ "left"
      ∷ "color" ∶ "var(--muted)"
      ∷ "font-weight" ∶ "500"
      ∷ "padding" ∶ "0.4rem 0.5rem"
      ∷ "border-bottom" ∶ "1px solid var(--border)"
      ∷ [])
  ∷ rule ".demo-section td"
      ( "padding" ∶ "0.4rem 0.5rem"
      ∷ "border-bottom" ∶ "1px solid rgba(48, 54, 61, 0.5)"
      ∷ [])
  ∷ rule ".demo-section td.val"
      ( "font-family" ∶ "'SF Mono', 'Fira Code', 'Cascadia Code', Monaco, 'Courier New', monospace"
      ∷ "color" ∶ "var(--success)"
      ∷ [])
  ∷ rule ".demo-section td.pass"
      ( "color" ∶ "var(--success)"
      ∷ [])
  ∷ rule ".demo-section td.fail"
      ( "color" ∶ "var(--accent)"
      ∷ [])
  ∷ []

-- 2.4.4  Bar chart visualization (AnimDemo)
barChartRules : Stylesheet
barChartRules =
    rule ".bar-chart"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "0.5rem"
      ∷ [])
  ∷ rule ".bar-row"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "0.75rem"
      ∷ [])
  ∷ rule ".bar-label"
      ( width' (px 120)
      ∷ fontSize' (rem 0.8)
      ∷ "color" ∶ "var(--muted-light)"
      ∷ "text-align" ∶ "right"
      ∷ [])
  ∷ rule ".bar"
      ( height' (px 24)
      ∷ borderRadius' (px 4)
      ∷ minWidth' (px 2)
      ∷ [])
  ∷ rule ".bar-value"
      ( fontSize' (rem 0.8)
      ∷ "color" ∶ "var(--muted)"
      ∷ "font-family" ∶ "monospace"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 2.5  Stress-test styles (from common.css lines 392-461)
------------------------------------------------------------------------

stressTestRules : Stylesheet
stressTestRules =
    rule ".stress-test"
      ( maxWidth' (px 700)
      ∷ "margin" ∶ "0 auto"
      ∷ [])
  ∷ rule ".stress-test .subtitle"
      ( "color" ∶ "var(--muted)"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".stress-test .controls"
      ( "display" ∶ "flex"
      ∷ gap' (px 8)
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".stress-test .controls button"
      ( "padding" ∶ "12px 28px"
      ∷ "border" ∶ "none"
      ∷ borderRadius' (px 6)
      ∷ "font-size" ∶ "15px"
      ∷ "font-weight" ∶ "600"
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s"
      ∷ [])
  ∷ rule ".stress-test .controls button:hover"
      ( "transform" ∶ "scale(1.05)"
      ∷ [])
  ∷ rule ".stress-test .controls button:nth-child(1)"
      ( "background" ∶ "var(--success)"
      ∷ "color" ∶ "var(--bg)"
      ∷ [])
  ∷ rule ".stress-test .controls button:nth-child(2)"
      ( "background" ∶ "var(--accent)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".stress-test .controls button:nth-child(3)"
      ( "background" ∶ "var(--muted-dark)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".stress-test .stats"
      ( "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "repeat(3, 1fr)"
      ∷ gap' (rem 1.0)
      ∷ "margin-bottom" ∶ "2rem"
      ∷ [])
  ∷ rule ".stress-test .stat"
      ( "background" ∶ "color-mix(in srgb, var(--primary) 8%, transparent)"
      ∷ "border" ∶ "1px solid color-mix(in srgb, var(--primary) 20%, transparent)"
      ∷ borderRadius' (px 10)
      ∷ padding' (rem 1.0)
      ∷ "text-align" ∶ "center"
      ∷ [])
  ∷ rule ".stress-test .stat-main"
      ( "background" ∶ "color-mix(in srgb, var(--success) 10%, transparent)"
      ∷ "border-color" ∶ "color-mix(in srgb, var(--success) 40%, transparent)"
      ∷ [])
  ∷ rule ".stress-test .stat-label"
      ( "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.75)
      ∷ "text-transform" ∶ "uppercase"
      ∷ "letter-spacing" ∶ "1px"
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ [])
  ∷ rule ".stress-test .stat-value"
      ( fontSize' (rem 1.3)
      ∷ "font-weight" ∶ "700"
      ∷ color' (var "text")
      ∷ "font-family" ∶ "monospace"
      ∷ minHeight' (rem 2.4)
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".stress-test .stat .stat-fps"
      ( "color" ∶ "var(--primary)"
      ∷ fontSize' (rem 2.2)
      ∷ [])
  ∷ rule ".stress-test .stat-highlight"
      ( "background" ∶ "color-mix(in srgb, var(--accent) 10%, transparent)"
      ∷ "border-color" ∶ "color-mix(in srgb, var(--accent) 40%, transparent)"
      ∷ [])
  ∷ rule ".stress-test .stat .stat-ops"
      ( "color" ∶ "var(--accent)"
      ∷ fontSize' (rem 2.2)
      ∷ [])
  ∷ rule ".stress-test .stat .stat-peak"
      ( "color" ∶ "#fbbf24"
      ∷ [])
  ∷ rule ".stress-test .bindings-section"
      ( "margin-bottom" ∶ "2rem"
      ∷ [])
  ∷ rule ".stress-test .bindings-section h2"
      ( fontSize' (rem 1.0)
      ∷ "color" ∶ "var(--muted)"
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".stress-test .binding-row"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "12px"
      ∷ "margin-bottom" ∶ "6px"
      ∷ "padding" ∶ "6px 12px"
      ∷ "background" ∶ "rgba(255,255,255,0.03)"
      ∷ borderRadius' (px 6)
      ∷ height' (px 36)
      ∷ [])
  ∷ rule ".stress-test .binding-label"
      ( "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.85)
      ∷ width' (px 60)
      ∷ "font-family" ∶ "monospace"
      ∷ [])
  ∷ rule ".stress-test .binding-val"
      ( "color" ∶ "var(--primary)"
      ∷ fontSize' (rem 1.1)
      ∷ width' (px 30)
      ∷ "text-align" ∶ "right"
      ∷ "font-family" ∶ "monospace"
      ∷ "font-weight" ∶ "700"
      ∷ [])
  ∷ rule ".stress-test .binding-bar"
      ( "color" ∶ "var(--primary)"
      ∷ "font-family" ∶ "monospace"
      ∷ fontSize' (rem 1.1)
      ∷ "letter-spacing" ∶ "1px"
      ∷ width' (px 200)
      ∷ "overflow" ∶ "hidden"
      ∷ "white-space" ∶ "nowrap"
      ∷ [])
  ∷ rule ".stress-test .explanation"
      ( "color" ∶ "var(--disabled)"
      ∷ fontSize' (rem 0.85)
      ∷ lineHeight' (rem 1.6)
      ∷ [])
  ∷ rule ".stress-test .explanation p"
      ( "margin-bottom" ∶ "0.3rem"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 2.7  Doc block (from common.css lines 464-522)
------------------------------------------------------------------------

docRules : Stylesheet
docRules =
    rule ".doc"
      ( maxWidth' (px 700)
      ∷ "margin" ∶ "2rem auto"
      ∷ padding' (rem 2.0)
      ∷ "background" ∶ "rgba(255,255,255,0.03)"
      ∷ borderRadius' (px 12)
      ∷ "border" ∶ "1px solid rgba(255,255,255,0.08)"
      ∷ lineHeight' (rem 1.7)
      ∷ "color" ∶ "var(--muted-light)"
      ∷ [])
  ∷ rule ".doc h2"
      ( "color" ∶ "var(--primary)"
      ∷ fontSize' (rem 1.1)
      ∷ "margin-top" ∶ "1.8rem"
      ∷ "margin-bottom" ∶ "0.6rem"
      ∷ [])
  ∷ rule ".doc h2:first-child"
      ( "margin-top" ∶ "0"
      ∷ [])
  ∷ rule ".doc p"
      ( "margin-bottom" ∶ "0.8rem"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".doc ol, .doc ul"
      ( "margin" ∶ "0.5rem 0 1rem 1.5rem"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".doc li"
      ( "margin-bottom" ∶ "0.4rem"
      ∷ [])
  ∷ rule ".doc code"
      ( "background" ∶ "color-mix(in srgb, var(--primary) 12%, transparent)"
      ∷ "padding" ∶ "1px 5px"
      ∷ borderRadius' (px 3)
      ∷ fontSize' (rem 0.85)
      ∷ "color" ∶ "#8cc8ff"
      ∷ [])
  ∷ rule ".doc pre"
      ( "background" ∶ "rgba(0,0,0,0.4)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "1rem 1.2rem"
      ∷ "overflow-x" ∶ "auto"
      ∷ "margin" ∶ "1rem 0"
      ∷ [])
  ∷ rule ".doc pre code"
      ( "background" ∶ "none"
      ∷ padding' zero
      ∷ "color" ∶ "#ccc"
      ∷ fontSize' (rem 0.82)
      ∷ lineHeight' (rem 1.5)
      ∷ [])
  ∷ rule ".doc table"
      ( "width" ∶ "100%"
      ∷ "border-collapse" ∶ "collapse"
      ∷ "margin" ∶ "1rem 0"
      ∷ fontSize' (rem 0.85)
      ∷ [])
  ∷ rule ".doc th"
      ( "text-align" ∶ "left"
      ∷ "padding" ∶ "8px 12px"
      ∷ "background" ∶ "color-mix(in srgb, var(--primary) 10%, transparent)"
      ∷ "color" ∶ "var(--primary)"
      ∷ "border-bottom" ∶ "1px solid color-mix(in srgb, var(--primary) 20%, transparent)"
      ∷ [])
  ∷ rule ".doc td"
      ( "padding" ∶ "8px 12px"
      ∷ "border-bottom" ∶ "1px solid rgba(255,255,255,0.05)"
      ∷ [])
  ∷ rule ".doc strong"
      ( color' (var "text")
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 2.6  WebGL styles (from common.css lines 528-554)
------------------------------------------------------------------------

webglRules : Stylesheet
webglRules =
    rule ".webgl-demo"
      ( "text-align" ∶ "center"
      ∷ padding' (rem 2.0)
      ∷ [])
  ∷ rule ".webgl-demo canvas"
      ( "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 8)
      ∷ "margin" ∶ "1rem 0"
      ∷ "display" ∶ "block"
      ∷ "margin-left" ∶ "auto"
      ∷ "margin-right" ∶ "auto"
      ∷ [])
  ∷ rule ".webgl-demo .controls"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "0.75rem"
      ∷ "justify-content" ∶ "center"
      ∷ "margin" ∶ "1rem 0"
      ∷ "position" ∶ "relative"
      ∷ "z-index" ∶ "1"
      ∷ [])
  ∷ rule ".webgl-demo .controls button"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.5rem 1rem"
      ∷ borderRadius' (px 6)
      ∷ "cursor" ∶ "pointer"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".webgl-demo .controls button:hover"
      ( "background" ∶ "var(--primary-hover)"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Container styles (original Styles.agda)
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
demoSectionStyle : Style
demoSectionStyle =
    "margin-bottom" ∶ "16px"
  ∷ []

------------------------------------------------------------------------
-- Button styles (original Styles.agda)
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

-- Button variants (override-only — base properties come from .demo-btn)
btnInfo : Style
btnInfo = backgroundColor' (var "agdelte-primary") ∷ color' (named "white") ∷ []

btnSuccess : Style
btnSuccess = backgroundColor' (hex "#4ade80") ∷ color' (hex "#1a1a2e") ∷ []

btnWarning : Style
btnWarning = backgroundColor' (hex "#fbbf24") ∷ color' (hex "#1a1a2e") ∷ []

btnError : Style
btnError = backgroundColor' (hex "#e94560") ∷ color' (named "white") ∷ []

-- Button group
btnGroup : Style
btnGroup = row ++ wrap ++ (gap' (px 8) ∷ [])

------------------------------------------------------------------------
-- Display styles (original Styles.agda)
------------------------------------------------------------------------

-- Selected/result display box (dark theme)
displayBox : Style
displayBox =
    "margin-top" ∶ "16px"
  ∷ padding' (px 12)
  ∷ "background" ∶ "color-mix(in srgb, var(--agdelte-success) 15%, var(--agdelte-bg))"
  ∷ borderRadius' (px 6)
  ∷ "border" ∶ "1px solid var(--agdelte-success)"
  ∷ color' (var "agdelte-success")
  ∷ "font-weight" ∶ "500"
  ∷ []

-- Input container (dark theme)
inputBox : Style
inputBox =
    "margin-bottom" ∶ "16px"
  ∷ padding' (px 12)
  ∷ backgroundColor' (var "agdelte-bg")
  ∷ borderRadius' (px 6)
  ∷ "border" ∶ "1px solid var(--agdelte-border)"
  ∷ color' (var "agdelte-text")
  ∷ []

-- Code block (dark theme)
codeBlock : Style
codeBlock =
    "background" ∶ "var(--agdelte-bg)"
  ∷ padding' (px 12)
  ∷ borderRadius' (px 6)
  ∷ "font-family" ∶ "monospace"
  ∷ "overflow-x" ∶ "auto"
  ∷ "border" ∶ "1px solid var(--agdelte-border)"
  ∷ color' (hex "#c9d1d9")
  ∷ []

------------------------------------------------------------------------
-- Theme variables (dark theme compatible with common.css)
-- Also override agdelte-controls variables for dark theme
------------------------------------------------------------------------

themeVars : Style
themeVars =
  -- Override agdelte-controls for dark theme
    cssVar "agdelte-bg"           "#16213e"
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
page = stack (rem 2.0) <> (maxWidth' (px 960) ∷ margin2 zero auto ∷ [])

------------------------------------------------------------------------
-- Card component (dark theme)
------------------------------------------------------------------------

card : Style
card =
    padding' (rem 1.0)
  ∷ backgroundColor' (var "agdelte-bg")
  ∷ borderRadius' (px 8)
  ∷ "border" ∶ "1px solid var(--agdelte-border)"
  ∷ color' (var "agdelte-text")
  ∷ transition' (trans "box-shadow" (ms 200) ease ∷ trans "transform" (ms 200) easeOut ∷ [])
  ∷ []

cardHover : Style
cardHover =
    "box-shadow" ∶ "0 4px 12px rgba(0,0,0,0.4)"
  ∷ "transform" ∶ "translateY(-2px)"
  ∷ []

------------------------------------------------------------------------
-- 3.1  WebSocket demo (demo-styles.css lines 4-76)
------------------------------------------------------------------------

wsMessagesRules : Stylesheet
wsMessagesRules =
    rule ".demo .messages, .ws-demo .messages"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ borderRadius' (px 8)
      ∷ padding' (rem 1.0)
      ∷ maxHeight' (px 300)
      ∷ "overflow-y" ∶ "auto"
      ∷ "list-style" ∶ "none"
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ gap' (rem 0.5)
      ∷ [])
  ∷ rule ".ws-demo .message"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "padding" ∶ "0.5rem 0.75rem"
      ∷ borderRadius' (px 12)
      ∷ fontSize' (rem 0.9)
      ∷ "max-width" ∶ "80%"
      ∷ [])
  ∷ rule ".ws-demo .message .label"
      ( fontSize' (rem 0.7)
      ∷ "font-weight" ∶ "600"
      ∷ "margin-bottom" ∶ "0.25rem"
      ∷ "text-transform" ∶ "uppercase"
      ∷ "letter-spacing" ∶ "0.5px"
      ∷ [])
  ∷ rule ".ws-demo .message .text" ("word-break" ∶ "break-word" ∷ [])
  ∷ rule ".ws-demo .message.sent"
      ( "align-self" ∶ "flex-end"
      ∷ "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border-bottom-right-radius" ∶ "4px"
      ∷ [])
  ∷ rule ".ws-demo .message.sent .label" ("color" ∶ "rgba(255,255,255,0.7)" ∷ "text-align" ∶ "right" ∷ [])
  ∷ rule ".ws-demo .message.received"
      ( "align-self" ∶ "flex-start"
      ∷ "background" ∶ "color-mix(in srgb, var(--success) 20%, transparent)"
      ∷ "color" ∶ "var(--success)"
      ∷ "border-bottom-left-radius" ∶ "4px"
      ∷ [])
  ∷ rule ".ws-demo .message.received .label" ("color" ∶ "color-mix(in srgb, var(--success) 70%, transparent)" ∷ [])
  ∷ rule ".ws-demo .input-section" ("display" ∶ "flex" ∷ "gap" ∶ "0.5rem" ∷ "margin-bottom" ∶ "1rem" ∷ [])
  ∷ rule ".ws-demo .messages-section h3" ("color" ∶ "var(--muted)" ∷ fontSize' (rem 0.9) ∷ "margin-bottom" ∶ "0.5rem" ∷ [])
  ∷ []

wsStatusRules : Stylesheet
wsStatusRules =
    rule ".demo .connection-status, .ws-demo .status"
      ( "padding" ∶ "0.5rem 1rem"
      ∷ borderRadius' (px 8)
      ∷ "margin-bottom" ∶ "1rem"
      ∷ "font-weight" ∶ "600"
      ∷ [])
  ∷ rule ".ws-demo .status.disconnected" ("background" ∶ "rgba(150,150,150,0.2)" ∷ "color" ∶ "var(--muted)" ∷ [])
  ∷ rule ".ws-demo .status.connecting" ("background" ∶ "color-mix(in srgb, var(--agdelte-warning) 20%, transparent)" ∷ "color" ∶ "var(--agdelte-warning)" ∷ [])
  ∷ rule ".ws-demo .status.connected" ("background" ∶ "color-mix(in srgb, var(--success) 20%, transparent)" ∷ "color" ∶ "var(--success)" ∷ [])
  ∷ rule ".ws-demo .status.error" ("background" ∶ "color-mix(in srgb, var(--accent) 20%, transparent)" ∷ "color" ∶ "var(--accent)" ∷ [])
  ∷ []

wsInputRules : Stylesheet
wsInputRules =
    rule ".demo input[type=\"text\"]"
      ( "flex" ∶ "1"
      ∷ "padding" ∶ "0.5rem"
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 6)
      ∷ "background" ∶ "var(--bg)"
      ∷ "color" ∶ "var(--text)"
      ∷ fontSize' (rem 0.9)
      ∷ [])
  ∷ rule ".demo input[type=\"text\"]:focus"
      ( "border-color" ∶ "var(--primary)"
      ∷ [])
  ∷ rule ".demo input[type=\"text\"]:focus-visible"
      ( "outline" ∶ "2px solid var(--primary)"
      ∷ "outline-offset" ∶ "-2px"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.2  Counters (composition, optic) (demo-styles.css lines 78-145)
------------------------------------------------------------------------

countersRules : Stylesheet
countersRules =
    rule ".demo .counters-container, .composition-demo .counters-container, .optic-demo .counters-container"
      ( "display" ∶ "flex"
      ∷ gap' (rem 2.0)
      ∷ [])
  ∷ rule ".composition-demo .counters-container, .optic-demo .counters-container"
      ( "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".demo .counter-component, .composition-demo .counter-component, .optic-demo .counter-component"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ borderRadius' (px 8)
      ∷ padding' (rem 1.5)
      ∷ [])
  ∷ rule ".demo .counter-component"
      ( "flex" ∶ "1"
      ∷ "text-align" ∶ "center"
      ∷ [])
  ∷ rule ".demo .counter-component h3"
      ( "color" ∶ "var(--primary)"
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".demo .count"
      ( fontSize' (rem 2.0)
      ∷ "font-weight" ∶ "bold"
      ∷ minWidth' (px 60)
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".demo .round-btn, .composition-demo .btn"
      ( width' (px 40)
      ∷ height' (px 40)
      ∷ "border-radius" ∶ "50%"
      ∷ "border" ∶ "none"
      ∷ "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ fontSize' (rem 1.5)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ "display" ∶ "inline-flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ padding' zero
      ∷ lineHeight' (rem 1.0)
      ∷ [])
  ∷ rule ".demo .round-btn:hover, .composition-demo .btn:hover"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "scale(1.1)"
      ∷ [])
  ∷ rule ".composition-demo .description, .optic-demo .description" ("color" ∶ "var(--muted)" ∷ "margin-bottom" ∶ "0.5rem" ∷ [])
  ∷ rule ".composition-demo .total, .optic-demo .total" ("color" ∶ "var(--success)" ∷ fontSize' (rem 1.2) ∷ "font-weight" ∶ "600" ∷ "margin-bottom" ∶ "1.5rem" ∷ [])
  ∷ rule ".composition-demo .counter-controls, .optic-demo .counter-controls" ("display" ∶ "flex" ∷ "align-items" ∶ "center" ∷ "justify-content" ∶ "center" ∷ "gap" ∶ "0.75rem" ∷ "flex-wrap" ∶ "wrap" ∷ [])
  ∷ rule ".composition-demo .reset-btn, .optic-demo .reset-btn"
      ( "background" ∶ "var(--accent)"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "padding" ∶ "0.5rem 1rem"
      ∷ borderRadius' (px 6)
      ∷ "cursor" ∶ "pointer"
      ∷ fontSize' (rem 0.85)
      ∷ "flex-basis" ∶ "100%"
      ∷ [])
  ∷ rule ".composition-demo .reset-btn:hover, .optic-demo .reset-btn:hover" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.3  Router demo (demo-styles.css lines 147-187)
------------------------------------------------------------------------

routerRules : Stylesheet
routerRules =
    rule ".router-demo" ("width" ∶ "clamp(320px, 25vw, 480px)" ∷ [])
  ∷ rule ".router-demo .stats" ("color" ∶ "var(--muted)" ∷ "margin-bottom" ∶ "1rem" ∷ [])
  ∷ rule ".router-demo .main-nav"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "4px"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ "background" ∶ "rgba(0,0,0,0.3)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "4px"
      ∷ [])
  ∷ rule ".router-demo .nav-link"
      ( "flex" ∶ "1"
      ∷ "text-align" ∶ "center"
      ∷ "padding" ∶ "0.6rem 1rem"
      ∷ "color" ∶ "var(--muted)"
      ∷ "text-decoration" ∶ "none"
      ∷ borderRadius' (px 6)
      ∷ "transition" ∶ "all 0.2s"
      ∷ [])
  ∷ rule ".router-demo .nav-link:hover"
      ( "color" ∶ "var(--primary)"
      ∷ "background" ∶ "color-mix(in srgb, var(--primary) 15%, transparent)"
      ∷ [])
  ∷ rule ".router-demo .nav-link.active"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".router-demo .content" (minHeight' (px 120) ∷ [])
  ∷ rule ".router-demo .page h2" ("color" ∶ "var(--primary)" ∷ "margin-bottom" ∶ "1rem" ∷ [])
  ∷ rule ".router-demo .page p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.5rem" ∷ [])
  ∷ rule ".router-demo .not-found h2" ("color" ∶ "var(--accent)" ∷ [])
  ∷ rule ".router-demo .not-found button"
      ( "margin-top" ∶ "1rem"
      ∷ "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.5rem 1rem"
      ∷ borderRadius' (px 6)
      ∷ "cursor" ∶ "pointer"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.4  Keyboard demo (demo-styles.css lines 189-223)
------------------------------------------------------------------------

keyboardRules : Stylesheet
keyboardRules =
    rule ".keyboard-demo"
      ( "position" ∶ "relative"
      ∷ "width" ∶ "100%"
      ∷ height' (px 400)
      ∷ [])
  ∷ rule ".keyboard-demo p" ("margin-bottom" ∶ "0.5rem" ∷ "color" ∶ "var(--muted-light)" ∷ [])
  ∷ rule ".keyboard-demo .box"
      ( "background" ∶ "var(--primary)"
      ∷ borderRadius' (px 8)
      ∷ "box-shadow" ∶ "0 4px 15px color-mix(in srgb, var(--primary) 40%, transparent)"
      ∷ [])
  ∷ rule ".keyboard-demo .instructions"
      ( "position" ∶ "absolute"
      ∷ "bottom" ∶ "1rem"
      ∷ "left" ∶ "1rem"
      ∷ fontSize' (rem 0.85)
      ∷ "color" ∶ "var(--muted-dark)"
      ∷ [])
  ∷ rule ".keyboard-demo .reset-btn"
      ( "position" ∶ "absolute"
      ∷ "bottom" ∶ "1rem"
      ∷ "right" ∶ "1rem"
      ∷ "background" ∶ "var(--accent)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.5rem 1rem"
      ∷ borderRadius' (px 6)
      ∷ "cursor" ∶ "pointer"
      ∷ [])
  ∷ rule ".keyboard-demo .reset-btn:hover" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ rule "body:has(.keyboard-demo) #app" (minHeight' (px 450) ∷ [])
  ∷ media "(min-width: 500px)"
      ( rule "body:has(.keyboard-demo) #app" (minWidth' (px 500) ∷ [])
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.5  Todo demo (demo-styles.css lines 225-291)
------------------------------------------------------------------------

todoRules : Stylesheet
todoRules =
    rule ".todo-app" (maxWidth' (px 500) ∷ "margin" ∶ "0 auto" ∷ "text-align" ∶ "left" ∷ [])
  ∷ rule ".todo-app h1"
      ( "text-align" ∶ "center"
      ∷ "font-size" ∶ "80px"
      ∷ "font-weight" ∶ "200"
      ∷ "background" ∶ "none"
      ∷ "color" ∶ "var(--accent)"
      ∷ [])
  ∷ rule ".todo-app .input-section" ("display" ∶ "flex" ∷ "gap" ∶ "8px" ∷ "margin-bottom" ∶ "16px" ∷ [])
  ∷ rule ".todo-list"
      ( "list-style" ∶ "none"
      ∷ padding' zero
      ∷ margin' zero
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 4)
      ∷ [])
  ∷ rule ".todo-item"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ padding' (px 12)
      ∷ "border-bottom" ∶ "1px solid var(--border)"
      ∷ [])
  ∷ rule ".todo-item:last-child" ("border-bottom" ∶ "none" ∷ [])
  ∷ rule ".todo-item input[type=\"checkbox\"]" ("width" ∶ "20px" ∷ "height" ∶ "20px" ∷ "margin-right" ∶ "12px" ∷ "cursor" ∶ "pointer" ∷ [])
  ∷ rule ".todo-item span" ("flex" ∶ "1" ∷ [])
  ∷ rule ".todo-app .delete-btn"
      ( "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "var(--accent)"
      ∷ "font-size" ∶ "24px"
      ∷ "cursor" ∶ "pointer"
      ∷ "padding" ∶ "0 8px"
      ∷ "opacity" ∶ "0.5"
      ∷ "transition" ∶ "opacity 0.2s"
      ∷ [])
  ∷ rule ".todo-app .delete-btn:hover" ("opacity" ∶ "1" ∷ [])
  ∷ rule ".todo-app .footer"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ padding' (px 12)
      ∷ "color" ∶ "var(--muted)"
      ∷ "font-size" ∶ "14px"
      ∷ [])
  ∷ rule ".todo-app .footer button" ("background" ∶ "none" ∷ "border" ∶ "none" ∷ "color" ∶ "var(--accent)" ∷ "cursor" ∶ "pointer" ∷ [])
  ∷ rule ".todo-app .footer button:hover" ("text-decoration" ∶ "underline" ∷ [])
  ∷ rule ".todo-app input[type=\"text\"]"
      ( "flex" ∶ "1"
      ∷ padding' (px 12)
      ∷ "font-size" ∶ "16px"
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ borderRadius' (px 4)
      ∷ "background" ∶ "var(--bg)"
      ∷ "color" ∶ "var(--text)"
      ∷ [])
  ∷ rule ".todo-app input[type=\"text\"]:focus" ("border-color" ∶ "var(--primary)" ∷ [])
  ∷ rule ".todo-app input[type=\"text\"]:focus-visible" ("outline" ∶ "2px solid var(--primary)" ∷ "outline-offset" ∶ "-2px" ∷ [])
  ∷ rule ".todo-app > .input-section button"
      ( "padding" ∶ "12px 24px"
      ∷ "background" ∶ "var(--accent)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ borderRadius' (px 4)
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "16px"
      ∷ [])
  ∷ rule ".todo-app > .input-section button:hover" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.6  Transitions demo (demo-styles.css lines 293-353)
------------------------------------------------------------------------

transitionsRules : Stylesheet
transitionsRules =
    rule ".transitions-demo .section" ("margin" ∶ "1.5rem 0" ∷ [])
  ∷ rule ".transitions-demo .section .btn" ("margin-bottom" ∶ "1rem" ∷ [])
  ∷ rule ".transitions-demo .panel"
      ( "background" ∶ "color-mix(in srgb, var(--primary) 10%, transparent)"
      ∷ "border" ∶ "1px solid color-mix(in srgb, var(--primary) 30%, transparent)"
      ∷ borderRadius' (px 8)
      ∷ padding' (rem 1.5)
      ∷ "text-align" ∶ "left"
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".transitions-demo .panel h3" ("color" ∶ "var(--primary)" ∷ "margin-bottom" ∶ "0.75rem" ∷ [])
  ∷ rule ".transitions-demo .panel p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.5rem" ∷ fontSize' (rem 0.9) ∷ [])
  ∷ rule ".transitions-demo .notification"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ gap' (rem 1.0)
      ∷ "background" ∶ "color-mix(in srgb, var(--success) 15%, transparent)"
      ∷ "border" ∶ "1px solid color-mix(in srgb, var(--success) 30%, transparent)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "1rem 1.25rem"
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".transitions-demo .notif-text" ("flex" ∶ "1" ∷ "color" ∶ "var(--success)" ∷ [])
  ∷ rule ".transitions-demo .dismiss-btn"
      ( "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 1.25)
      ∷ "cursor" ∶ "pointer"
      ∷ "padding" ∶ "0 0.25rem"
      ∷ [])
  ∷ rule ".transitions-demo .dismiss-btn:hover" ("color" ∶ "var(--text)" ∷ [])
  ∷ rule ".transitions-demo .btn.notif-btn" ("background" ∶ "var(--success)" ∷ [])
  ∷ rule ".transitions-demo .btn.notif-btn:hover" ("background" ∶ "color-mix(in srgb, var(--success) 80%, black)" ∷ [])
  ∷ rule ".transitions-demo .counter-text" ("color" ∶ "var(--muted-dark)" ∷ fontSize' (rem 0.85) ∷ [])
  ∷ rule ".transitions-demo .description" ("color" ∶ "var(--muted)" ∷ "margin-bottom" ∶ "1rem" ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.7  Combinators demo (demo-styles.css lines 355-414)
------------------------------------------------------------------------

combinatorsRules : Stylesheet
combinatorsRules =
    rule ".combinators-demo .description" ("color" ∶ "var(--muted)" ∷ "margin-bottom" ∶ "1.5rem" ∷ [])
  ∷ rule ".combinators-demo .controls"
      ( "display" ∶ "flex"
      ∷ gap' (rem 1.0)
      ∷ "justify-content" ∶ "center"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".combinators-demo .btn.reset-btn" ("background" ∶ "var(--accent)" ∷ [])
  ∷ rule ".combinators-demo .btn.reset-btn:hover" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ rule ".combinators-demo .stats"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "1.5rem"
      ∷ "justify-content" ∶ "center"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".combinators-demo .stat"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "1rem 1.5rem"
      ∷ "text-align" ∶ "center"
      ∷ minWidth' (px 120)
      ∷ [])
  ∷ rule ".combinators-demo .stat-label"
      ( "display" ∶ "block"
      ∷ "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.8)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ [])
  ∷ rule ".combinators-demo .stat-value"
      ( "display" ∶ "block"
      ∷ fontSize' (rem 2.0)
      ∷ "font-weight" ∶ "bold"
      ∷ "color" ∶ "var(--primary)"
      ∷ [])
  ∷ rule ".combinators-demo .batch-stat .stat-value" ("color" ∶ "var(--success)" ∷ [])
  ∷ rule ".combinators-demo .batch-value" ("color" ∶ "var(--success)" ∷ [])
  ∷ rule ".combinators-demo .explanation"
      ( "background" ∶ "rgba(0,0,0,0.15)"
      ∷ borderRadius' (px 8)
      ∷ padding' (rem 1.0)
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".combinators-demo .explanation p"
      ( "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.85)
      ∷ "font-family" ∶ "monospace"
      ∷ "margin-bottom" ∶ "0.3rem"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.8  OpticDynamic demo (demo-styles.css lines 416-530)
------------------------------------------------------------------------

opticDynamicRules : Stylesheet
opticDynamicRules =
    rule ".optic-dynamic-demo"
      ( "text-align" ∶ "center"
      ∷ maxWidth' (px 600)
      ∷ "margin" ∶ "0 auto"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .info-panel"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ "border-radius" ∶ "10px"
      ∷ "padding" ∶ "1rem 1.5rem"
      ∷ "margin" ∶ "1rem 0"
      ∷ "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-around"
      ∷ gap' (rem 1.0)
      ∷ "flex-wrap" ∶ "wrap"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .info-panel p"
      ( fontSize' (rem 0.9)
      ∷ "color" ∶ "var(--muted-light)"
      ∷ [])
  ∷ rule ".optic-dynamic-demo p.total"
      ( "color" ∶ "var(--primary)"
      ∷ "font-weight" ∶ "bold"
      ∷ fontSize' (rem 1.1)
      ∷ [])
  ∷ rule ".optic-dynamic-demo p.selected-info"
      ( "color" ∶ "var(--accent)"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .controls"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "0.5rem"
      ∷ "justify-content" ∶ "center"
      ∷ "flex-wrap" ∶ "wrap"
      ∷ "margin" ∶ "1rem 0"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .add-btn" ("background" ∶ "var(--success)" ∷ "color" ∶ "var(--bg)" ∷ [])
  ∷ rule ".optic-dynamic-demo .add-btn:hover" ("background" ∶ "color-mix(in srgb, var(--success) 80%, black)" ∷ [])
  ∷ rule ".optic-dynamic-demo .reset-btn" ("background" ∶ "var(--accent)" ∷ [])
  ∷ rule ".optic-dynamic-demo .reset-btn:hover" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ rule ".optic-dynamic-demo .items-list"
      ( "list-style" ∶ "none"
      ∷ padding' zero
      ∷ "margin" ∶ "1rem 0"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .item"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ "align-items" ∶ "center"
      ∷ "padding" ∶ "0.75rem 1rem"
      ∷ "margin" ∶ "0.25rem 0"
      ∷ "background" ∶ "rgba(255,255,255,0.05)"
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "background 0.15s, border-color 0.15s"
      ∷ "border" ∶ "2px solid transparent"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .item:hover" ("background" ∶ "rgba(255,255,255,0.1)" ∷ [])
  ∷ rule ".optic-dynamic-demo .item.selected"
      ( "background" ∶ "color-mix(in srgb, var(--primary) 15%, transparent)"
      ∷ "border-color" ∶ "var(--primary)"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .item-label" ("font-weight" ∶ "500" ∷ [])
  ∷ rule ".optic-dynamic-demo .item-value"
      ( fontSize' (rem 1.3)
      ∷ "font-weight" ∶ "bold"
      ∷ "color" ∶ "var(--primary)"
      ∷ "min-width" ∶ "3ch"
      ∷ "text-align" ∶ "right"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .explanation"
      ( "margin-top" ∶ "1.5rem"
      ∷ "background" ∶ "rgba(0,0,0,0.15)"
      ∷ borderRadius' (px 8)
      ∷ padding' (rem 1.0)
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".optic-dynamic-demo .explanation p"
      ( "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.85)
      ∷ "font-family" ∶ "monospace"
      ∷ "margin-bottom" ∶ "0.3rem"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.9  Worker demo (demo-styles.css lines 532-621)
------------------------------------------------------------------------

workerRules : Stylesheet
workerRules =
    rule ".worker-demo" ("text-align" ∶ "center" ∷ [])
  ∷ rule ".worker-demo h1"
      ( fontSize' (rem 1.5)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ "background" ∶ "none"
      ∷ "color" ∶ "var(--text)"
      ∷ [])
  ∷ rule ".worker-demo p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.75rem" ∷ [])
  ∷ rule ".worker-demo .controls"
      ( "display" ∶ "flex"
      ∷ gap' (rem 1.0)
      ∷ "justify-content" ∶ "center"
      ∷ "align-items" ∶ "center"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".worker-demo .controls button"
      ( width' (px 44)
      ∷ height' (px 44)
      ∷ "border-radius" ∶ "50%"
      ∷ "border" ∶ "none"
      ∷ "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ fontSize' (rem 1.5)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ "display" ∶ "inline-flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".worker-demo .controls button:hover"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "scale(1.1)"
      ∷ [])
  ∷ rule ".worker-demo .input-value"
      ( fontSize' (rem 2.0)
      ∷ "font-weight" ∶ "bold"
      ∷ "color" ∶ "var(--primary)"
      ∷ minWidth' (px 100)
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".worker-demo .compute-btn"
      ( "background" ∶ "var(--accent)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.85rem 2rem"
      ∷ fontSize' (rem 1.1)
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".worker-demo .compute-btn:hover:not(:disabled)"
      ( "background" ∶ "var(--accent-hover)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".worker-demo .compute-btn:disabled" ("background" ∶ "var(--disabled)" ∷ "cursor" ∶ "not-allowed" ∷ [])
  ∷ rule ".worker-demo .status"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ "padding" ∶ "1rem 1.5rem"
      ∷ borderRadius' (px 8)
      ∷ fontSize' (rem 1.1)
      ∷ "margin-bottom" ∶ "0.75rem"
      ∷ [])
  ∷ rule ".worker-demo .count" ("color" ∶ "var(--muted-dark)" ∷ fontSize' (rem 0.9) ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.10 Parallel demo (demo-styles.css lines 623-723)
------------------------------------------------------------------------

parallelRules : Stylesheet
parallelRules =
    rule ".parallel-demo" ("text-align" ∶ "center" ∷ [])
  ∷ rule ".parallel-demo h1"
      ( fontSize' (rem 1.5)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ "background" ∶ "none"
      ∷ "color" ∶ "var(--text)"
      ∷ [])
  ∷ rule ".parallel-demo p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.75rem" ∷ [])
  ∷ rule ".parallel-demo .nav"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "4px"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ "background" ∶ "rgba(0,0,0,0.3)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "4px"
      ∷ [])
  ∷ rule ".parallel-demo .nav button"
      ( "flex" ∶ "1"
      ∷ "padding" ∶ "0.6rem 1rem"
      ∷ "border" ∶ "none"
      ∷ borderRadius' (px 6)
      ∷ "background" ∶ "transparent"
      ∷ "color" ∶ "var(--muted)"
      ∷ fontSize' (rem 0.9)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "all 0.2s"
      ∷ [])
  ∷ rule ".parallel-demo .nav button:hover"
      ( "background" ∶ "color-mix(in srgb, var(--primary) 15%, transparent)"
      ∷ "color" ∶ "var(--primary)"
      ∷ [])
  ∷ rule ".parallel-demo .nav button.active"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "cursor" ∶ "default"
      ∷ [])
  ∷ rule ".parallel-demo .demo-section"
      ( "background" ∶ "rgba(0,0,0,0.15)"
      ∷ "border-radius" ∶ "10px"
      ∷ padding' (rem 1.5)
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".parallel-demo .demo-section h2"
      ( "color" ∶ "var(--primary)"
      ∷ fontSize' (rem 1.1)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ [])
  ∷ rule ".parallel-demo .demo-section p" ("margin-bottom" ∶ "0.5rem" ∷ [])
  ∷ rule ".parallel-demo .demo-section button"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.65rem 1.5rem"
      ∷ fontSize' (rem 0.95)
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ "margin" ∶ "0.25rem"
      ∷ [])
  ∷ rule ".parallel-demo .demo-section button:hover:not(:disabled)"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".parallel-demo .demo-section button:disabled" ("background" ∶ "var(--disabled)" ∷ "cursor" ∶ "not-allowed" ∷ [])
  ∷ rule ".parallel-demo .status"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ "padding" ∶ "0.75rem 1rem"
      ∷ borderRadius' (px 8)
      ∷ "font-family" ∶ "monospace"
      ∷ fontSize' (rem 0.9)
      ∷ "margin-top" ∶ "0.75rem"
      ∷ "text-align" ∶ "left"
      ∷ "overflow-wrap" ∶ "break-word"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.11 Remote Agent demo (demo-styles.css lines 725-793)
------------------------------------------------------------------------

remoteAgentRules : Stylesheet
remoteAgentRules =
    rule ".remote-agent-demo" ("text-align" ∶ "center" ∷ [])
  ∷ rule ".remote-agent-demo h1"
      ( fontSize' (rem 1.5)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ "background" ∶ "none"
      ∷ "color" ∶ "var(--text)"
      ∷ [])
  ∷ rule ".remote-agent-demo p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.75rem" ∷ [])
  ∷ rule ".remote-agent-demo .count"
      ( fontSize' (rem 2.5)
      ∷ "font-weight" ∶ "bold"
      ∷ "color" ∶ "var(--primary)"
      ∷ "margin" ∶ "1rem 0"
      ∷ [])
  ∷ rule ".remote-agent-demo .status"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ "padding" ∶ "0.75rem 1rem"
      ∷ borderRadius' (px 8)
      ∷ fontSize' (rem 0.95)
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ [])
  ∷ rule ".remote-agent-demo .controls"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "0.75rem"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".remote-agent-demo .controls button"
      ( "background" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "0.75rem 1.5rem"
      ∷ fontSize' (rem 1.0)
      ∷ borderRadius' (px 8)
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ [])
  ∷ rule ".remote-agent-demo .controls button:hover:not(:disabled)"
      ( "background" ∶ "var(--primary-hover)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".remote-agent-demo .controls button:disabled" ("background" ∶ "var(--disabled)" ∷ "cursor" ∶ "not-allowed" ∷ [])
  ∷ rule ".remote-agent-demo .controls .step-btn" ("background" ∶ "var(--accent)" ∷ [])
  ∷ rule ".remote-agent-demo .controls .step-btn:hover:not(:disabled)" ("background" ∶ "var(--accent-hover)" ∷ [])
  ∷ []

------------------------------------------------------------------------
-- 3.12 Session Form demo (demo-styles.css lines 795-921)
------------------------------------------------------------------------

sessionFormRules : Stylesheet
sessionFormRules =
    rule ".session-form" ("text-align" ∶ "center" ∷ [])
  ∷ rule ".session-form h1"
      ( fontSize' (rem 1.5)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ "background" ∶ "none"
      ∷ "color" ∶ "var(--text)"
      ∷ [])
  ∷ rule ".session-form p" ("color" ∶ "var(--muted-light)" ∷ "margin-bottom" ∶ "0.75rem" ∷ [])
  ∷ rule ".session-form .progress"
      ( "background" ∶ "rgba(0,0,0,0.2)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "0.6rem 1.2rem"
      ∷ "margin-bottom" ∶ "1.5rem"
      ∷ fontSize' (rem 0.9)
      ∷ "color" ∶ "var(--muted)"
      ∷ "letter-spacing" ∶ "0.5px"
      ∷ [])
  ∷ rule ".session-form .form-step"
      ( "background" ∶ "rgba(0,0,0,0.15)"
      ∷ "border-radius" ∶ "10px"
      ∷ padding' (rem 2.0)
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".session-form .prompt"
      ( fontSize' (rem 1.15)
      ∷ "color" ∶ "var(--primary)"
      ∷ "margin-bottom" ∶ "1rem"
      ∷ "font-weight" ∶ "500"
      ∷ [])
  ∷ rule ".session-form input"
      ( "width" ∶ "100%"
      ∷ "padding" ∶ "0.85rem 1rem"
      ∷ fontSize' (rem 1.1)
      ∷ "border" ∶ "2px solid var(--border)"
      ∷ borderRadius' (px 8)
      ∷ "background" ∶ "var(--bg)"
      ∷ "color" ∶ "var(--text)"
      ∷ "margin-bottom" ∶ "1.25rem"
      ∷ "transition" ∶ "border-color 0.2s"
      ∷ [])
  ∷ rule ".session-form input:focus" ("border-color" ∶ "var(--primary)" ∷ [])
  ∷ rule ".session-form input:focus-visible" ("outline" ∶ "2px solid var(--primary)" ∷ "outline-offset" ∶ "-2px" ∷ [])
  ∷ rule ".session-form input::placeholder" ("color" ∶ "var(--disabled)" ∷ [])
  ∷ rule ".session-form .actions"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "0.75rem"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".session-form .btn"
      ( "padding" ∶ "0.7rem 1.5rem"
      ∷ fontSize' (rem 1.0)
      ∷ borderRadius' (px 8)
      ∷ "border" ∶ "1px solid var(--border)"
      ∷ "background" ∶ "rgba(255,255,255,0.05)"
      ∷ "color" ∶ "var(--text)"
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform 0.1s, background 0.2s"
      ∷ [])
  ∷ rule ".session-form .btn:hover"
      ( "background" ∶ "rgba(255,255,255,0.1)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
  ∷ rule ".session-form .btn.primary"
      ( "background" ∶ "var(--primary)"
      ∷ "border-color" ∶ "var(--primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".session-form .btn.primary:hover" ("background" ∶ "var(--primary-hover)" ∷ [])
  ∷ rule ".session-form .confirm"
      ( "border" ∶ "1px solid color-mix(in srgb, var(--primary) 30%, transparent)"
      ∷ "background" ∶ "color-mix(in srgb, var(--primary) 5%, transparent)"
      ∷ [])
  ∷ rule ".session-form .done"
      ( "border" ∶ "1px solid color-mix(in srgb, var(--success) 30%, transparent)"
      ∷ "background" ∶ "color-mix(in srgb, var(--success) 5%, transparent)"
      ∷ [])
  ∷ rule ".session-form .summary"
      ( "text-align" ∶ "left"
      ∷ "background" ∶ "rgba(0,0,0,0.2)"
      ∷ borderRadius' (px 8)
      ∷ "padding" ∶ "1rem 1.25rem"
      ∷ "margin" ∶ "1rem 0"
      ∷ fontSize' (rem 0.95)
      ∷ lineHeight' (rem 1.8)
      ∷ "color" ∶ "var(--muted-light)"
      ∷ [])
  ∷ rule ".session-form .done h2"
      ( "color" ∶ "var(--success)"
      ∷ fontSize' (rem 1.3)
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Combined stylesheet
------------------------------------------------------------------------

examplesCSS : Stylesheet
examplesCSS =
  -- === common.css content ===
  rootVarsRules
  ++ resetRules
  ++ bodyRules
  ++ backLinkRules
  ++ headerRules
  ++ instructionsRules
  ++ appRules
  ++ btnBaseRules
  ++ infoErrorRules
  -- Demo-specific
  ++ (sep "Demo content wrappers" ∷ [])
  ++ agdelteWrapperRules
  ++ displayRules
  ++ controlsButtonsRules
  ++ statusRules
  ++ actionBtnRules
  -- CSS / Anim Demo
  ++ (sep "CSS / Anim Demo presentation" ∷ [])
  ++ demoGridRules
  ++ cssOutputRules
  ++ dataTableRules
  ++ barChartRules
  -- Stress test
  ++ (sep "Stress Test" ∷ [])
  ++ stressTestRules
  -- Doc block
  ++ (sep "Doc block" ∷ [])
  ++ docRules
  -- WebGL
  ++ (sep "WebGL Demos" ∷ [])
  ++ webglRules
  -- === demo-styles.css content ===
  ++ (sep "WebSocket demo" ∷ [])
  ++ wsMessagesRules
  ++ wsStatusRules
  ++ wsInputRules
  ++ (sep "Counters (composition, optic)" ∷ [])
  ++ countersRules
  ++ (sep "Router demo" ∷ [])
  ++ routerRules
  ++ (sep "Keyboard demo" ∷ [])
  ++ keyboardRules
  ++ (sep "Todo demo" ∷ [])
  ++ todoRules
  ++ (sep "Transitions demo" ∷ [])
  ++ transitionsRules
  ++ (sep "Combinators demo" ∷ [])
  ++ combinatorsRules
  ++ (sep "OpticDynamic demo" ∷ [])
  ++ opticDynamicRules
  ++ (sep "Worker demo" ∷ [])
  ++ workerRules
  ++ (sep "Parallel demo" ∷ [])
  ++ parallelRules
  ++ (sep "Remote Agent demo" ∷ [])
  ++ remoteAgentRules
  ++ (sep "Session Form demo" ∷ [])
  ++ sessionFormRules
  -- === Original examples.css content ===
  ++ (sep "Agda-generated example classes" ∷ [])
  -- Containers
  ++ ( rule ".demo-container" demoContainer
  ∷ rule ".tab-content" tabContent
  ∷ rule ".demo-section" demoSectionStyle
  -- Buttons (variant enforces base/override split)
  ∷ rule ".demo-btn" btn
  ∷ variant ".demo-btn" btn ".demo-btn.info" btnInfo
  ∷ variant ".demo-btn" btn ".demo-btn.success" btnSuccess
  ∷ variant ".demo-btn" btn ".demo-btn.warning" btnWarning
  ∷ variant ".demo-btn" btn ".demo-btn.error" btnError
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
  ∷ keyframe "slideInUpSubtle" (("from" , "transform" ∶ "translateY(20px)" ∷ "opacity" ∶ "0" ∷ [])
                              ∷ ("to"   , "transform" ∶ "translateY(0)" ∷ "opacity" ∶ "1" ∷ []) ∷ [])
  ∷ keyframe "pulse"     (("from" , "transform" ∶ "scale(1)" ∷ [])
                        ∷ ("50%"  , "transform" ∶ "scale(1.05)" ∷ [])
                        ∷ ("to"   , "transform" ∶ "scale(1)" ∷ []) ∷ [])
  -- Animation classes
  ∷ rule ".fade-in" ("animation" ∶ "fadeIn 300ms ease" ∷ [])
  ∷ rule ".fade-out" ("animation" ∶ "fadeOut 300ms ease" ∷ [])
  ∷ rule ".slide-in" ("animation" ∶ "slideInUpSubtle 300ms ease" ∷ [])
  -- Responsive
  ∷ media "(max-width: 768px)" (
        rule ".card" (padding' (px 8) ∷ [])
      ∷ rule ".demo-container" (padding' (px 8) ∷ [])
      ∷ [])
  -- Selected row highlight (not in agdelte-controls.css)
  ∷ rule ".agdelte-table__row--selected" ("background" ∶ "color-mix(in srgb, var(--agdelte-primary) 20%, var(--agdelte-bg))" ∷ [])
  -- Aliases (backwards compat)
  ∷ rule ".controls-demo" demoContainer
  ∷ rule ".toast-buttons" btnGroup
  ∷ rule ".selected-display" displayBox
  ∷ rule ".timeout-input" inputBox
  ∷ [])
