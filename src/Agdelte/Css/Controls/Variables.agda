{-# OPTIONS --without-K #-}

-- CSS styles for control theming variables
-- (defines :root dark theme defaults and light theme overrides)

module Agdelte.Css.Controls.Variables where

open import Data.List using (List; []; _∷_; _++_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Variables using (cssVar)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Dark theme defaults (:root)
------------------------------------------------------------------------

darkThemeVars : Style
darkThemeVars =
  -- Colors
    cssVar "agdelte-primary"       "#4a9eff"
  ∷ cssVar "agdelte-primary-hover" "#3a8eef"
  ∷ cssVar "agdelte-success"       "#4ade80"
  ∷ cssVar "agdelte-warning"       "#fbbf24"
  ∷ cssVar "agdelte-warning-text"  "#1f2937"
  ∷ cssVar "agdelte-error"         "#e94560"
  ∷ cssVar "agdelte-info"          "#4a9eff"
  -- Background
  ∷ cssVar "agdelte-bg"            "#16213e"
  ∷ cssVar "agdelte-bg-hover"      "#1a2744"
  ∷ cssVar "agdelte-bg-active"     "#1e2d4d"
  ∷ cssVar "agdelte-backdrop"      "rgba(0, 0, 0, 0.6)"
  -- Text
  ∷ cssVar "agdelte-text"          "#eee"
  ∷ cssVar "agdelte-text-muted"    "#aaa"
  ∷ cssVar "agdelte-text-light"    "#ffffff"
  -- Border
  ∷ cssVar "agdelte-border"        "#30363d"
  ∷ cssVar "agdelte-border-radius" "6px"
  -- Spacing
  ∷ cssVar "agdelte-spacing-xs"    "4px"
  ∷ cssVar "agdelte-spacing-sm"    "8px"
  ∷ cssVar "agdelte-spacing-md"    "16px"
  ∷ cssVar "agdelte-spacing-lg"    "24px"
  -- Shadow
  ∷ cssVar "agdelte-shadow"        "0 4px 6px -1px rgba(0, 0, 0, 0.3), 0 2px 4px -1px rgba(0, 0, 0, 0.2)"
  ∷ cssVar "agdelte-shadow-lg"     "0 10px 15px -3px rgba(0, 0, 0, 0.3), 0 4px 6px -2px rgba(0, 0, 0, 0.2)"
  -- Tooltip
  ∷ cssVar "agdelte-tooltip-bg"    "#1a1a2e"
  ∷ cssVar "agdelte-tooltip-text"  "#fff"
  -- Z-index scale
  ∷ cssVar "agdelte-z-dropdown"    "100"
  ∷ cssVar "agdelte-z-tooltip"     "500"
  ∷ cssVar "agdelte-z-popover"     "600"
  ∷ cssVar "agdelte-z-modal"       "1000"
  ∷ cssVar "agdelte-z-toast"       "2000"
  -- Transitions
  ∷ cssVar "agdelte-transition"    "150ms ease-in-out"
  ∷ []

------------------------------------------------------------------------
-- Light theme overrides
------------------------------------------------------------------------

lightThemeVars : Style
lightThemeVars =
    cssVar "agdelte-primary"       "#3b82f6"
  ∷ cssVar "agdelte-primary-hover" "#2563eb"
  ∷ cssVar "agdelte-success"       "#10b981"
  ∷ cssVar "agdelte-warning"       "#f59e0b"
  ∷ cssVar "agdelte-warning-text"  "#1f2937"
  ∷ cssVar "agdelte-error"         "#ef4444"
  ∷ cssVar "agdelte-info"          "#3b82f6"
  ∷ cssVar "agdelte-bg"            "#ffffff"
  ∷ cssVar "agdelte-bg-hover"      "#f3f4f6"
  ∷ cssVar "agdelte-bg-active"     "#e5e7eb"
  ∷ cssVar "agdelte-backdrop"      "rgba(0, 0, 0, 0.5)"
  ∷ cssVar "agdelte-text"          "#1f2937"
  ∷ cssVar "agdelte-text-muted"    "#6b7280"
  ∷ cssVar "agdelte-border"        "#d1d5db"
  ∷ cssVar "agdelte-shadow"        "0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06)"
  ∷ cssVar "agdelte-shadow-lg"     "0 10px 15px -3px rgba(0, 0, 0, 0.1), 0 4px 6px -2px rgba(0, 0, 0, 0.05)"
  ∷ cssVar "agdelte-tooltip-bg"    "#333"
  ∷ cssVar "agdelte-tooltip-text"  "#fff"
  ∷ []

------------------------------------------------------------------------
-- Combined rules
------------------------------------------------------------------------

variablesRules : Stylesheet
variablesRules =
    rule ":root" darkThemeVars
  ∷ rule "[data-theme=\"light\"]" lightThemeVars
  ∷ []
