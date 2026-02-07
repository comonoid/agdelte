{-# OPTIONS --without-K #-}

-- CssFullDemo: end-to-end test for all CSS features
-- Covers: Decl, Types, Conditional, Variables,
--         Stylesheet, Layout, Animation, Generate

module CssFullDemo where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)

open import Agdelte.Css.Decl using (Decl; Style; _∶_; _<>_; none)
open import Agdelte.Css.Length using (Length; px; rem; em; pct; vh; vw; zero)
open import Agdelte.Css.Color using (Color; hex; rgba; rgb; hsl; named; var)
open import Agdelte.Css.Properties using (padding'; padding2; background'; backgroundColor';
                                           color'; fontSize'; borderRadius';
                                           width'; height'; maxWidth'; gap';
                                           margin'; margin2)
open import Agdelte.Css.Variables using (cssVar; varRef)
open import Agdelte.Css.Layout using (row; col; center; spaceBetween; wrap;
                                       grid; stack; inline)
open import Agdelte.Css.Easing using (Easing; ease; easeOut; easeInOut; cubicBezier;
                                       Duration; ms; s;
                                       linearFn; easeOutFn)
open import Agdelte.Css.Transition using (TransSpec; trans; transition')
open import Agdelte.Css.Animation using (Stop; from; to; at;
                                          Keyframes; mkKeyframes; keyframeRule;
                                          Animation; anim; mkAnim; animation'; animations;
                                          FillMode; forwards; fmNone;
                                          Direction; normal;
                                          IterCount; infinite; times;
                                          staggerDelay)
open import Agdelte.Css.Animate using (fadeIn; fadeOut; slideInUp; pulse; shake; spin)
open import Agdelte.Css.Conditional using (styleIf; styleWhen)
open import Agdelte.Css.Stylesheet using (Rule; rule; media; keyframe; rawRule;
                                           Stylesheet; renderStylesheet)

------------------------------------------------------------------------
-- CSS Variables
------------------------------------------------------------------------

-- Define theme variables (rendered as inline style on :root or container)
themeVars : Style
themeVars =
    cssVar "primary"   "#3b82f6"
  ∷ cssVar "secondary" "#10b981"
  ∷ cssVar "radius"    "8px"
  ∷ cssVar "gap"       "1rem"
  ∷ []

-- Reference variables in typed properties
themedCard : Style
themedCard =
    color' (named "white")
  ∷ backgroundColor' (var "primary")
  ∷ "border-radius" ∶ varRef "radius"
  ∷ "padding" ∶ varRef "gap"
  ∷ []

------------------------------------------------------------------------
-- Layout helpers
------------------------------------------------------------------------

-- Horizontal toolbar: flex row, centered, with gap
toolbar : Style
toolbar = row <> center <> (gap' (px 12) ∷ [])

-- Sidebar layout: column, space-between
sidebar : Style
sidebar = col <> spaceBetween

-- Responsive card grid
cardGrid : Style
cardGrid = grid "repeat(auto-fill, minmax(280px, 1fr))" <> (gap' (rem 1.0) ∷ [])

-- Vertical stack with wrapping
tagList : Style
tagList = inline (px 8) <> wrap

-- Page layout: centered column, max-width
page : Style
page = stack (rem 2.0) <> (maxWidth' (px 960) ∷ margin2 zero (pct 50.0) ∷ [])

------------------------------------------------------------------------
-- Conditional styles
------------------------------------------------------------------------

baseStyle : Style
baseStyle =
    padding' (rem 1.0)
  ∷ color' (hex "#333")
  ∷ []

activeStyle : Style
activeStyle =
    background' (hex "#e0f0ff")
  ∷ []

-- Conditional composition
cardStyle : Bool → Style
cardStyle isActive = baseStyle <> styleIf isActive activeStyle

-- Active card has 3 properties, inactive has 2
activeCard : Style
activeCard = cardStyle true

inactiveCard : Style
inactiveCard = cardStyle false

------------------------------------------------------------------------
-- Transitions & Animations
------------------------------------------------------------------------

-- Transition shorthand
hoverTransition : Decl
hoverTransition = transition' (
    trans "opacity" (ms 300) ease
  ∷ trans "transform" (ms 200) easeOut
  ∷ [])

-- Animation shorthand
fadeInAnim : Decl
fadeInAnim = animation' (anim "fadeIn" (ms 300))

-- Infinite pulse with easeInOut
pulseAnim : Decl
pulseAnim = animation' (mkAnim "pulse" (s 2.0) easeInOut (ms 0) infinite normal fmNone)

-- Multiple animations
multiAnim : Decl
multiAnim = animations (
    anim "fadeIn" (ms 300)
  ∷ anim "slideInUp" (ms 500)
  ∷ [])

-- Stagger delay for list items
delay0 : Decl
delay0 = staggerDelay 0 50

delay3 : Decl
delay3 = staggerDelay 3 50

------------------------------------------------------------------------
-- Full stylesheet using presets
------------------------------------------------------------------------

appCSS : Stylesheet
appCSS =
    -- Theme variables on :root
    rule ":root" themeVars
    -- Preset keyframes
  ∷ keyframeRule fadeIn
  ∷ keyframeRule fadeOut
  ∷ keyframeRule slideInUp
  ∷ keyframeRule pulse
  ∷ keyframeRule shake
  ∷ keyframeRule spin
    -- Layout rules
  ∷ rule ".toolbar" toolbar
  ∷ rule ".sidebar" sidebar
  ∷ rule ".card-grid" cardGrid
  ∷ rule ".page" page
    -- Card with typed properties
  ∷ rule ".card" (
        padding' (rem 1.0)
      ∷ background' (hex "#fff")
      ∷ borderRadius' (px 8)
      ∷ hoverTransition
      ∷ [])
  ∷ rule ".card:hover" (
        "box-shadow" ∶ "0 4px 12px rgba(0,0,0,0.15)"
      ∷ "transform" ∶ "translateY(-2px)"
      ∷ [])
    -- Themed card using variable references
  ∷ rule ".card--themed" themedCard
    -- Responsive
  ∷ media "(max-width: 768px)" (
        rule ".card" (
            padding' (px 8)
          ∷ [])
      ∷ rule ".card-grid" (
            grid "1fr")
      ∷ [])
    -- Enter/leave classes for whenT
  ∷ rule ".panel-enter" (
        animation' (anim "fadeIn" (ms 300))
      ∷ [])
  ∷ rule ".panel-leave" (
        animation' (anim "fadeOut" (ms 300))
      ∷ [])
    -- Spinner
  ∷ rule ".spinner" (
        animation' (mkAnim "spin" (s 1.0) ease (ms 0) infinite normal fmNone)
      ∷ [])
  ∷ []

-- Render to CSS string
cssOutput : String
cssOutput = renderStylesheet appCSS
