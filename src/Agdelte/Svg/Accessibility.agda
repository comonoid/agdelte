{-# OPTIONS --without-K #-}

-- SVG Accessibility Helpers
-- ARIA attributes and semantic wrappers

module Agdelte.Svg.Accessibility where

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Agdelte.Reactive.Node using (Node; Attr; attr; elem)
open import Agdelte.Svg.Elements using (svg; title'; desc')

------------------------------------------------------------------------
-- ARIA attributes
------------------------------------------------------------------------

role_ : ∀ {M Msg} → String → Attr M Msg
role_ = attr "role"

ariaLabel_ : ∀ {M Msg} → String → Attr M Msg
ariaLabel_ = attr "aria-label"

ariaLabelledby_ : ∀ {M Msg} → String → Attr M Msg
ariaLabelledby_ = attr "aria-labelledby"

ariaDescribedby_ : ∀ {M Msg} → String → Attr M Msg
ariaDescribedby_ = attr "aria-describedby"

ariaHidden_ : ∀ {M Msg} → String → Attr M Msg
ariaHidden_ = attr "aria-hidden"

focusable_ : ∀ {M Msg} → String → Attr M Msg
focusable_ = attr "focusable"

tabindex_ : ∀ {M Msg} → String → Attr M Msg
tabindex_ = attr "tabindex"

------------------------------------------------------------------------
-- Accessible SVG wrapper
------------------------------------------------------------------------

-- Accessible SVG with title and description
-- Screen readers will announce the title
accessibleSvg : ∀ {M Msg}
  → String                    -- title text
  → String                    -- description text
  → List (Attr M Msg)         -- additional attributes
  → List (Node M Msg)         -- content
  → Node M Msg
accessibleSvg titleText descText attrs content =
  svg ( role_ "img"
      ∷ ariaLabelledby_ "svg-title svg-desc"
      ∷ attrs)
    ( title' (attr "id" "svg-title" ∷ []) (text titleText ∷ [])
    ∷ desc' (attr "id" "svg-desc" ∷ []) (text descText ∷ [])
    ∷ content)
  where
    open import Agdelte.Reactive.Node using (text)

-- Decorative SVG (hidden from screen readers)
decorativeSvg : ∀ {M Msg}
  → List (Attr M Msg)
  → List (Node M Msg)
  → Node M Msg
decorativeSvg attrs content =
  svg ( ariaHidden_ "true"
      ∷ focusable_ "false"
      ∷ attrs)
    content

-- Semantic graphic with role
graphicSvg : ∀ {M Msg}
  → String                    -- accessible name (aria-label)
  → List (Attr M Msg)
  → List (Node M Msg)
  → Node M Msg
graphicSvg name attrs content =
  svg ( role_ "img"
      ∷ ariaLabel_ name
      ∷ attrs)
    content

------------------------------------------------------------------------
-- Interactive element helpers
------------------------------------------------------------------------

-- Button-like SVG element
svgButton : ∀ {M Msg}
  → String                    -- accessible name
  → Attr M Msg                -- click handler (on "click" msg)
  → List (Attr M Msg)         -- additional attributes
  → List (Node M Msg)         -- content
  → Node M Msg
svgButton name clickHandler attrs content =
  elem "g"
    ( role_ "button"
    ∷ ariaLabel_ name
    ∷ tabindex_ "0"
    ∷ clickHandler
    ∷ attrs)
    content

-- Link-like SVG element
svgLink : ∀ {M Msg}
  → String                    -- href
  → String                    -- accessible name
  → List (Attr M Msg)
  → List (Node M Msg)
  → Node M Msg
svgLink href name attrs content =
  elem "a"
    ( attr "href" href
    ∷ ariaLabel_ name
    ∷ attrs)
    content
