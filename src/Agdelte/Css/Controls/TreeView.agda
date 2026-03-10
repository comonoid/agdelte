{-# OPTIONS --without-K #-}

-- CSS styles for the TreeView control
-- (HTML structure is in Agdelte.Html.Controls.TreeView)

module Agdelte.Css.Controls.TreeView where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- TreeView rules
------------------------------------------------------------------------

treeViewRules : Stylesheet
treeViewRules =
    rule ".agdelte-tree"
      ( "font-size" ∶ "inherit"
      ∷ [])
  ∷ rule ".agdelte-tree__node"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ [])
  ∷ rule ".agdelte-tree__header"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-tree__toggle"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "20px"
      ∷ "height" ∶ "20px"
      ∷ "padding" ∶ "0"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "font-size" ∶ "0.625rem"
      ∷ "transition" ∶ "transform var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-tree__toggle:hover"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-tree__toggle--open"
      ( "transform" ∶ "rotate(90deg)"
      ∷ [])
  ∷ rule ".agdelte-tree__spacer"
      ( "width" ∶ "20px"
      ∷ "height" ∶ "20px"
      ∷ [])
  ∷ rule ".agdelte-tree__label"
      ( "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "transition" ∶ "background var(--agdelte-transition)"
      ∷ "text-align" ∶ "left"
      ∷ "font-size" ∶ "inherit"
      ∷ [])
  ∷ rule ".agdelte-tree__label:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-tree__children"
      ( "margin-left" ∶ "var(--agdelte-spacing-md)"
      ∷ "border-left" ∶ "1px solid var(--agdelte-border)"
      ∷ "animation" ∶ "agdelte-slide-down var(--agdelte-transition)"
      ∷ [])
  ∷ []
