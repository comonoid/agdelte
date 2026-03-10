{-# OPTIONS --without-K #-}

-- CSS styles for the TabBar control
-- (HTML structure is in Agdelte.Html.Controls.TabBar)

module Agdelte.Css.Controls.TabBar where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- TabBar rules
------------------------------------------------------------------------

tabBarRules : Stylesheet
tabBarRules =
    rule ".agdelte-tabs"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ [])
  ∷ rule ".agdelte-tabs__header"
      ( "display" ∶ "flex"
      ∷ "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-tabs__tab"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "border-bottom" ∶ "2px solid transparent"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "inherit"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-tabs__tab:hover"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-tabs__tab--active"
      ( "color" ∶ "var(--agdelte-primary)"
      ∷ "border-bottom-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-tabs__content"
      ( "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ [])
  ∷ rule ".agdelte-tabs__panel"
      ( "animation" ∶ "agdelte-fade-in var(--agdelte-transition)"
      ∷ [])
  ∷ []
