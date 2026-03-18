{-# OPTIONS --without-K #-}

-- CSS styles for the Sidebar control
-- (HTML structure is in Agdelte.Html.Controls.Sidebar)

module Agdelte.Css.Controls.Sidebar where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Sidebar rules
------------------------------------------------------------------------

sidebarRules : Stylesheet
sidebarRules =
    rule ".agdelte-sidebar"
      ( "--agdelte-sidebar-width" ∶ "240px"
      ∷ "--agdelte-sidebar-collapsed-offset" ∶ "180px"
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "width" ∶ "var(--agdelte-sidebar-width)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border-right" ∶ "1px solid var(--agdelte-border)"
      ∷ "transition" ∶ "transform var(--agdelte-transition), margin-right var(--agdelte-transition)"
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-sidebar--collapsed"
      ( "transform" ∶ "translateX(calc(-1 * var(--agdelte-sidebar-collapsed-offset)))"
      ∷ "margin-right" ∶ "calc(-1 * var(--agdelte-sidebar-collapsed-offset))"
      ∷ [])
  ∷ rule ".agdelte-sidebar__header"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__toggle"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "32px"
      ∷ "height" ∶ "32px"
      ∷ "padding" ∶ "0"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "transition" ∶ "background var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__toggle:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__toggle:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-sidebar__title"
      ( "white-space" ∶ "nowrap"
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-sidebar__nav"
      ( "list-style" ∶ "none"
      ∷ "margin" ∶ "0"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__item"
      ( "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__link"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "width" ∶ "100%"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "text-align" ∶ "left"
      ∷ "font-size" ∶ "inherit"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__link:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__link:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-sidebar__link--active"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__link--active:hover"
      ( "background" ∶ "var(--agdelte-primary-hover)"
      ∷ [])
  ∷ rule ".agdelte-sidebar__icon"
      ( "flex-shrink" ∶ "0"
      ∷ "font-size" ∶ "1.25rem"
      ∷ [])
  ∷ rule ".agdelte-sidebar__label"
      ( "white-space" ∶ "nowrap"
      ∷ "overflow" ∶ "hidden"
      ∷ "text-overflow" ∶ "ellipsis"
      ∷ [])
  ∷ rule ".agdelte-sidebar--collapsed .agdelte-sidebar__link"
      ( "justify-content" ∶ "center"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ []
