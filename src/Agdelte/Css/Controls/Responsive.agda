{-# OPTIONS --without-K #-}

-- CSS responsive breakpoints and reduced motion for controls

module Agdelte.Css.Controls.Responsive where

open import Data.List using (List; []; _∷_; _++_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; media; rawRule; Stylesheet)

------------------------------------------------------------------------
-- Reduced motion
------------------------------------------------------------------------

reducedMotionRules : Stylesheet
reducedMotionRules =
    media "(prefers-reduced-motion: reduce)"
      ( rule ".agdelte-tabs__panel, .agdelte-modal__backdrop, .agdelte-modal__content, .agdelte-dropdown__menu, .agdelte-toast, .agdelte-accordion__content, .agdelte-tree__children, .agdelte-popover__content, .agdelte-enter-fade, .agdelte-leave-fade, .agdelte-enter-scale, .agdelte-leave-scale, .agdelte-enter-slide-down, .agdelte-leave-slide-down"
          ( "animation" ∶ "none !important"
          ∷ [])
      ∷ rule ".agdelte-tabs__tab, .agdelte-modal__btn, .agdelte-dropdown__trigger, .agdelte-dropdown__option, .agdelte-accordion__header, .agdelte-accordion__icon, .agdelte-sidebar, .agdelte-sidebar__toggle, .agdelte-sidebar__link, .agdelte-breadcrumb__link, .agdelte-tree__toggle, .agdelte-tree__label, .agdelte-tooltip__content, .agdelte-progress__bar, .agdelte-stepper__number, .agdelte-stepper--clickable .agdelte-stepper__step, .agdelte-pagination__btn, .agdelte-pagination__page, .agdelte-datepicker__day, .agdelte-datepicker__nav, .agdelte-datepicker__year, .agdelte-datepicker__month, .agdelte-timepicker__btn, .agdelte-daterange__preset, .agdelte-grid__row, .agdelte-toast__close, .agdelte-slider__input::-webkit-slider-thumb"
          ( "transition" ∶ "none !important"
          ∷ [])
      ∷ rule ".agdelte-spinner"
          ( "animation-duration" ∶ "4s"
          ∷ [])
      ∷ rule ".agdelte-skeleton"
          ( "animation" ∶ "none"
          ∷ "opacity" ∶ "0.7"
          ∷ [])
      ∷ rule ".agdelte-progress--indeterminate .agdelte-progress__bar"
          ( "animation" ∶ "none"
          ∷ "width" ∶ "100%"
          ∷ [])
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Responsive breakpoints
------------------------------------------------------------------------

mobileBreakpointRules : Stylesheet
mobileBreakpointRules =
    media "(max-width: 640px)"
      ( rule ".agdelte-sidebar"
          ( "position" ∶ "fixed"
          ∷ "top" ∶ "0"
          ∷ "left" ∶ "0"
          ∷ "bottom" ∶ "0"
          ∷ "z-index" ∶ "var(--agdelte-z-modal)"
          ∷ [])
      ∷ rule ".agdelte-sidebar--collapsed"
          ( "transform" ∶ "translateX(calc(-1 * var(--agdelte-sidebar-width)))"
          ∷ [])
      ∷ rule ".agdelte-modal__content"
          ( "max-width" ∶ "100vw"
          ∷ "margin" ∶ "var(--agdelte-spacing-sm)"
          ∷ "border-radius" ∶ "var(--agdelte-spacing-sm)"
          ∷ [])
      ∷ rule ".agdelte-dropdown__menu"
          ( "max-height" ∶ "160px"
          ∷ [])
      ∷ rule ".agdelte-toast-container"
          ( "left" ∶ "var(--agdelte-spacing-sm)"
          ∷ "right" ∶ "var(--agdelte-spacing-sm)"
          ∷ [])
      ∷ rule ".agdelte-stepper"
          ( "flex-direction" ∶ "column"
          ∷ [])
      ∷ rule ".agdelte-tabs__header"
          ( "flex-wrap" ∶ "wrap"
          ∷ [])
      ∷ rule ".agdelte-pagination"
          ( "flex-wrap" ∶ "wrap"
          ∷ "justify-content" ∶ "center"
          ∷ [])
      ∷ rule ".agdelte-grid"
          ( "font-size" ∶ "0.875rem"
          ∷ [])
      ∷ rule ".agdelte-grid__cell"
          ( "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
          ∷ [])
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Tablet breakpoint
------------------------------------------------------------------------

tabletBreakpointRules : Stylesheet
tabletBreakpointRules =
    media "(max-width: 768px)"
      ( rule ".agdelte-grid"
          ( "font-size" ∶ "0.9375rem"
          ∷ [])
      ∷ rule ".agdelte-grid__cell"
          ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
          ∷ [])
      ∷ rule ".agdelte-datepicker__day"
          ( "width" ∶ "2rem"
          ∷ "height" ∶ "2rem"
          ∷ "font-size" ∶ "0.875rem"
          ∷ [])
      ∷ rule ".agdelte-tabs__header"
          ( "overflow-x" ∶ "auto"
          ∷ "flex-wrap" ∶ "nowrap"
          ∷ "-webkit-overflow-scrolling" ∶ "touch"
          ∷ [])
      ∷ rule ".agdelte-tabs__tab"
          ( "white-space" ∶ "nowrap"
          ∷ "flex-shrink" ∶ "0"
          ∷ [])
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Combined
------------------------------------------------------------------------

responsiveRules : Stylesheet
responsiveRules = reducedMotionRules ++ tabletBreakpointRules ++ mobileBreakpointRules
