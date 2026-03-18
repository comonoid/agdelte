{-# OPTIONS --without-K #-}

-- CSS styles for the DatePicker, TimePicker, and DateRange controls
-- (HTML structure is in Agdelte.Html.Controls.DatePicker)

module Agdelte.Css.Controls.DatePicker where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- DatePicker rules
------------------------------------------------------------------------

datePickerRules : Stylesheet
datePickerRules =
    rule ".agdelte-datepicker"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ "min-width" ∶ "280px"
      ∷ [])
  -- Variant extension points (no extra styling)
  ∷ rule ".agdelte-datepicker--full" []
  ∷ rule ".agdelte-datepicker--range" []
  -- Header
  ∷ rule ".agdelte-datepicker__header"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "space-between"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__nav"
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
      ∷ "font-size" ∶ "0.875rem"
      ∷ "transition" ∶ "background var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__nav:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__nav:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-datepicker__title"
      ( "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  -- Weekdays
  ∷ rule ".agdelte-datepicker__weekdays"
      ( "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "repeat(7, 1fr)"
      ∷ "gap" ∶ "2px"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__weekday"
      ( "text-align" ∶ "center"
      ∷ "font-size" ∶ "0.75rem"
      ∷ "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) 0"
      ∷ [])
  -- Day grid
  ∷ rule ".agdelte-datepicker__grid"
      ( "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "repeat(7, 1fr)"
      ∷ "gap" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "36px"
      ∷ "height" ∶ "36px"
      ∷ "padding" ∶ "0"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--selected"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--selected:hover"
      ( "background" ∶ "var(--agdelte-primary-hover)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--today"
      ( "font-weight" ∶ "700"
      ∷ "border" ∶ "1px solid var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--empty"
      ( "visibility" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--disabled"
      ( "opacity" ∶ "0.35"
      ∷ "cursor" ∶ "not-allowed"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  -- Year/Month selectors
  ∷ rule ".agdelte-datepicker__year-selector, .agdelte-datepicker__month-selector"
      ( "display" ∶ "grid"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__year-selector"
      ( "grid-template-columns" ∶ "repeat(4, 1fr)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__month-selector"
      ( "grid-template-columns" ∶ "repeat(3, 1fr)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__year, .agdelte-datepicker__month"
      ( "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "1px solid transparent"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__year:hover, .agdelte-datepicker__month:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__year--current, .agdelte-datepicker__month--current"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  -- Quick action buttons
  ∷ rule ".agdelte-datepicker__today, .agdelte-datepicker__clear"
      ( "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__today:hover, .agdelte-datepicker__clear:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  -- DatePicker input variant
  ∷ rule ".agdelte-datepicker-input"
      ( "position" ∶ "relative"
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".agdelte-datepicker-input__field"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "min-width" ∶ "180px"
      ∷ "transition" ∶ "border-color var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-datepicker-input__field:hover"
      ( "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-datepicker-input .agdelte-datepicker"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "100%"
      ∷ "left" ∶ "0"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ "z-index" ∶ "var(--agdelte-z-dropdown)"
      ∷ "box-shadow" ∶ "var(--agdelte-shadow-lg)"
      ∷ [])
  -- Date range picker
  ∷ rule ".agdelte-daterange"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "var(--agdelte-spacing-md)"
      ∷ "flex-wrap" ∶ "wrap"
      ∷ [])
  ∷ rule ".agdelte-daterange__start, .agdelte-daterange__end"
      ( "flex" ∶ "1"
      ∷ "min-width" ∶ "280px"
      ∷ [])
  ∷ rule ".agdelte-daterange__label"
      ( "display" ∶ "block"
      ∷ "font-weight" ∶ "500"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  -- Range day highlights
  ∷ rule ".agdelte-datepicker__day--range-start"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius) 0 0 var(--agdelte-border-radius)"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--range-end"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border-radius" ∶ "0 var(--agdelte-border-radius) var(--agdelte-border-radius) 0"
      ∷ [])
  ∷ rule ".agdelte-datepicker__day--in-range"
      ( "background" ∶ "var(--agdelte-bg-active)"
      ∷ "border-radius" ∶ "0"
      ∷ [])
  -- Preset buttons
  ∷ rule ".agdelte-daterange__presets"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-daterange__preset"
      ( "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ "text-align" ∶ "left"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-daterange__preset:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  -- Time picker
  ∷ rule ".agdelte-timepicker"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-timepicker__hour, .agdelte-timepicker__minute"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-timepicker__btn"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "28px"
      ∷ "height" ∶ "28px"
      ∷ "padding" ∶ "0"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.75rem"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-timepicker__btn:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-timepicker__value"
      ( "font-size" ∶ "1.25rem"
      ∷ "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "min-width" ∶ "2ch"
      ∷ "text-align" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-timepicker__sep"
      ( "font-size" ∶ "1.25rem"
      ∷ "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ [])
  -- DateTime combo
  ∷ rule ".agdelte-datetimepicker"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-datetimepicker .agdelte-timepicker"
      ( "border-top" ∶ "1px solid var(--agdelte-border)"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ "padding-top" ∶ "var(--agdelte-spacing-sm)"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ []
