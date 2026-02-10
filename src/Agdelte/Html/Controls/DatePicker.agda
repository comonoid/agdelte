{-# OPTIONS --without-K #-}

-- DatePicker: Calendar-based date selection
-- CSS classes: .agdelte-datepicker, .agdelte-datepicker__header,
--              .agdelte-datepicker__grid, .agdelte-datepicker__day,
--              .agdelte-datepicker__day--selected

module Agdelte.Html.Controls.DatePicker where

open import Data.String as Str using (String; _++_)
open import Data.List as List using (List; []; _∷_) renaming (_++_ to _++ᴸ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Date type
------------------------------------------------------------------------

record Date : Set where
  constructor mkDate
  field
    year  : ℕ
    month : ℕ   -- 1-12
    day   : ℕ   -- 1-31

open Date public

------------------------------------------------------------------------
-- Date utilities
------------------------------------------------------------------------

private
  -- Nat equality
  _==ℕ_ : ℕ → ℕ → Bool
  zero ==ℕ zero = true
  zero ==ℕ suc _ = false
  suc _ ==ℕ zero = false
  suc m ==ℕ suc n = m ==ℕ n

-- Check date equality
eqDate : Date → Date → Bool
eqDate d1 d2 = (year d1 ==ℕ year d2) ∧ (month d1 ==ℕ month d2) ∧ (day d1 ==ℕ day d2)

-- Days in month (simplified)
daysInMonth : ℕ → ℕ → ℕ
daysInMonth _ 1 = 31
daysInMonth _ 2 = 28
daysInMonth _ 3 = 31
daysInMonth _ 4 = 30
daysInMonth _ 5 = 31
daysInMonth _ 6 = 30
daysInMonth _ 7 = 31
daysInMonth _ 8 = 31
daysInMonth _ 9 = 30
daysInMonth _ 10 = 31
daysInMonth _ 11 = 30
daysInMonth _ 12 = 31
daysInMonth _ _ = 30

-- Month name
monthName : ℕ → String
monthName 1 = "January"
monthName 2 = "February"
monthName 3 = "March"
monthName 4 = "April"
monthName 5 = "May"
monthName 6 = "June"
monthName 7 = "July"
monthName 8 = "August"
monthName 9 = "September"
monthName 10 = "October"
monthName 11 = "November"
monthName 12 = "December"
monthName _ = "Unknown"

------------------------------------------------------------------------
-- Simple DatePicker
------------------------------------------------------------------------

-- | Basic date picker calendar grid.
-- | getSelected: extract selected date from model
-- | viewYear/viewMonth: currently displayed month
-- | onSelect: message when date is clicked
-- | onPrev/onNext: messages to navigate months
datePickerSimple : ∀ {M A}
                 → (M → Maybe Date)    -- selected date (for highlighting)
                 → ℕ                   -- viewing year
                 → ℕ                   -- viewing month
                 → (Date → A)          -- on date select
                 → A                   -- prev month clicked
                 → A                   -- next month clicked
                 → Node M A
datePickerSimple {M} {A} getSelected viewYear viewMonth onSelect onPrev onNext =
  div (class "agdelte-datepicker" ∷ [])
    ( -- Header
      div (class "agdelte-datepicker__header" ∷ [])
        ( button ( class "agdelte-datepicker__nav"
                 ∷ onClick onPrev
                 ∷ [] )
            ( text "◀" ∷ [] )
        ∷ span (class "agdelte-datepicker__title" ∷ [])
            ( text (monthName viewMonth ++ " " ++ show viewYear) ∷ [] )
        ∷ button ( class "agdelte-datepicker__nav"
                 ∷ onClick onNext
                 ∷ [] )
            ( text "▶" ∷ [] )
        ∷ [] )
    -- Weekday header
    ∷ div (class "agdelte-datepicker__weekdays" ∷ [])
        ( span (class "agdelte-datepicker__weekday" ∷ []) (text "Su" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "Mo" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "Tu" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "We" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "Th" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "Fr" ∷ [])
        ∷ span (class "agdelte-datepicker__weekday" ∷ []) (text "Sa" ∷ [])
        ∷ [] )
    -- Day grid
    ∷ div (class "agdelte-datepicker__grid" ∷ [])
        (renderDays 1 (daysInMonth viewYear viewMonth))
    ∷ [] )
  where
    isSelected : ℕ → M → Bool
    isSelected d m with getSelected m
    ... | nothing = false
    ... | just sel = eqDate (mkDate viewYear viewMonth d) sel

    dayClass : ℕ → M → String
    dayClass d m =
      if isSelected d m
      then "agdelte-datepicker__day agdelte-datepicker__day--selected"
      else "agdelte-datepicker__day"

    renderDays : ℕ → ℕ → List (Node M A)
    renderDays _ zero = []
    renderDays d (suc k) =
      button ( classBind (dayClass d)
             ∷ onClick (onSelect (mkDate viewYear viewMonth d))
             ∷ [] )
        ( text (show d) ∷ [] )
      ∷ renderDays (suc d) k

------------------------------------------------------------------------
-- DatePicker with input field (uses Popover pattern)
------------------------------------------------------------------------

-- | DatePicker shown in popover from an input field
datePickerInput : ∀ {M A}
                → (M → Maybe Date)    -- selected date
                → (M → Bool)          -- is picker open
                → ℕ → ℕ               -- viewing year/month
                → (Date → A)          -- on select
                → A                   -- toggle picker
                → A → A               -- prev/next month
                → Node M A
datePickerInput {M} {A} getSelected isOpen viewYear viewMonth onSelect toggle onPrev onNext =
  div (class "agdelte-datepicker-input" ∷ [])
    ( -- Input field showing selected date
      div ( class "agdelte-datepicker-input__field"
          ∷ onClick toggle
          ∷ [] )
        ( bindF formatDate ∷ [] )
    -- Dropdown calendar
    ∷ when isOpen
        (datePickerSimple getSelected viewYear viewMonth onSelect onPrev onNext)
    ∷ [] )
  where
    formatDate : M → String
    formatDate m with getSelected m
    ... | nothing = "Select date..."
    ... | just d = show (day d) ++ "/" ++ show (month d) ++ "/" ++ show (year d)

------------------------------------------------------------------------
-- Month/Year navigation helpers
------------------------------------------------------------------------

-- | Navigate to previous month (returns new year, month)
prevMonth : ℕ → ℕ → ℕ × ℕ
prevMonth y 1 = (y ∸ 1 , 12)
prevMonth y m = (y , m ∸ 1)

-- | Navigate to next month (returns new year, month)
nextMonth : ℕ → ℕ → ℕ × ℕ
nextMonth y 12 = (y + 1 , 1)
nextMonth y m = (y , m + 1)

------------------------------------------------------------------------
-- Leap year and advanced date utilities
------------------------------------------------------------------------

private
  -- Check if year is a leap year
  isLeapYear : ℕ → Bool
  isLeapYear y =
    let mod4 = modN y 4
        mod100 = modN y 100
        mod400 = modN y 400
    in (mod4 ==ℕ 0 ∧ not (mod100 ==ℕ 0)) ∨ (mod400 ==ℕ 0)
    where
      open import Data.Bool using (not; _∨_)

      modN : ℕ → ℕ → ℕ
      modN _ 0 = 0
      modN n m = mod' n m n
        where
          mod' : ℕ → ℕ → ℕ → ℕ
          mod' _ _ zero = 0
          mod' acc divisor (suc fuel) =
            if acc <ᵇ divisor then acc else mod' (acc ∸ divisor) divisor fuel
            where
              open import Data.Nat using (_<ᵇ_)

-- Days in month with leap year support
daysInMonthLeap : ℕ → ℕ → ℕ
daysInMonthLeap y 1 = 31
daysInMonthLeap y 2 = if isLeapYear y then 29 else 28
daysInMonthLeap _ 3 = 31
daysInMonthLeap _ 4 = 30
daysInMonthLeap _ 5 = 31
daysInMonthLeap _ 6 = 30
daysInMonthLeap _ 7 = 31
daysInMonthLeap _ 8 = 31
daysInMonthLeap _ 9 = 30
daysInMonthLeap _ 10 = 31
daysInMonthLeap _ 11 = 30
daysInMonthLeap _ 12 = 31
daysInMonthLeap _ _ = 30

-- | First day of month (0 = Sunday, 6 = Saturday)
-- Uses Zeller's congruence simplified
firstDayOfMonth : ℕ → ℕ → ℕ
firstDayOfMonth y m =
  let y' = if m <ᵇ 3 then y ∸ 1 else y
      m' = if m <ᵇ 3 then m + 12 else m
      q = 1
      k = modN y' 100
      j = divN y' 100
      h = modN (q + divN (13 * (m' + 1)) 5 + k + divN k 4 + divN j 4 + 5 * j) 7
  in modN (h + 6) 7
  where
    open import Data.Nat using (_<ᵇ_; _*_)

    modN : ℕ → ℕ → ℕ
    modN _ 0 = 0
    modN n m' = mod' n m' n
      where
        mod' : ℕ → ℕ → ℕ → ℕ
        mod' _ _ zero = 0
        mod' acc divisor (suc fuel) =
          if acc <ᵇ divisor then acc else mod' (acc ∸ divisor) divisor fuel

    divN : ℕ → ℕ → ℕ
    divN _ 0 = 0
    divN n m' = div' n m' n 0
      where
        div' : ℕ → ℕ → ℕ → ℕ → ℕ
        div' _ _ zero acc = acc
        div' num divisor (suc fuel) acc =
          if num <ᵇ divisor then acc else div' (num ∸ divisor) divisor fuel (suc acc)

-- | Compare dates
dateLt : Date → Date → Bool
dateLt d1 d2 =
  if year d1 <ᵇ year d2 then true
  else if year d1 ==ℕ year d2 then
    if month d1 <ᵇ month d2 then true
    else if month d1 ==ℕ month d2 then day d1 <ᵇ day d2
    else false
  else false
  where
    open import Data.Nat using (_<ᵇ_)

dateLte : Date → Date → Bool
dateLte d1 d2 = dateLt d1 d2 ∨ eqDate d1 d2
  where
    open import Data.Bool using (_∨_)

-- | Check if date is in range
dateInRange : Date → Date → Date → Bool
dateInRange d minD maxD = dateLte minD d ∧ dateLte d maxD

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

record DatePickerConfig : Set where
  constructor mkDatePickerConfig
  field
    dpLocale        : String          -- "en", "ru", "de", etc.
    dpStartMonday   : Bool            -- true = week starts Monday
    dpShowWeekNums  : Bool            -- show week numbers
    dpMinDate       : Maybe Date      -- minimum selectable date
    dpMaxDate       : Maybe Date      -- maximum selectable date

open DatePickerConfig public

defaultDatePickerConfig : DatePickerConfig
defaultDatePickerConfig = mkDatePickerConfig "en" false false nothing nothing

-- | Localized month names
monthNameLocalized : String → ℕ → String
monthNameLocalized "ru" 1 = "Январь"
monthNameLocalized "ru" 2 = "Февраль"
monthNameLocalized "ru" 3 = "Март"
monthNameLocalized "ru" 4 = "Апрель"
monthNameLocalized "ru" 5 = "Май"
monthNameLocalized "ru" 6 = "Июнь"
monthNameLocalized "ru" 7 = "Июль"
monthNameLocalized "ru" 8 = "Август"
monthNameLocalized "ru" 9 = "Сентябрь"
monthNameLocalized "ru" 10 = "Октябрь"
monthNameLocalized "ru" 11 = "Ноябрь"
monthNameLocalized "ru" 12 = "Декабрь"
monthNameLocalized "de" 1 = "Januar"
monthNameLocalized "de" 2 = "Februar"
monthNameLocalized "de" 3 = "März"
monthNameLocalized "de" 4 = "April"
monthNameLocalized "de" 5 = "Mai"
monthNameLocalized "de" 6 = "Juni"
monthNameLocalized "de" 7 = "Juli"
monthNameLocalized "de" 8 = "August"
monthNameLocalized "de" 9 = "September"
monthNameLocalized "de" 10 = "Oktober"
monthNameLocalized "de" 11 = "November"
monthNameLocalized "de" 12 = "Dezember"
monthNameLocalized _ m = monthName m

-- | Localized weekday headers (short)
weekdayHeaders : String → Bool → List String
weekdayHeaders "ru" true  = "Пн" ∷ "Вт" ∷ "Ср" ∷ "Чт" ∷ "Пт" ∷ "Сб" ∷ "Вс" ∷ []
weekdayHeaders "ru" false = "Вс" ∷ "Пн" ∷ "Вт" ∷ "Ср" ∷ "Чт" ∷ "Пт" ∷ "Сб" ∷ []
weekdayHeaders "de" true  = "Mo" ∷ "Di" ∷ "Mi" ∷ "Do" ∷ "Fr" ∷ "Sa" ∷ "So" ∷ []
weekdayHeaders "de" false = "So" ∷ "Mo" ∷ "Di" ∷ "Mi" ∷ "Do" ∷ "Fr" ∷ "Sa" ∷ []
weekdayHeaders _ true  = "Mo" ∷ "Tu" ∷ "We" ∷ "Th" ∷ "Fr" ∷ "Sa" ∷ "Su" ∷ []
weekdayHeaders _ false = "Su" ∷ "Mo" ∷ "Tu" ∷ "We" ∷ "Th" ∷ "Fr" ∷ "Sa" ∷ []

------------------------------------------------------------------------
-- Full-featured DatePicker
------------------------------------------------------------------------

-- | Full calendar with config support
datePickerFull : ∀ {M A}
               → DatePickerConfig
               → (M → Maybe Date)     -- selected date
               → ℕ → ℕ                -- viewing year/month
               → (Date → A)           -- on date select
               → A → A                -- prev/next month
               → Node M A
datePickerFull {M} {A} cfg getSelected viewYear viewMonth onSelect onPrev onNext =
  div (class "agdelte-datepicker agdelte-datepicker--full" ∷ [])
    ( -- Header with navigation
      div (class "agdelte-datepicker__header" ∷ [])
        ( button ( class "agdelte-datepicker__nav"
                 ∷ onClick onPrev
                 ∷ [] )
            ( text "◀" ∷ [] )
        ∷ span (class "agdelte-datepicker__title" ∷ [])
            ( text (monthNameLocalized (dpLocale cfg) viewMonth ++ " " ++ show viewYear) ∷ [] )
        ∷ button ( class "agdelte-datepicker__nav"
                 ∷ onClick onNext
                 ∷ [] )
            ( text "▶" ∷ [] )
        ∷ [] )
    -- Weekday headers (localized)
    ∷ div (class "agdelte-datepicker__weekdays" ∷ [])
        (renderWeekdays (weekdayHeaders (dpLocale cfg) (dpStartMonday cfg)))
    -- Day grid with proper first-day offset
    ∷ div (class "agdelte-datepicker__grid" ∷ [])
        (renderEmptyDays (adjustFirstDay (firstDayOfMonth viewYear viewMonth))
         ++ᴸ renderDays 1 (daysInMonthLeap viewYear viewMonth))
    ∷ [] )
  where
    adjustFirstDay : ℕ → ℕ
    adjustFirstDay fd =
      if dpStartMonday cfg
      then (fd + 6) ∸ (if fd ==ℕ 0 then 0 else 0)  -- adjust for Monday start
      else fd

    isSelected : ℕ → M → Bool
    isSelected d m with getSelected m
    ... | nothing = false
    ... | just sel = eqDate (mkDate viewYear viewMonth d) sel

    isDisabled : ℕ → Bool
    isDisabled d =
      let thisDate = mkDate viewYear viewMonth d
      in case (dpMinDate cfg , dpMaxDate cfg) of λ where
           (nothing , nothing) → false
           (just minD , nothing) → dateLt thisDate minD
           (nothing , just maxD) → dateLt maxD thisDate
           (just minD , just maxD) → dateLt thisDate minD ∨ dateLt maxD thisDate
      where
        open import Data.Bool using (_∨_)
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

    dayClass : ℕ → M → String
    dayClass d m =
      let base = "agdelte-datepicker__day"
          sel = if isSelected d m then " agdelte-datepicker__day--selected" else ""
          dis = if isDisabled d then " agdelte-datepicker__day--disabled" else ""
      in base ++ sel ++ dis

    renderWeekdays : List String → List (Node M A)
    renderWeekdays [] = []
    renderWeekdays (w ∷ ws) =
      span (class "agdelte-datepicker__weekday" ∷ []) (text w ∷ [])
      ∷ renderWeekdays ws

    renderEmptyDays : ℕ → List (Node M A)
    renderEmptyDays zero = []
    renderEmptyDays (suc n) =
      span (class "agdelte-datepicker__day agdelte-datepicker__day--empty" ∷ []) (text "" ∷ [])
      ∷ renderEmptyDays n

    renderDays : ℕ → ℕ → List (Node M A)
    renderDays _ zero = []
    renderDays d (suc k) =
      let disabled = isDisabled d
      in (if disabled
          then span ( classBind (dayClass d)
                    ∷ [] )
                 ( text (show d) ∷ [] )
          else button ( classBind (dayClass d)
                      ∷ onClick (onSelect (mkDate viewYear viewMonth d))
                      ∷ [] )
                 ( text (show d) ∷ [] ))
         ∷ renderDays (suc d) k

------------------------------------------------------------------------
-- Year/Month selector
------------------------------------------------------------------------

-- | Year selector dropdown
yearSelector : ∀ {M A}
             → ℕ                      -- current year
             → ℕ                      -- range (years before/after)
             → (ℕ → A)                -- on year select
             → Node M A
yearSelector {M} {A} currentYear range onSelect =
  div (class "agdelte-datepicker__year-selector" ∷ [])
    (renderYears (currentYear ∸ range) (range + range + 1))
  where
    renderYears : ℕ → ℕ → List (Node M A)
    renderYears _ zero = []
    renderYears y (suc n) =
      button ( class (if y ==ℕ currentYear
                      then "agdelte-datepicker__year agdelte-datepicker__year--current"
                      else "agdelte-datepicker__year")
             ∷ onClick (onSelect y)
             ∷ [] )
        ( text (show y) ∷ [] )
      ∷ renderYears (suc y) n

-- | Month selector grid
monthSelector : ∀ {M A}
              → String                -- locale
              → ℕ                     -- current month (for highlighting)
              → (ℕ → A)               -- on month select
              → Node M A
monthSelector {M} {A} locale currentMonth onSelect =
  div (class "agdelte-datepicker__month-selector" ∷ [])
    (renderMonths 1 12)
  where
    renderMonths : ℕ → ℕ → List (Node M A)
    renderMonths _ zero = []
    renderMonths m (suc remaining) =
      button ( class (if m ==ℕ currentMonth
                      then "agdelte-datepicker__month agdelte-datepicker__month--current"
                      else "agdelte-datepicker__month")
             ∷ onClick (onSelect m)
             ∷ [] )
        ( text (monthNameLocalized locale m) ∷ [] )
      ∷ renderMonths (suc m) remaining

------------------------------------------------------------------------
-- Quick date selections
------------------------------------------------------------------------

-- | Today button
todayButton : ∀ {M A}
            → Date                    -- today's date
            → (Date → A)              -- on select today
            → Node M A
todayButton today onSelect =
  button ( class "agdelte-datepicker__today"
         ∷ onClick (onSelect today)
         ∷ [] )
    ( text "Today" ∷ [] )

-- | Clear selection button
clearButton : ∀ {M A}
            → A                       -- on clear
            → Node M A
clearButton onClear =
  button ( class "agdelte-datepicker__clear"
         ∷ onClick onClear
         ∷ [] )
    ( text "Clear" ∷ [] )

------------------------------------------------------------------------
-- Date range picker with highlighting
------------------------------------------------------------------------

-- | Picker for selecting a date range (two calendars side by side)
dateRangePicker : ∀ {M A}
                → (M → Maybe Date)    -- start date
                → (M → Maybe Date)    -- end date
                → ℕ → ℕ               -- viewing year/month for start
                → ℕ → ℕ               -- viewing year/month for end
                → (Date → A)          -- on start select
                → (Date → A)          -- on end select
                → A → A               -- prev/next for start calendar
                → A → A               -- prev/next for end calendar
                → Node M A
dateRangePicker getStart getEnd y1 m1 y2 m2 onStart onEnd prev1 next1 prev2 next2 =
  div (class "agdelte-daterange" ∷ [])
    ( -- Start date picker
      div (class "agdelte-daterange__start" ∷ [])
        ( span (class "agdelte-daterange__label" ∷ []) (text "From:" ∷ [])
        ∷ datePickerSimple getStart y1 m1 onStart prev1 next1
        ∷ [] )
    -- End date picker
    ∷ div (class "agdelte-daterange__end" ∷ [])
        ( span (class "agdelte-daterange__label" ∷ []) (text "To:" ∷ [])
        ∷ datePickerSimple getEnd y2 m2 onEnd prev2 next2
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Single calendar range picker with in-range highlighting
------------------------------------------------------------------------

-- | Single calendar for date range with in-range highlighting
dateRangeCalendar : ∀ {M A}
                  → DatePickerConfig
                  → (M → Maybe Date)     -- start date
                  → (M → Maybe Date)     -- end date
                  → (M → Bool)           -- is selecting end date
                  → ℕ → ℕ                -- viewing year/month
                  → (Date → A)           -- on date click
                  → A → A                -- prev/next month
                  → Node M A
dateRangeCalendar {M} {A} cfg getStart getEnd isSelectingEnd viewYear viewMonth onClick' onPrev onNext =
  div (class "agdelte-datepicker agdelte-datepicker--range" ∷ [])
    ( -- Header
      div (class "agdelte-datepicker__header" ∷ [])
        ( button ( class "agdelte-datepicker__nav" ∷ onClick onPrev ∷ [] )
            ( text "◀" ∷ [] )
        ∷ span (class "agdelte-datepicker__title" ∷ [])
            ( text (monthNameLocalized (dpLocale cfg) viewMonth ++ " " ++ show viewYear) ∷ [] )
        ∷ button ( class "agdelte-datepicker__nav" ∷ onClick onNext ∷ [] )
            ( text "▶" ∷ [] )
        ∷ [] )
    -- Weekday headers
    ∷ div (class "agdelte-datepicker__weekdays" ∷ [])
        (renderWeekdays (weekdayHeaders (dpLocale cfg) (dpStartMonday cfg)))
    -- Day grid
    ∷ div (class "agdelte-datepicker__grid" ∷ [])
        (renderDays 1 (daysInMonthLeap viewYear viewMonth))
    ∷ [] )
  where
    open import Data.Bool using (not; _∨_)

    getDayClass : ℕ → M → String
    getDayClass d m =
      let thisDate = mkDate viewYear viewMonth d
          startM = getStart m
          endM = getEnd m
          base = "agdelte-datepicker__day"
          isStart = caseOf startM (λ { nothing → false ; (just s) → eqDate thisDate s })
          isEnd = caseOf endM (λ { nothing → false ; (just e) → eqDate thisDate e })
          inRange = caseOf2 startM endM
            (λ { (just s) (just e) → dateLte s thisDate ∧ dateLte thisDate e ; _ _ → false })
          startCls = if isStart then " agdelte-datepicker__day--range-start" else ""
          endCls = if isEnd then " agdelte-datepicker__day--range-end" else ""
          rangeCls = if inRange ∧ not isStart ∧ not isEnd
                     then " agdelte-datepicker__day--in-range"
                     else ""
      in base ++ startCls ++ endCls ++ rangeCls
      where
        caseOf : ∀ {X Y : Set} → Maybe X → (Maybe X → Y) → Y
        caseOf x f = f x
        caseOf2 : ∀ {X Y Z : Set} → Maybe X → Maybe Y → (Maybe X → Maybe Y → Z) → Z
        caseOf2 x y f = f x y

    renderWeekdays : List String → List (Node M A)
    renderWeekdays [] = []
    renderWeekdays (w ∷ ws) =
      span (class "agdelte-datepicker__weekday" ∷ []) (text w ∷ [])
      ∷ renderWeekdays ws

    renderDays : ℕ → ℕ → List (Node M A)
    renderDays _ zero = []
    renderDays d (suc k) =
      button ( classBind (getDayClass d)
             ∷ onClick (onClick' (mkDate viewYear viewMonth d))
             ∷ [] )
        ( text (show d) ∷ [] )
      ∷ renderDays (suc d) k

------------------------------------------------------------------------
-- Preset date ranges
------------------------------------------------------------------------

-- | Common preset date ranges
data DatePreset : Set where
  Today       : DatePreset
  Yesterday   : DatePreset
  Last7Days   : DatePreset
  Last30Days  : DatePreset
  ThisMonth   : DatePreset
  LastMonth   : DatePreset
  ThisYear    : DatePreset

-- | Preset selector buttons
datePresetSelector : ∀ {M A}
                   → (DatePreset → A)
                   → Node M A
datePresetSelector {M} {A} onSelect =
  div (class "agdelte-daterange__presets" ∷ [])
    ( button ( class "agdelte-daterange__preset" ∷ onClick (onSelect Today) ∷ [] )
        ( text "Today" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect Yesterday) ∷ [] )
        ( text "Yesterday" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect Last7Days) ∷ [] )
        ( text "Last 7 days" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect Last30Days) ∷ [] )
        ( text "Last 30 days" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect ThisMonth) ∷ [] )
        ( text "This month" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect LastMonth) ∷ [] )
        ( text "Last month" ∷ [] )
    ∷ button ( class "agdelte-daterange__preset" ∷ onClick (onSelect ThisYear) ∷ [] )
        ( text "This year" ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Time picker addon
------------------------------------------------------------------------

-- | Time component (hours:minutes)
record Time : Set where
  constructor mkTime
  field
    hour   : ℕ   -- 0-23
    minute : ℕ   -- 0-59

open Time public

-- | DateTime combining date and time
record DateTime : Set where
  constructor mkDateTime
  field
    dtDate : Date
    dtTime : Time

open DateTime public

-- | Simple time picker (hour/minute inputs)
-- | Uses message constructors for increment/decrement actions
timePicker : ∀ {M A}
           → (M → String)             -- current hour (as string)
           → (M → String)             -- current minute (as string)
           → A                        -- increment hour
           → A                        -- decrement hour
           → A                        -- increment minute
           → A                        -- decrement minute
           → Node M A
timePicker {M} {A} getHour getMinute incH decH incM decM =
  div (class "agdelte-timepicker" ∷ [])
    ( -- Hour selector
      div (class "agdelte-timepicker__hour" ∷ [])
        ( button ( class "agdelte-timepicker__btn" ∷ onClick incH ∷ [] )
            ( text "▲" ∷ [] )
        ∷ span (class "agdelte-timepicker__value" ∷ [])
            ( bindF getHour ∷ [] )
        ∷ button ( class "agdelte-timepicker__btn" ∷ onClick decH ∷ [] )
            ( text "▼" ∷ [] )
        ∷ [] )
    -- Separator
    ∷ span (class "agdelte-timepicker__sep" ∷ [])
        ( text ":" ∷ [] )
    -- Minute selector
    ∷ div (class "agdelte-timepicker__minute" ∷ [])
        ( button ( class "agdelte-timepicker__btn" ∷ onClick incM ∷ [] )
            ( text "▲" ∷ [] )
        ∷ span (class "agdelte-timepicker__value" ∷ [])
            ( bindF getMinute ∷ [] )
        ∷ button ( class "agdelte-timepicker__btn" ∷ onClick decM ∷ [] )
            ( text "▼" ∷ [] )
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- DateTime picker
------------------------------------------------------------------------

-- | Combined date and time picker
dateTimePicker : ∀ {M A}
               → DatePickerConfig
               → (M → Maybe Date)     -- selected date
               → (M → String)         -- hour (as string)
               → (M → String)         -- minute (as string)
               → ℕ → ℕ                -- viewing year/month
               → (Date → A)           -- on date select
               → A → A                -- increment/decrement hour
               → A → A                -- increment/decrement minute
               → A → A                -- prev/next month
               → Node M A
dateTimePicker cfg getDate getHour getMinute viewYear viewMonth onDate incH decH incM decM onPrev onNext =
  div (class "agdelte-datetimepicker" ∷ [])
    ( datePickerFull cfg getDate viewYear viewMonth onDate onPrev onNext
    ∷ timePicker getHour getMinute incH decH incM decM
    ∷ [] )
