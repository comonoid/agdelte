{-# OPTIONS --without-K #-}

-- Agdelte Controls CSS — aggregating module
--
-- Collects all control styles into a single Stylesheet.
-- This is the Agda source for the generated agdelte-controls.css.
--
-- Build:
--   agda --js --js-es6 --js-optimize --compile-dir=_build -i src src/Agdelte/Css/Controls.agda
--   node scripts/generate-css.js jAgda.Agdelte.Css.Controls controlsCSS examples_html/generated/agdelte-controls.css

module Agdelte.Css.Controls where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; _++_)

open import Agdelte.Css.Stylesheet using (Rule; rawRule; Stylesheet)

-- Import all submodules
open import Agdelte.Css.Controls.Variables   using (variablesRules)
open import Agdelte.Css.Controls.TabBar      using (tabBarRules)
open import Agdelte.Css.Controls.Modal       using (modalRules)
open import Agdelte.Css.Controls.Dropdown    using (dropdownRules)
open import Agdelte.Css.Controls.Toast       using (toastRules)
open import Agdelte.Css.Controls.DataGrid    using (dataGridRules)
open import Agdelte.Css.Controls.Checkbox    using (checkboxRules)
open import Agdelte.Css.Controls.RadioGroup  using (radioGroupRules)
open import Agdelte.Css.Controls.Slider      using (sliderRules)
open import Agdelte.Css.Controls.Pagination  using (paginationRules)
open import Agdelte.Css.Controls.Accordion   using (accordionRules)
open import Agdelte.Css.Controls.Sidebar     using (sidebarRules)
open import Agdelte.Css.Controls.Breadcrumb  using (breadcrumbRules)
open import Agdelte.Css.Controls.TreeView    using (treeViewRules)
open import Agdelte.Css.Controls.Tooltip     using (tooltipRules)
open import Agdelte.Css.Controls.Popover     using (popoverRules)
open import Agdelte.Css.Controls.Progress    using (progressRules)
open import Agdelte.Css.Controls.Stepper     using (stepperRules)
open import Agdelte.Css.Controls.DatePicker  using (datePickerRules)
open import Agdelte.Css.Controls.Animations  using (animationsRules)
open import Agdelte.Css.Controls.Responsive  using (responsiveRules)
open import Agdelte.Css.Controls.Video      using (videoRules)

------------------------------------------------------------------------
-- Section separators for readability in generated CSS
------------------------------------------------------------------------

sep : String → Rule
sep label = rawRule ("/* ======================================================================== " ++ˢ label ++ˢ " ======================================================================== */")

------------------------------------------------------------------------
-- Combined stylesheet
------------------------------------------------------------------------

controlsCSS : Stylesheet
controlsCSS =
    rawRule "/* Agdelte HTML Controls CSS — generated from Agda sources */"
  ∷ rawRule "/* Override with your own CSS or use CSS variables for theming. */"
  -- Variables
  ∷ sep "CSS Variables"
  ∷ (variablesRules
  -- TabBar
  ++ (sep "TabBar" ∷ tabBarRules)
  -- Modal
  ++ (sep "Modal" ∷ modalRules)
  -- Dropdown
  ++ (sep "Dropdown" ∷ dropdownRules)
  -- Toast
  ++ (sep "Toast" ∷ toastRules)
  -- DataGrid
  ++ (sep "DataGrid" ∷ dataGridRules)
  -- Checkbox
  ++ (sep "Checkbox" ∷ checkboxRules)
  -- RadioGroup
  ++ (sep "RadioGroup" ∷ radioGroupRules)
  -- Slider
  ++ (sep "Slider" ∷ sliderRules)
  -- Pagination
  ++ (sep "Pagination" ∷ paginationRules)
  -- Accordion
  ++ (sep "Accordion" ∷ accordionRules)
  -- Sidebar
  ++ (sep "Sidebar" ∷ sidebarRules)
  -- Breadcrumb
  ++ (sep "Breadcrumb" ∷ breadcrumbRules)
  -- TreeView
  ++ (sep "TreeView" ∷ treeViewRules)
  -- Tooltip
  ++ (sep "Tooltip" ∷ tooltipRules)
  -- Popover
  ++ (sep "Popover" ∷ popoverRules)
  -- Progress / Spinner / Skeleton
  ++ (sep "Progress" ∷ progressRules)
  -- Stepper
  ++ (sep "Stepper" ∷ stepperRules)
  -- DatePicker
  ++ (sep "DatePicker" ∷ datePickerRules)
  -- Animations
  ++ (sep "Animations" ∷ animationsRules)
  -- Responsive
  ++ (sep "Responsive" ∷ responsiveRules)
  -- Video Player
  ++ (sep "Video Player" ∷ videoRules))
