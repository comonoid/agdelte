{-# OPTIONS --without-K #-}

-- Agdelte HTML Controls Library
-- Re-exports all HTML UI controls

module Agdelte.Html.Controls where

-- Navigation & Layout
open import Agdelte.Html.Controls.TabBar public

-- Feedback & Overlay
open import Agdelte.Html.Controls.Modal public
open import Agdelte.Html.Controls.Toast public

-- Data Display
open import Agdelte.Html.Controls.DataGrid public
open import Agdelte.Html.Controls.Table public

-- Forms & Input
open import Agdelte.Html.Controls.Dropdown public
open import Agdelte.Html.Controls.Checkbox public
open import Agdelte.Html.Controls.RadioGroup public
open import Agdelte.Html.Controls.Slider public
open import Agdelte.Html.Controls.DatePicker public

-- Navigation
open import Agdelte.Html.Controls.Pagination public

-- Layout
open import Agdelte.Html.Controls.Accordion public
open import Agdelte.Html.Controls.Sidebar public
open import Agdelte.Html.Controls.Breadcrumb public
open import Agdelte.Html.Controls.TreeView public

-- Feedback
open import Agdelte.Html.Controls.Tooltip public
open import Agdelte.Html.Controls.Progress public
-- open import Agdelte.Html.Controls.Popover public  -- conflicts with Tooltip.popover
-- open import Agdelte.Html.Controls.Spinner public  -- conflicts with Progress.spinner
-- open import Agdelte.Html.Controls.Skeleton public  -- conflicts with Progress.skeleton*

-- Wizard
open import Agdelte.Html.Controls.Stepper public
