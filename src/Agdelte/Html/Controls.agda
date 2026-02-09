{-# OPTIONS --without-K #-}

-- Agdelte HTML Controls Library
-- Re-exports all HTML UI controls

module Agdelte.Html.Controls where

-- Navigation & Layout
open import Agdelte.Html.Controls.TabBar public

-- Feedback & Overlay
open import Agdelte.Html.Controls.Modal public
open import Agdelte.Html.Controls.Toast public

-- Forms & Input
open import Agdelte.Html.Controls.Dropdown public
