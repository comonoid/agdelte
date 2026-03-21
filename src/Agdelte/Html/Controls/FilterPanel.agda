{-# OPTIONS --without-K --guardedness #-}

-- Filter panel for course catalog.
-- CSS classes: .agdelte-filters, .agdelte-filters__group, .agdelte-filters__label

module Agdelte.Html.Controls.FilterPanel where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Base using (filterᵇ)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node
open import Agdelte.Storage.AppStore using (CourseRecord; crCategory; crLevel; crPrice; crTitle)

------------------------------------------------------------------------
-- Filter state
------------------------------------------------------------------------

record FilterState : Set where
  constructor mkFilterState
  field
    fsQuery    : String          -- text search
    fsCategory : Maybe String    -- selected category (nothing = all)
    fsLevel    : Maybe String    -- selected level (nothing = all)
    fsMaxPrice : Maybe ℕ         -- max price in kopecks (nothing = no limit)

open FilterState public

emptyFilter : FilterState
emptyFilter = mkFilterState "" nothing nothing nothing

------------------------------------------------------------------------
-- Filter logic (pure)
------------------------------------------------------------------------

-- | Simple substring check (JS postulate).
postulate
  containsIgnoreCase : String → String → Bool

{-# COMPILE JS containsIgnoreCase = function(needle) {
  return function(haystack) {
    return haystack.toLowerCase().includes(needle.toLowerCase());
  };
} #-}

-- | Does a course match the current filter state?
matchesFilter : FilterState → CourseRecord → Bool
matchesFilter fs c =
  matchQuery ∧ matchCategory ∧ matchLevel ∧ matchPrice
  where
    matchQuery : Bool
    matchQuery with fsQuery fs ≟ ""
    ... | yes _ = true
    ... | no _  = containsIgnoreCase (fsQuery fs) (crTitle c)

    matchCategory : Bool
    matchCategory with fsCategory fs
    ... | nothing  = true
    ... | just cat with cat ≟ crCategory c
    ...   | yes _ = true
    ...   | no _  = false

    matchLevel : Bool
    matchLevel with fsLevel fs
    ... | nothing  = true
    ... | just lvl with lvl ≟ crLevel c
    ...   | yes _ = true
    ...   | no _  = false

    matchPrice : Bool
    matchPrice with fsMaxPrice fs
    ... | nothing = true
    ... | just mp = crPrice c ≤ᵇ mp

-- | Apply filter to a list of courses.
filterCourses : FilterState → List CourseRecord → List CourseRecord
filterCourses fs = filterᵇ (matchesFilter fs)

------------------------------------------------------------------------
-- Filter panel UI
------------------------------------------------------------------------

-- | Filter button: one button per option, highlights when active.
filterButtons : ∀ {M A}
              → String               -- group label
              → List String           -- options
              → (M → Maybe String)   -- current selection
              → (String → A)        -- on select
              → A                   -- on clear
              → Node M A
filterButtons groupLabel options getCurrent onSelect onClear =
  div (class "agdelte-filters__group" ∷ [])
    ( span (class "agdelte-filters__label" ∷ [])
        ( text groupLabel ∷ [] )
    ∷ button ( class "agdelte-filters__btn"
             ∷ onClick onClear
             ∷ [] )
        ( text "Все" ∷ [] )
    ∷ mkButtons options )
  where
    mkButtons : List String → List (Node _ _)
    mkButtons [] = []
    mkButtons (o ∷ os) =
      button ( class "agdelte-filters__btn"
             ∷ onClick (onSelect o)
             ∷ [] )
        ( text o ∷ [] )
      ∷ mkButtons os
