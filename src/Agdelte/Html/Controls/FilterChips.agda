{-# OPTIONS --without-K #-}

-- Filter-chips tool: a labelled group of toggle buttons ("All" + one per option)
-- for narrowing a list/catalog. Domain-neutral — options are plain strings, the
-- current selection comes from a getter, and select/clear emit host messages. The
-- domain owns its own filter STATE and matching logic; this is only the UI control.
-- Emits BEM classes .agdelte-filters__{group,label,btn}.

module Agdelte.Html.Controls.FilterChips where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)

open import Agdelte.Reactive.Node

-- | One filter group: a label, an "All" reset, and a button per option.
-- `getCurrent` is kept in the signature so a consumer can drive an active-state
-- highlight (e.g. via classBind) without changing the call shape.
filterButtons : ∀ {M A}
              → String               -- group label
              → List String          -- options
              → (M → Maybe String)   -- current selection (nothing = all)
              → (String → A)         -- on select
              → A                    -- on clear
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
