{-# OPTIONS --without-K #-}

-- Html Navigation: high-level primitives for SPA navigation

module Agdelte.Html.Navigation where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)

open import Agdelte.Html.Types
open import Agdelte.Html.Elements using (a)
open import Agdelte.Html.Attributes using (href; class)
open import Agdelte.Html.Events using (onClickPrevent)

private
  variable
    Msg : Set

------------------------------------------------------------------------
-- Navigation Link
------------------------------------------------------------------------

-- | Navigation link for SPA
-- Automatically: preventDefault + dispatch Msg
-- URL is rendered in href for SEO and Ctrl+Click
navLink : String → Msg → List (Attr Msg) → List (Html Msg) → Html Msg
navLink url msg attrs children =
  a (onClickPrevent msg ∷ href url ∷ attrs) children

-- | Simple navigation link (text only)
navLink' : String → Msg → String → Html Msg
navLink' url msg label = navLink url msg [] (text label ∷ [])

-- | Navigation link with class
navLinkClass : String → Msg → String → String → Html Msg
navLinkClass url msg className label =
  navLink url msg (class className ∷ []) (text label ∷ [])
