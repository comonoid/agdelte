{-# OPTIONS --without-K #-}

-- Html Navigation: высокоуровневые примитивы для SPA навигации

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

-- | Навигационная ссылка для SPA
-- Автоматически: preventDefault + dispatch Msg
-- URL отображается в href для SEO и Ctrl+Click
navLink : String → Msg → List (Attr Msg) → List (Html Msg) → Html Msg
navLink url msg attrs children =
  a (onClickPrevent msg ∷ href url ∷ attrs) children

-- | Простая навигационная ссылка (только текст)
navLink' : String → Msg → String → Html Msg
navLink' url msg label = navLink url msg [] (text label ∷ [])

-- | Навигационная ссылка с классом
navLinkClass : String → Msg → String → String → Html Msg
navLinkClass url msg className label =
  navLink url msg (class className ∷ []) (text label ∷ [])
