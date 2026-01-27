{-# OPTIONS --without-K #-}

-- Html Types: базовые типы для виртуального DOM

module Agdelte.Html.Types where

open import Data.String using (String)
open import Data.List using (List; []; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; not)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Атрибуты
------------------------------------------------------------------------

-- Атрибут HTML элемента
data Attr (Msg : Set) : Set where
  -- Обычный атрибут (name="value")
  attr : String → String → Attr Msg
  -- Булев атрибут (disabled, checked, etc.)
  boolAttr : String → Attr Msg
  -- CSS стиль
  style : String → String → Attr Msg
  -- Обработчик событий
  on : String → Msg → Attr Msg
  -- Обработчик с данными (для input)
  onInput : (String → Msg) → Attr Msg
  -- Обработчик клавиш
  onKey : String → (String → Msg) → Attr Msg
  -- Ключ для эффективного diffing
  key : String → Attr Msg

-- FFI для Attr конструкторов
-- Параметр Msg стирается при компиляции
{-# COMPILE JS attr = name => value => ({ type: 'attr', name, value }) #-}
{-# COMPILE JS boolAttr = name => ({ type: 'boolAttr', name }) #-}
{-# COMPILE JS style = name => value => ({ type: 'style', name, value }) #-}
{-# COMPILE JS on = name => value => ({ type: 'on', name, value }) #-}
{-# COMPILE JS onInput = handler => ({ type: 'onInput', handler }) #-}
{-# COMPILE JS onKey = name => handler => ({ type: 'onKey', name, handler }) #-}
{-# COMPILE JS key = value => ({ type: 'key', value }) #-}

------------------------------------------------------------------------
-- HTML элементы
------------------------------------------------------------------------

-- Виртуальный DOM узел
data Html (Msg : Set) : Set where
  -- Элемент: тег, атрибуты, дети
  node : String → List (Attr Msg) → List (Html Msg) → Html Msg
  -- Текстовый узел
  text : String → Html Msg
  -- Keyed элемент (для списков)
  keyed : String → List (Attr Msg) → List (String × Html Msg) → Html Msg
  -- ПРИМЕЧАНИЕ: lazy требует Set₁, убран из MVP
  -- lazy : ∀ {A : Set} → A → (A → Html Msg) → Html Msg

-- FFI для Html конструкторов
-- Параметр Msg стирается при компиляции
{-# COMPILE JS node = tag => attrs => children => ({ tag, attrs, children }) #-}
{-# COMPILE JS text = s => ({ tag: 'TEXT', text: s }) #-}
{-# COMPILE JS keyed = tag => attrs => children => ({ tag, attrs, children, keyed: true }) #-}

------------------------------------------------------------------------
-- Functor для Attr и Html
------------------------------------------------------------------------

-- Преобразование сообщений в Attr
mapAttr : ∀ {A B : Set} → (A → B) → Attr A → Attr B
mapAttr f (attr name value) = attr name value
mapAttr f (boolAttr name) = boolAttr name
mapAttr f (style prop value) = style prop value
mapAttr f (on event msg) = on event (f msg)
mapAttr f (onInput handler) = onInput (f ∘ handler)
mapAttr f (onKey event handler) = onKey event (f ∘ handler)
mapAttr f (key k) = key k

-- Преобразование сообщений в Html
{-# TERMINATING #-}
mapHtml : ∀ {A B : Set} → (A → B) → Html A → Html B
mapHtml f (node tag attrs children) =
  node tag (map (mapAttr f) attrs) (map (mapHtml f) children)
mapHtml f (text s) = text s
mapHtml f (keyed tag attrs children) =
  keyed tag (map (mapAttr f) attrs) (map (λ p → proj₁ p , mapHtml f (proj₂ p)) children)

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Пустой элемент
empty : ∀ {Msg : Set} → Html Msg
empty = text ""

-- Группировка без обёртки (fragment)
fragment : ∀ {Msg : Set} → List (Html Msg) → Html Msg
fragment children = node "div" [] children  -- В реальности используем Fragment

-- Условный рендеринг
when : ∀ {Msg : Set} → Bool → Html Msg → Html Msg
when true  h = h
when false _ = empty

-- Unless
unless : ∀ {Msg : Set} → Bool → Html Msg → Html Msg
unless b = when (not b)
