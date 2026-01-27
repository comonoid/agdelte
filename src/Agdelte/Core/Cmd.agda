{-# OPTIONS --without-K #-}

-- Cmd: одноразовые команды (side effects)
-- В отличие от Event (подписки), Cmd выполняется один раз

module Agdelte.Core.Cmd where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Function using (_∘_)

open import Agdelte.Core.Task as Task using (Task; Result; ok; err)

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Cmd — команды (одноразовые эффекты)
------------------------------------------------------------------------

data Cmd (A : Set) : Set where
  -- Пустая команда
  ε : Cmd A

  -- Композиция команд (выполняются параллельно)
  _<>_ : Cmd A → Cmd A → Cmd A

  -- HTTP запросы (простой API)
  httpGet  : String → (String → A) → (String → A) → Cmd A
  httpPost : String → String → (String → A) → (String → A) → Cmd A

  -- Запуск Task (монадический API)
  -- Task String — цепочка HTTP запросов, возвращает String или ошибку
  attempt : Task String → (Result String String → A) → Cmd A

infixr 5 _<>_

------------------------------------------------------------------------
-- Функторные операции
------------------------------------------------------------------------

mapCmd : (A → B) → Cmd A → Cmd B
mapCmd f ε = ε
mapCmd f (c₁ <> c₂) = mapCmd f c₁ <> mapCmd f c₂
mapCmd f (httpGet url onOk onErr) = httpGet url (f ∘ onOk) (f ∘ onErr)
mapCmd f (httpPost url body onOk onErr) = httpPost url body (f ∘ onOk) (f ∘ onErr)
mapCmd f (attempt task handler) = attempt task (f ∘ handler)

------------------------------------------------------------------------
-- Комбинаторы
------------------------------------------------------------------------

-- Batch из списка команд
batch : List (Cmd A) → Cmd A
batch [] = ε
batch (c ∷ cs) = c <> batch cs

-- Проверка на пустоту (для оптимизации runtime)
isEmpty : Cmd A → Set
isEmpty ε = ⊤
  where open import Data.Unit using (⊤)
isEmpty _ = ⊥
  where open import Data.Empty using (⊥)
