{-# OPTIONS --without-K --guardedness #-}

-- Signal: дискретный поток значений (коиндуктивный)
-- Signal A ≅ Coalg (Mono A ⊤) = ν X. A × X
--
-- Полином Mono A ⊤ имеет:
--   Pos = A (что выдаём)
--   Dir = λ _ → ⊤ (один вход для перехода к следующему)
--
-- Интерпретация: ⟦Mono A ⊤⟧(X) = Σ A (λ _ → ⊤ → X) ≅ A × X

module Agdelte.Core.Signal where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; concat; filter; foldr)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)

private
  variable
    A B C : Set

------------------------------------------------------------------------
-- Signal: коиндуктивный дискретный поток
------------------------------------------------------------------------

record Signal (A : Set) : Set where
  coinductive
  field
    now  : A           -- Текущее значение
    next : Signal A    -- Следующий момент времени

open Signal public

------------------------------------------------------------------------
-- Конструкторы
------------------------------------------------------------------------

-- Константный сигнал
constant : A → Signal A
now  (constant a) = a
next (constant a) = constant a

-- Синоним для ясности
pure : A → Signal A
pure = constant

------------------------------------------------------------------------
-- Functor
------------------------------------------------------------------------

-- map для Signal (ленивый)
mapS : (A → B) → Signal A → Signal B
now  (mapS f s) = f (now s)
next (mapS f s) = mapS f (next s)

-- Инфиксная версия
_<$>_ : (A → B) → Signal A → Signal B
_<$>_ = mapS

infixl 4 _<$>_

------------------------------------------------------------------------
-- Applicative
------------------------------------------------------------------------

-- Применение функции из сигнала к значению из сигнала
_<*>_ : Signal (A → B) → Signal A → Signal B
now  (sf <*> sa) = now sf (now sa)
next (sf <*> sa) = next sf <*> next sa

infixl 4 _<*>_

-- liftA2
liftA2 : (A → B → C) → Signal A → Signal B → Signal C
liftA2 f sa sb = mapS f sa <*> sb

-- liftA3
liftA3 : ∀ {D : Set} → (A → B → C → D) → Signal A → Signal B → Signal C → Signal D
liftA3 f sa sb sc = liftA2 f sa sb <*> sc

------------------------------------------------------------------------
-- Временные комбинаторы
------------------------------------------------------------------------

-- Задержка на один такт (pre с начальным значением)
pre : A → Signal A → Signal A
now  (pre a s) = a
next (pre a s) = pre (now s) (next s)

-- Сдвиг назад (delay)
delay : A → Signal A → Signal A
delay = pre

-- Zip двух сигналов
zipS : Signal A → Signal B → Signal (A × B)
zipS sa sb = liftA2 _,_ sa sb

-- Scan (foldl через время)
scanS : (B → A → B) → B → Signal A → Signal B
now  (scanS f b s) = b
next (scanS f b s) = scanS f (f b (now s)) (next s)

------------------------------------------------------------------------
-- Выборка значений
------------------------------------------------------------------------

-- Взять n значений из сигнала (для отладки)
takeS : ℕ → Signal A → List A
takeS zero    s = []
takeS (suc n) s = now s ∷ takeS n (next s)

-- Пропустить n значений
dropS : ℕ → Signal A → Signal A
dropS zero    s = s
dropS (suc n) s = dropS n (next s)

------------------------------------------------------------------------
-- Комбинирование
------------------------------------------------------------------------

-- Выбор между двумя сигналами по условию
switch : Signal Bool → Signal A → Signal A → Signal A
now  (switch c t f) = if now c then now t else now f
next (switch c t f) = switch (next c) (next t) (next f)

-- Слияние с предпочтением первого
merge : Signal (Maybe A) → Signal (Maybe A) → Signal (Maybe A)
now (merge s₁ s₂) with now s₁
... | just a  = just a
... | nothing = now s₂
next (merge s₁ s₂) = merge (next s₁) (next s₂)

------------------------------------------------------------------------
-- Интеграция с полиномами
------------------------------------------------------------------------

-- Signal A как коалгебра полинома Mono A ⊤:
--   State   = Signal A
--   observe = now  : Signal A → A
--   update  = λ s _ → next s : Signal A → ⊤ → Signal A
--
-- Структура record Signal напрямую реализует эту коалгебру:
--   now  соответствует observe
--   next соответствует update (с тривиальным аргументом ⊤)

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Индексация по времени
_!!_ : Signal A → ℕ → A
s !! zero    = now s
s !! suc n   = next s !! n

infixl 9 _!!_

-- Сравнение с предыдущим значением
changed : {A : Set} → (A → A → Bool) → Signal A → Signal Bool
now  (changed eq s) = false  -- В первый момент нет предыдущего
next (changed eq s) = changed' eq (now s) (next s)
  where
    changed' : (A → A → Bool) → A → Signal A → Signal Bool
    now  (changed' eq prev s) = if eq prev (now s) then false else true
    next (changed' eq prev s) = changed' eq (now s) (next s)

-- Создание счётчика (вызывать с начальным значением)
-- Примечание: не определяем глобальный counter, так как JS backend
-- вычисляет его сразу (eager), что вызывает бесконечную рекурсию.
-- Используй: mkCounter 0 там, где нужен счётчик.
mkCounter : ℕ → Signal ℕ
now  (mkCounter n) = n
next (mkCounter n) = mkCounter (suc n)
