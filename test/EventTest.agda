{-# OPTIONS --without-K --guardedness #-}

-- EventTest: тесты для Event комбинаторов

module EventTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Core.Signal
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Базовые тесты
------------------------------------------------------------------------

-- never не генерирует событий
test-never : ∀ {A : Set} → now (never {A}) ≡ []
test-never = refl

-- once генерирует одно событие
test-once : now (once 42) ≡ (42 ∷ [])
test-once = refl

-- mapE сохраняет структуру
test-mapE : now (mapE suc (once 0)) ≡ (1 ∷ [])
test-mapE = refl

------------------------------------------------------------------------
-- Тесты merge
------------------------------------------------------------------------

-- merge объединяет события
test-merge : now (merge (once 1) (once 2)) ≡ (1 ∷ 2 ∷ [])
test-merge = refl

-- merge с never
test-merge-never : now (merge (once 1) never) ≡ (1 ∷ [])
test-merge-never = refl

------------------------------------------------------------------------
-- Тесты filter
------------------------------------------------------------------------

-- filterE
isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

test-filterE : now (filterE isEven (emit (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))
             ≡ (0 ∷ 2 ∷ 4 ∷ [])
test-filterE = refl

------------------------------------------------------------------------
-- Тесты fold
------------------------------------------------------------------------

-- foldE аккумулирует
test-foldE-now : now (foldE _+_ 0 (emit (1 ∷ 2 ∷ 3 ∷ []))) ≡ 6
test-foldE-now = refl

-- count считает события
test-count : now (count (emit (1 ∷ 2 ∷ 3 ∷ []))) ≡ 3
test-count = refl

------------------------------------------------------------------------
-- Тесты snapshot
------------------------------------------------------------------------

-- snapshot комбинирует
test-snapshot : now (snapshot (once 1) (constant 10)) ≡ ((1 , 10) ∷ [])
test-snapshot = refl

------------------------------------------------------------------------
-- Тесты gate
------------------------------------------------------------------------

-- gate пропускает при true
test-gate-true : now (gate (once 1) (constant true)) ≡ (1 ∷ [])
test-gate-true = refl

-- gate блокирует при false
test-gate-false : now (gate (once 1) (constant false)) ≡ []
test-gate-false = refl

------------------------------------------------------------------------
-- Тесты Signal
------------------------------------------------------------------------

-- constant всегда возвращает значение
test-constant : now (constant 42) ≡ 42
test-constant = refl

-- mapS применяет функцию
test-mapS : now (mapS suc (constant 0)) ≡ 1
test-mapS = refl

-- Applicative
test-applicative : now (pure suc <*> constant 0) ≡ 1
test-applicative = refl

-- pre задерживает
test-pre : now (pre 0 (constant 1)) ≡ 0
test-pre = refl

------------------------------------------------------------------------
-- Все тесты прошли если модуль компилируется!
------------------------------------------------------------------------

allTestsPassed : Bool
allTestsPassed = true
