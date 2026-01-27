{-# OPTIONS --without-K --guardedness #-}

-- PolySignal: явная связь между Signal и Polynomial Functors
-- Демонстрирует, что Signal A ≅ Coalg (Mono A ⊤)

module Agdelte.Core.PolySignal where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_; id)

open import Agdelte.Core.Poly
open import Agdelte.Core.Signal

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Signal как коалгебра полинома Mono A ⊤
------------------------------------------------------------------------

-- Полином для Signal A
-- Pos = A (наблюдаемое значение)
-- Dir = λ _ → ⊤ (тривиальный вход для перехода)
SignalPoly : Set → Poly
SignalPoly A = Mono A ⊤

-- Проверка: интерпретация SignalPoly даёт A × X
-- ⟦SignalPoly A⟧ X = Σ A (λ _ → ⊤ → X) ≅ A × X

------------------------------------------------------------------------
-- Преобразование Signal в Coalg
------------------------------------------------------------------------

-- Signal A можно рассматривать как коалгебру SignalPoly A
-- где State = Signal A
signalToCoalg : ∀ {A} → Coalg (SignalPoly A)
signalToCoalg {A} = mkCoalg
  (Signal A)           -- State
  now                  -- observe : Signal A → A
  (λ s _ → next s)     -- update  : Signal A → ⊤ → Signal A

------------------------------------------------------------------------
-- Операции на Signal через Poly
------------------------------------------------------------------------

-- map для Signal через mapPoly
-- Это показывает, что mapS соответствует функториальности полинома
mapS-via-Poly : ∀ {A B : Set} → (A → B) → Signal A → Signal B
mapS-via-Poly {A} {B} f s = go s
  where
    go : Signal A → Signal B
    now  (go s') = f (now s')
    next (go s') = go (next s')

-- Линза между SignalPoly A и SignalPoly B индуцируется функцией A → B
signalLens : (A → B) → Lens (SignalPoly A) (SignalPoly B)
signalLens f = mkLens f (λ _ _ → tt)

------------------------------------------------------------------------
-- Константный сигнал как коалгебра
------------------------------------------------------------------------

-- Константный сигнал — это коалгебра с одноточечным состоянием
constSignalCoalg : A → Coalg (SignalPoly A)
constSignalCoalg a = mkCoalg
  ⊤                    -- State = ⊤ (одно состояние)
  (λ _ → a)            -- observe : ⊤ → A
  (λ _ _ → tt)         -- update  : ⊤ → ⊤ → ⊤

-- Разворачивание коалгебры в Signal
unfoldSignal : ∀ {S : Set} {A : Set} → (S → A) → (S → S) → S → Signal A
now  (unfoldSignal {S} {A} obs step s) = obs s
next (unfoldSignal {S} {A} obs step s) = unfoldSignal {S} {A} obs step (step s)

-- Любая коалгебра SignalPoly A разворачивается в Signal A
coalgToSignal : ∀ {A} → (c : Coalg (SignalPoly A)) → State c → Signal A
coalgToSignal {A} c s₀ = unfoldSignal {State c} {A} (observe c) (λ s → update c s tt) s₀

------------------------------------------------------------------------
-- Изоморфизм между Signal и Coalg (неформально)
------------------------------------------------------------------------

-- Формально, Signal A и Coalg (SignalPoly A) с State = Signal A
-- образуют эквивалентные структуры. Функции now/next напрямую
-- соответствуют observe/update.

-- Signal → Coalg → Signal должен давать исходный сигнал:
-- coalgToSignal signalToCoalg s ≡ s  (требует bisimilarity)

