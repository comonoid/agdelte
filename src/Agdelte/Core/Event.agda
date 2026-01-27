{-# OPTIONS --without-K --guardedness #-}

-- Event: дискретные события во времени
-- Event A = Signal (List A) — список событий на каждом такте

module Agdelte.Core.Event where

open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ;
                             foldl; length; null; head; reverse)
open import Data.List.NonEmpty using (List⁺; _∷_; toList) renaming (map to map⁺)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _∸_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; const; _$_)

open import Agdelte.Core.Signal hiding (merge; delay)

private
  variable
    A B C : Set

------------------------------------------------------------------------
-- Event = Signal (List A)
------------------------------------------------------------------------

Event : Set → Set
Event A = Signal (List A)

------------------------------------------------------------------------
-- Базовые конструкторы
------------------------------------------------------------------------

-- Никогда не происходит
never : Event A
now  never = []
next never = never

-- Одиночное событие в момент 0
once : A → Event A
now  (once a) = a ∷ []
next (once a) = never

-- Множественные события в момент 0
emit : List A → Event A
now  (emit as) = as
next (emit as) = never

------------------------------------------------------------------------
-- Functor для Event
------------------------------------------------------------------------

mapE : (A → B) → Event A → Event B
mapE f = mapS (map f)

-- Инфиксная версия
_<$ᴱ>_ : (A → B) → Event A → Event B
_<$ᴱ>_ = mapE

infixl 4 _<$ᴱ>_

------------------------------------------------------------------------
-- Фильтрация
------------------------------------------------------------------------

-- Фильтр по предикату
filterE : (A → Bool) → Event A → Event A
filterE p = mapS (filterᵇ p)

-- Фильтр с Maybe
filterMapE : (A → Maybe B) → Event A → Event B
filterMapE f = mapS (concat ∘ map (maybe (_∷ []) []) ∘ map f)

-- Взять только Just
justs : Event (Maybe A) → Event A
justs = filterMapE id

-- Фильтр по типу (через Either)
lefts : Event (A ⊎ B) → Event A
lefts = filterMapE (λ { (inj₁ a) → just a ; (inj₂ _) → nothing })

rights : Event (A ⊎ B) → Event B
rights = filterMapE (λ { (inj₁ _) → nothing ; (inj₂ b) → just b })

------------------------------------------------------------------------
-- Комбинирование событий
------------------------------------------------------------------------

-- Слияние двух потоков событий (все события с обоих)
merge : Event A → Event A → Event A
now  (merge e₁ e₂) = now e₁ ++ now e₂
next (merge e₁ e₂) = merge (next e₁) (next e₂)

-- Слияние списка потоков
mergeAll : List (Event A) → Event A
mergeAll [] = never
mergeAll (e ∷ es) = merge e (mergeAll es)

-- Левое предпочтение (только первый, если оба)
leftmost : Event A → Event A → Event A
now  (leftmost e₁ e₂) = if null (now e₁) then now e₂ else now e₁
next (leftmost e₁ e₂) = leftmost (next e₁) (next e₂)

-- Тег событий (для различения источников)
tagLeft : Event A → Event (A ⊎ B)
tagLeft = mapE inj₁

tagRight : Event B → Event (A ⊎ B)
tagRight = mapE inj₂

-- Объединение с тегами
eitherE : Event A → Event B → Event (A ⊎ B)
eitherE ea eb = merge (tagLeft ea) (tagRight eb)

------------------------------------------------------------------------
-- Аккумуляторы и состояние
------------------------------------------------------------------------

-- Свёртка через время (foldp в Elm)
-- Семантика: события обрабатываются в порядке поступления (слева направо)
-- foldl f z [a,b,c] = f (f (f z a) b) c
foldE : (B → A → B) → B → Event A → Signal B
now  (foldE f b e) = foldl f b (now e)
next (foldE f b e) = foldE f (foldl f b (now e)) (next e)

-- Аккумулятор (accumE) — применяет функции-события к состоянию
accumE : B → Event (B → B) → Signal B
accumE = foldE (λ b f → f b)

-- Подсчёт событий
count : Event A → Signal ℕ
count = foldE (λ n _ → suc n) zero

-- Собрать все события в список (в порядке поступления)
collect : Event A → Signal (List A)
collect = foldE (λ as a → as ++ (a ∷ [])) []

-- Последнее событие (или начальное значение)
stepper : A → Event A → Signal A
stepper a = foldE (λ _ x → x) a

-- hold — синоним stepper
hold : A → Event A → Signal A
hold = stepper

------------------------------------------------------------------------
-- Временные комбинаторы
------------------------------------------------------------------------

-- Задержка событий на один такт
delay : Event A → Event A
now  (delay e) = []
next (delay e) = delay' (now e) (next e)
  where
    delay' : List A → Event A → Event A
    now  (delay' prev e) = prev
    next (delay' prev e) = delay' (now e) (next e)

-- Первое событие в потоке
first : Event A → Event A
first e = mapS (λ { [] → [] ; (a ∷ _) → a ∷ [] }) e

-- Только первое событие за всё время
-- ПРИМЕЧАНИЕ: требует sized types для корректного termination checking
-- firstEver : Event A → Event A

-- Пропустить первые n событий
-- ПРИМЕЧАНИЕ: требует sized types для корректного termination checking
-- dropE : ℕ → Event A → Event A

-- Взять первые n событий
-- ПРИМЕЧАНИЕ: требует sized types для корректного termination checking
-- takeE : ℕ → Event A → Event A

------------------------------------------------------------------------
-- Связь Signal и Event
------------------------------------------------------------------------

-- Выборка значения сигнала при событии
snapshot : Event A → Signal B → Event (A × B)
now  (snapshot e s) = map (_, now s) (now e)
next (snapshot e s) = snapshot (next e) (next s)

-- Выборка с функцией
snapshotWith : (A → B → C) → Event A → Signal B → Event C
snapshotWith f e s = mapE (λ { (a , b) → f a b }) (snapshot e s)

-- Замена значения события на значение сигнала
tag : Event A → Signal B → Event B
tag e s = snapshotWith (λ _ b → b) e s

-- Пропускать события когда сигнал false
gate : Event A → Signal Bool → Event A
now  (gate e g) = if now g then now e else []
next (gate e g) = gate (next e) (next g)

-- whenE — синоним gate
whenE : Signal Bool → Event A → Event A
whenE g e = gate e g

------------------------------------------------------------------------
-- Переключение
------------------------------------------------------------------------

-- Переключиться на новый поток при событии
switchE : Event A → Event (Event A) → Event A
now  (switchE e ee) with now ee
... | []       = now e
... | (e' ∷ _) = now e'
next (switchE e ee) with now ee
... | []       = switchE (next e) (next ee)
... | (e' ∷ _) = switchE (next e') (next ee)

-- Flatten: Event (Event A) → Event A
flatten : Event (Event A) → Event A
flatten = switchE never

------------------------------------------------------------------------
-- Debounce / Throttle (требуют внешнего времени)
------------------------------------------------------------------------

-- Эти комбинаторы реализуются через FFI в Primitive модулях
-- Здесь только типы для документации

-- debounce : ℕ → Event A → Event A  -- Подождать тишины
-- throttle : ℕ → Event A → Event A  -- Ограничить частоту

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Проверка наличия событий на текущем такте
hasEvents : Event A → Signal Bool
hasEvents = mapS (not ∘ null)

-- Количество событий на текущем такте
eventCount : Event A → Signal ℕ
eventCount = mapS length

-- Преобразование в Maybe (берём первое событие)
toMaybe : Event A → Signal (Maybe A)
toMaybe = mapS (λ { [] → nothing ; (a ∷ _) → just a })

-- Из Maybe в Event
fromMaybe : Signal (Maybe A) → Event A
fromMaybe = mapS (maybe (_∷ []) [])

-- Константное событие при изменении сигнала
changes : {A : Set} → (A → A → Bool) → Signal A → Event A
changes eq s = gate (mapS (_∷ []) s) (changed eq s)

-- Дублировать каждое событие
duplicate : Event A → Event A
duplicate = mapS (concat ∘ map (λ a → a ∷ a ∷ []))

-- Разбить на пары
pairs : Event A → Event (A × A)
pairs e = zipE e (delay e)
  where
    zipE : Event A → Event A → Event (A × A)
    now  (zipE e₁ e₂) = zip' (now e₁) (now e₂)
      where
        zip' : List A → List A → List (A × A)
        zip' [] _ = []
        zip' _ [] = []
        zip' (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip' xs ys
    next (zipE e₁ e₂) = zipE (next e₁) (next e₂)
