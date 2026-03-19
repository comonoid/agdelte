{-# OPTIONS --without-K #-}

-- Higher-level combinators and sequential composition for Event.
-- Re-exported by Agdelte.Core.Event for backward compatibility.

module Agdelte.Core.Event.Combinators where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)

open import Agdelte.Core.Event.Core using
  ( Event; never; merge; mapE; filterE; foldE; mapFilterE; switchE
  ; parallel; race; timeout
  )

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------

mergeAll : List (Event A) → Event A
mergeAll [] = never
mergeAll (e ∷ es) = merge e (mergeAll es)

_<|>_ : Event A → Event A → Event A
_<|>_ = merge

infixr 3 _<|>_

_<$>_ : (A → B) → Event A → Event B
_<$>_ = mapE

infixl 4 _<$>_

------------------------------------------------------------------------
-- Stateful combinators
------------------------------------------------------------------------

accumE : A → Event (A → A) → Event A
accumE a₀ e = foldE a₀ (λ f a → f a) e

mapAccum : ∀ {S : Set} → (B → S → S × A) → S → Event B → Event A
mapAccum step s₀ e = mapFilterE proj (foldE (s₀ , nothing) step' e)
  where
    open Data.Product using (proj₂)
    step' : _ → _ → _
    step' b (s , _) with step b s
    ... | (s' , a) = (s' , just a)
    proj : _ → Maybe _
    proj (_ , ma) = ma

gate : (A → Bool) → Event A → Event A
gate = filterE

partitionE : (A → Bool) → Event A → Event A × Event A
partitionE p e = (filterE p e , filterE (not ∘ p) e)

leftmost : List (Event A) → Event A
leftmost = mergeAll

------------------------------------------------------------------------
-- Concurrency combinators
------------------------------------------------------------------------

parallelAll : List (Event A) → Event (List A)
parallelAll es = parallel es id

raceTimeout : ℕ → A → Event A → Event A
raceTimeout ms fallback e = race (e ∷ timeout ms fallback ∷ [])

------------------------------------------------------------------------
-- Periodic events
------------------------------------------------------------------------

open import Agdelte.Core.Event.Core using (interval)

everySecond : A → Event A
everySecond msg = interval 1000 msg

everyMinute : A → Event A
everyMinute msg = interval 60000 msg

------------------------------------------------------------------------
-- Sequential / monadic combinators
------------------------------------------------------------------------

occur : A → Event A
occur a = timeout 0 a

delay : ℕ → Event ⊤
delay ms = timeout ms tt

infixl 1 _>>=E_

_>>=E_ : Event A → (A → Event B) → Event B
e >>=E f = switchE never (mapE f e)

sequenceE : List (Event A) → Event (List A)
sequenceE []       = occur []
sequenceE (e ∷ es) = e >>=E λ a → mapE (a ∷_) (sequenceE es)
