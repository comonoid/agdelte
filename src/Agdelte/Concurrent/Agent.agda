{-# OPTIONS --without-K --guardedness #-}

-- Agent: polynomial coalgebra for concurrent processes
-- Pure Agda — compiles to both JS and Haskell backends

module Agdelte.Concurrent.Agent where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Agent as coalgebra of polynomial functor p(y) = S × (I → S)
-- State S, Input I, Output O
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O
    step    : S → I → S

open Agent public

-- Create an Agent from initial state, observer, and step function
mkAgent : ∀ {S I O} → S → (S → O) → (S → I → S) → Agent S I O
mkAgent s obs stp = record { state = s ; observe = obs ; step = stp }

-- Run one step: apply input, return new agent and output
stepAgent : ∀ {S I O} → Agent S I O → I → Agent S I O × O
stepAgent a i =
  let s' = step a (state a) i
      a' = record a { state = s' }
  in a' , observe a s'

-- Map output
mapObserve : ∀ {S I O O'} → (O → O') → Agent S I O → Agent S I O'
mapObserve f a = record
  { state   = state a
  ; observe = λ s → f (observe a s)
  ; step    = step a
  }

-- Map input (contravariant)
mapInput : ∀ {S I I' O} → (I' → I) → Agent S I O → Agent S I' O
mapInput f a = record
  { state   = state a
  ; observe = observe a
  ; step    = λ s i' → step a s (f i')
  }
