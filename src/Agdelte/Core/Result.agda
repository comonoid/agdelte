{-# OPTIONS --without-K #-}

-- Result: error handling for events
-- Provides Result E A type and Event combinators for filtering ok/err

module Agdelte.Core.Result where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Event using (Event; mapFilterE)

private
  variable
    A E : Set

------------------------------------------------------------------------
-- Result type
------------------------------------------------------------------------

data Result (E A : Set) : Set where
  ok  : A → Result E A
  err : E → Result E A

------------------------------------------------------------------------
-- Event combinators for Result
------------------------------------------------------------------------

-- Extract only successes
filterOk : Event (Result E A) → Event A
filterOk = mapFilterE λ where
  (ok a)  → just a
  (err _) → nothing

-- Extract only errors
filterErr : Event (Result E A) → Event E
filterErr = mapFilterE λ where
  (ok _)  → nothing
  (err e) → just e

-- Split into (successes, errors)
partitionResult : Event (Result E A) → Event A × Event E
partitionResult e = (filterOk e , filterErr e)
