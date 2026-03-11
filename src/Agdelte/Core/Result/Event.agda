{-# OPTIONS --without-K #-}

-- Result.Event: Event combinators for Result
-- Separated from Result.agda so that importing Result doesn't pull in Event.

module Agdelte.Core.Result.Event where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Result using (Result; ok; err)
open import Agdelte.Core.Event using (Event; mapFilterE)

private
  variable
    A E : Set

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
-- NOTE: creates two mapFilterE subscriptions on the same event source.
-- At runtime, this means the event fires handlers twice per occurrence.
-- Acceptable for httpGet/httpPost results (low-frequency), but could be
-- an issue for high-frequency events. A native partition constructor
-- with a single runtime subscription would eliminate the duplication.
--
-- For high-frequency events, prefer using mapFilterE with a single handler:
--   handleResult : Event (Result E A) → Event Msg
--   handleResult e = mapFilterE (λ { (ok a) → just (GotOk a)
--                                   ; (err e) → just (GotErr e) }) e
partitionResult : Event (Result E A) → Event A × Event E
partitionResult e = (filterOk e , filterErr e)
