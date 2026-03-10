{-# OPTIONS --without-K #-}

-- Result: error handling type
-- Pure Result E A type with no external dependencies.
--
-- Event combinators (filterOk, filterErr, partitionResult) are in
-- Agdelte.Core.Result.Event to avoid pulling in Event for code
-- that only needs the Result type.

module Agdelte.Core.Result where

private
  variable
    A E : Set

------------------------------------------------------------------------
-- Result type
------------------------------------------------------------------------

data Result (E A : Set) : Set where
  ok  : A → Result E A
  err : E → Result E A
