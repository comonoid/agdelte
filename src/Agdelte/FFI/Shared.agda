{-# OPTIONS --without-K #-}

-- Shared FFI types: platform-agnostic interfaces for cross-process communication
-- Used by both Browser (JS) and Server (Haskell) backends

module Agdelte.FFI.Shared where

open import Data.String using (String)
open import Data.Maybe using (Maybe)

private
  variable
    A E : Set

------------------------------------------------------------------------
-- Serialize: encode/decode for cross-process/cross-host communication
------------------------------------------------------------------------

record Serialize (A : Set) : Set where
  field
    encode : A → String        -- to wire format (JSON)
    decode : String → Maybe A   -- from wire format (may fail)

open Serialize {{...}} public

------------------------------------------------------------------------
-- Primitive instances
------------------------------------------------------------------------

-- String is trivially serializable (identity)
instance
  serializeString : Serialize String
  serializeString = record
    { encode = λ s → s
    ; decode = λ s → Maybe.just s
    }
    where import Data.Maybe as Maybe

------------------------------------------------------------------------
-- Protocol: message envelope for cross-process communication
------------------------------------------------------------------------

-- Wire message with type tag for routing
record Envelope : Set where
  constructor mkEnvelope
  field
    tag     : String    -- message type / agent path
    payload : String    -- serialized content

open Envelope public

------------------------------------------------------------------------
-- Result type for cross-process operations
------------------------------------------------------------------------

data TransportResult (A : Set) : Set where
  success : A → TransportResult A
  failure : String → TransportResult A

mapTransport : ∀ {A B : Set} → (A → B) → TransportResult A → TransportResult B
mapTransport f (success a) = success (f a)
mapTransport f (failure e) = failure e
