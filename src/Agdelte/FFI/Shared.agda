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
    encode : A → String        -- to wire format (plain text; identity for String)
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
-- SharedArrayBuffer (opaque handle)
------------------------------------------------------------------------

-- At JS level: SharedArrayBuffer object passed to/from workers
-- At Agda level: opaque type, used by Event constructors (allocShared, workerShared)
postulate SharedBuffer : Set
{-# COMPILE JS SharedBuffer = function(x) { return x; } #-}

------------------------------------------------------------------------
-- Re-export Result for cross-process operations
-- NOTE: Result is NOT re-exported here to avoid a cyclic dependency:
--   Event → Shared → Result → Event
-- Import Agdelte.Core.Result directly instead.
------------------------------------------------------------------------
