{-# OPTIONS --without-K #-}

-- Shared FFI types: platform-agnostic interfaces for cross-process communication
-- Used by both Browser (JS) and Server (Haskell) backends

module Agdelte.FFI.Shared where

open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)

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
    ; decode = λ s → just s
    }

-- Bool: "true" / "false"
instance
  serializeBool : Serialize Bool
  serializeBool = record
    { encode = λ { true → "true" ; false → "false" }
    ; decode = λ { "true" → just true ; "false" → just false ; _ → nothing }
    }

-- ℕ: decimal string
postulate
  readℕ : String → Maybe ℕ
{-# COMPILE JS readℕ = function(s) {
  const n = parseInt(s, 10);
  if (Number.isNaN(n) || n < 0) return (cb) => cb.nothing();
  return (cb) => cb.just(BigInt(n));
} #-}

instance
  serializeNat : Serialize ℕ
  serializeNat = record
    { encode = showℕ
    ; decode = readℕ
    }

-- String helpers for tagged serialization
-- Pure Agda implementations (work on both JS and GHC backends).
-- JS backend overrides with native for performance.

open import Data.String using (toList; fromList) renaming (length to strLength)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (drop) renaming (length to listLength)

private
  isPrefixOfChars : List Char → List Char → Bool
  isPrefixOfChars [] _ = true
  isPrefixOfChars _ [] = false
  isPrefixOfChars (p ∷ ps) (c ∷ cs) =
    if p ≈ᵇ c then isPrefixOfChars ps cs else false

startsWith : String → String → Bool
startsWith prefix s = isPrefixOfChars (toList prefix) (toList s)

dropPrefix : ℕ → String → String
dropPrefix n s = fromList (drop n (toList s))

-- Maybe A: "just:<encoded>" / "nothing"
instance
  serializeMaybe : ∀ {A} → {{Serialize A}} → Serialize (Maybe A)
  serializeMaybe {A} {{sA}} = record
    { encode = λ { (just a) → "just:" ++ encode a ; nothing → "nothing" }
    ; decode = decodeMaybe
    }
    where
      decodeMaybe : String → Maybe (Maybe A)
      decodeMaybe "nothing" = just nothing
      decodeMaybe s with startsWith "just:" s
      ... | true  with decode (dropPrefix 5 s)
      ...   | just a  = just (just a)
      ...   | nothing = nothing
      decodeMaybe s | false = nothing

-- List A: length-prefixed format "len1:payload1len2:payload2..."
-- Empty list: ""
-- Safe for any payload content (no delimiter conflicts).
postulate
  encodeListLP : (A → String) → List A → String
  decodeListLP : (String → Maybe A) → String → Maybe (List A)
{-# COMPILE JS encodeListLP = function(_) { return function(enc) { return function(xs) {
  const arr = []; let cur = xs; let done = false;
  while (!done) { cur({ '[]': () => { done = true; }, '_∷_': (h, t) => { arr.push(h); cur = t; } }); }
  return arr.map(a => { const s = enc(a); return s.length + ':' + s; }).join('');
}; }; } #-}
{-# COMPILE JS decodeListLP = function(_) { return function(dec) { return function(s) {
  if (s === '') return (cb) => cb.just((c) => c['[]']());
  const items = []; let pos = 0;
  while (pos < s.length) {
    const colon = s.indexOf(':', pos);
    if (colon === -1) return (cb) => cb.nothing();
    const len = parseInt(s.slice(pos, colon), 10);
    if (Number.isNaN(len) || len < 0) return (cb) => cb.nothing();
    const start = colon + 1;
    if (start + len > s.length) return (cb) => cb.nothing();
    items.push(s.slice(start, start + len));
    pos = start + len;
  }
  const decoded = [];
  for (const item of items) {
    const r = dec(item); let ok = false; let val;
    r({ just: (v) => { ok = true; val = v; }, nothing: () => {} });
    if (!ok) return (cb) => cb.nothing();
    decoded.push(val);
  }
  let result = (c) => c['[]']();
  for (let i = decoded.length - 1; i >= 0; i--) {
    const head = decoded[i]; const tail = result;
    result = (c) => c['_∷_'](head, tail);
  }
  return (cb) => cb.just(result);
}; }; } #-}

instance
  serializeList : ∀ {A} → {{Serialize A}} → Serialize (List A)
  serializeList {A} {{sA}} = record
    { encode = encodeListLP (Serialize.encode sA)
    ; decode = decodeListLP (Serialize.decode sA)
    }

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

-- Result E A: "ok:<encoded>" / "err:<encoded>"
-- Requires Serialize for both E and A
open import Agdelte.Core.Result using (Result; ok; err)

instance
  serializeResult : ∀ {E A} → {{Serialize E}} → {{Serialize A}} → Serialize (Result E A)
  serializeResult {E} {A} {{sE}} {{sA}} = record
    { encode = λ { (ok a) → "ok:" ++ encode a ; (err e) → "err:" ++ encode e }
    ; decode = decodeResult
    }
    where
      decodeResult : String → Maybe (Result E A)
      decodeResult s with startsWith "ok:" s
      ... | true  with decode {{sA}} (dropPrefix 3 s)
      ...   | just a  = just (ok a)
      ...   | nothing = nothing
      decodeResult s | false with startsWith "err:" s
      ... | true  with decode {{sE}} (dropPrefix 4 s)
      ...   | just e  = just (err e)
      ...   | nothing = nothing
      decodeResult s | false | false = nothing

------------------------------------------------------------------------
