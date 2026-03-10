{-# OPTIONS --without-K #-}

-- JSON Encoding and Decoding for Agdelte
-- Provides type-safe JSON parsing and generation

module Agdelte.Json where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)
open import Data.Float using (Float)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

open import Agdelte.Data.Array using (Array)
open import Agdelte.Core.Result using (Result; ok; err)

------------------------------------------------------------------------
-- JSON Value type
------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data JsonValue : Set where
  jNull   : JsonValue
  jBool   : Bool → JsonValue
  jNumber : ℕ → JsonValue      -- natural numbers
  jFloat  : Float → JsonValue  -- float (covers negative and fractional)
  jString : String → JsonValue
  jArray  : Array JsonValue → JsonValue
  jObject : Array (String × JsonValue) → JsonValue

------------------------------------------------------------------------
-- Decoder type (applicative functor)
------------------------------------------------------------------------

-- A Decoder A describes how to extract an A from a JsonValue
postulate
  Decoder : Set → Set

{-# COMPILE JS Decoder = function(x) { return x; } #-}

------------------------------------------------------------------------
-- Primitive decoders
------------------------------------------------------------------------

postulate
  -- Decode a string
  string : Decoder String

  -- Decode a natural number
  nat : Decoder ℕ

  -- Decode an integer (as JS number)
  int : Decoder ℤ

  -- Decode a float
  float : Decoder Float

  -- Decode a boolean
  bool : Decoder Bool

  -- Decode null (returns unit)
  jnull : Decoder ⊤

{-# COMPILE JS string = {
  decode: (json) => {
    if (typeof json === 'string') return { tag: 'ok', value: json };
    return { tag: 'err', error: 'Expected string, got ' + typeof json };
  }
} #-}

{-# COMPILE JS nat = {
  decode: (json) => {
    if (typeof json === 'number' && Number.isInteger(json) && json >= 0) {
      return { tag: 'ok', value: BigInt(json) };
    }
    return { tag: 'err', error: 'Expected natural number, got ' + typeof json };
  }
} #-}

{-# COMPILE JS int = {
  decode: (json) => {
    if (typeof json === 'number' && Number.isInteger(json)) {
      const n = BigInt(json);
      const value = n >= 0n
        ? (cases) => cases["+_"](n)
        : (cases) => cases["-[1+_]"](-n - 1n);
      return { tag: 'ok', value };
    }
    return { tag: 'err', error: 'Expected integer, got ' + typeof json };
  }
} #-}

{-# COMPILE JS float = {
  decode: (json) => {
    if (typeof json === 'number') {
      return { tag: 'ok', value: json };
    }
    return { tag: 'err', error: 'Expected number, got ' + typeof json };
  }
} #-}

{-# COMPILE JS bool = {
  decode: (json) => {
    if (typeof json === 'boolean') {
      const value = json
        ? (cases) => cases["true"]()
        : (cases) => cases["false"]();
      return { tag: 'ok', value };
    }
    return { tag: 'err', error: 'Expected boolean, got ' + typeof json };
  }
} #-}

{-# COMPILE JS jnull = {
  decode: (json) => {
    if (json === null) return { tag: 'ok', value: (cases) => cases["tt"]() };
    return { tag: 'err', error: 'Expected null' };
  }
} #-}

------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------

postulate
  -- Decode a field from an object
  field′ : ∀ {A : Set} → String → Decoder A → Decoder A

  -- Optional field (returns Maybe)
  optionalField : ∀ {A : Set} → String → Decoder A → Decoder (Maybe A)

  -- Field with default value
  fieldWithDefault : ∀ {A : Set} → String → A → Decoder A → Decoder A

  -- Decode an array
  array : ∀ {A : Set} → Decoder A → Decoder (Array A)

  -- Decode a list
  list : ∀ {A : Set} → Decoder A → Decoder (List A)

  -- Decode nullable value
  nullable : ∀ {A : Set} → Decoder A → Decoder (Maybe A)

  -- Index into array
  index : ∀ {A : Set} → ℕ → Decoder A → Decoder A

{-# COMPILE JS field′ = function(name) { return function(decoder) {
  return {
    decode: (json) => {
      if (typeof json !== 'object' || json === null) {
        return { tag: 'err', error: 'Expected object for field "' + name + '"' };
      }
      if (!(name in json)) {
        return { tag: 'err', error: 'Missing field "' + name + '"' };
      }
      return decoder.decode(json[name]);
    }
  };
}; } #-}

{-# COMPILE JS optionalField = function(name) { return function(decoder) {
  return {
    decode: (json) => {
      if (typeof json !== 'object' || json === null) {
        return { tag: 'ok', value: a => a["nothing"]() };
      }
      if (!(name in json) || json[name] === null || json[name] === undefined) {
        return { tag: 'ok', value: a => a["nothing"]() };
      }
      const result = decoder.decode(json[name]);
      if (result.tag === 'ok') {
        return { tag: 'ok', value: a => a["just"](result.value) };
      }
      return result;
    }
  };
}; } #-}

{-# COMPILE JS fieldWithDefault = function(name) { return function(def) { return function(decoder) {
  return {
    decode: (json) => {
      if (typeof json !== 'object' || json === null || !(name in json)) {
        return { tag: 'ok', value: def };
      }
      const result = decoder.decode(json[name]);
      if (result.tag === 'ok') return result;
      return { tag: 'ok', value: def };
    }
  };
}; }; } #-}

{-# COMPILE JS array = function(decoder) {
  return {
    decode: (json) => {
      if (!Array.isArray(json)) {
        return { tag: 'err', error: 'Expected array, got ' + typeof json };
      }
      const results = [];
      for (let i = 0; i < json.length; i++) {
        const r = decoder.decode(json[i]);
        if (r.tag === 'err') {
          return { tag: 'err', error: 'At index ' + i + ': ' + r.error };
        }
        results.push(r.value);
      }
      return { tag: 'ok', value: results };
    }
  };
} #-}

{-# COMPILE JS list = function(decoder) {
  return {
    decode: (json) => {
      if (!Array.isArray(json)) {
        return { tag: 'err', error: 'Expected array, got ' + typeof json };
      }
      const results = [];
      for (let i = 0; i < json.length; i++) {
        const r = decoder.decode(json[i]);
        if (r.tag === 'err') {
          return { tag: 'err', error: 'At index ' + i + ': ' + r.error };
        }
        results.push(r.value);
      }
      let agdaList = (cases) => cases['[]']();
      for (let i = results.length - 1; i >= 0; i--) {
        const elem = results[i];
        const tail = agdaList;
        agdaList = (cases) => cases['_∷_'](elem, tail);
      }
      return { tag: 'ok', value: agdaList };
    }
  };
} #-}

{-# COMPILE JS nullable = function(decoder) {
  return {
    decode: (json) => {
      if (json === null || json === undefined) {
        return { tag: 'ok', value: a => a["nothing"]() };
      }
      const result = decoder.decode(json);
      if (result.tag === 'ok') {
        return { tag: 'ok', value: a => a["just"](result.value) };
      }
      return result;
    }
  };
} #-}

{-# COMPILE JS index = function(i) { return function(decoder) {
  return {
    decode: (json) => {
      if (!Array.isArray(json)) {
        return { tag: 'err', error: 'Expected array' };
      }
      const idx = Number(i);
      if (idx >= json.length) {
        return { tag: 'err', error: 'Index ' + idx + ' out of bounds (length ' + json.length + ')' };
      }
      return decoder.decode(json[idx]);
    }
  };
}; } #-}

------------------------------------------------------------------------
-- Functor / Applicative / Monad
------------------------------------------------------------------------

postulate
  -- Map over decoder result
  mapDecoder : ∀ {A B : Set} → (A → B) → Decoder A → Decoder B

  -- Pure value (always succeeds)
  succeed : ∀ {A : Set} → A → Decoder A

  -- Always fail with message
  fail : ∀ {A : Set} → String → Decoder A

  -- Applicative: apply function decoder to value decoder
  apply : ∀ {A B : Set} → Decoder (A → B) → Decoder A → Decoder B

  -- Monadic bind: decode then use result to choose next decoder
  andThen : ∀ {A B : Set} → (A → Decoder B) → Decoder A → Decoder B

  -- Alternative: try first, if fails try second
  oneOf : ∀ {A : Set} → List (Decoder A) → Decoder A

{-# COMPILE JS mapDecoder = function(f) { return function(decoder) {
  return {
    decode: (json) => {
      const result = decoder.decode(json);
      if (result.tag === 'ok') {
        return { tag: 'ok', value: f(result.value) };
      }
      return result;
    }
  };
}; } #-}

{-# COMPILE JS succeed = function(value) {
  return { decode: (_) => ({ tag: 'ok', value }) };
} #-}

{-# COMPILE JS fail = function(msg) {
  return { decode: (_) => ({ tag: 'err', error: msg }) };
} #-}

{-# COMPILE JS apply = function(df) { return function(da) {
  return {
    decode: (json) => {
      const rf = df.decode(json);
      if (rf.tag === 'err') return rf;
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      return { tag: 'ok', value: rf.value(ra.value) };
    }
  };
}; } #-}

{-# COMPILE JS andThen = function(f) { return function(decoder) {
  return {
    decode: (json) => {
      const result = decoder.decode(json);
      if (result.tag === 'err') return result;
      return f(result.value).decode(json);
    }
  };
}; } #-}

{-# COMPILE JS oneOf = function(decoders) {
  return {
    decode: (json) => {
      const errors = [];
      let current = decoders;
      let found = null;
      let done = false;
      while (!done) {
        current({
          '[]': () => { done = true; },
          '_∷_': (head, tail) => {
            const result = head.decode(json);
            if (result.tag === 'ok') { found = result; done = true; }
            else { errors.push(result.error); current = tail; }
          }
        });
      }
      if (found) return found;
      return { tag: 'err', error: 'None of ' + errors.length + ' decoders matched: ' + errors.join('; ') };
    }
  };
} #-}

------------------------------------------------------------------------
-- Running decoders
------------------------------------------------------------------------

postulate
  -- Decode a JSON string
  decodeString : ∀ {A : Set} → Decoder A → String → Result String A

  -- Decode a JsonValue directly
  decodeValue : ∀ {A : Set} → Decoder A → JsonValue → Result String A

{-# COMPILE JS decodeString = function(decoder) { return function(jsonStr) {
  try {
    const json = JSON.parse(jsonStr);
    const result = decoder.decode(json);
    if (result.tag === 'ok') {
      return b => b["ok"](result.value);
    }
    return b => b["err"](result.error);
  } catch (e) {
    return b => b["err"]('JSON parse error: ' + e.message);
  }
}; } #-}

-- FFI-FRAGILE: jNull, jBool, jNumber, jFloat, jString, jArray, jObject (JsonValue),
--   true/false (Bool), _,_ (Pair), [] / _∷_ (List)
{-# COMPILE JS decodeValue = function(decoder) { return function(json) {
  var expectedKeys = ['jNull','jBool','jNumber','jFloat','jString','jArray','jObject'];
  function toList(x) {
    if (Array.isArray(x)) return x;
    var arr = [], current = x, done = false;
    while (!done) {
      current({ '[]': function() { done = true; }, '_∷_': function(h, t) { arr.push(h); current = t; } });
    }
    return arr;
  }
  var dispatch = {
    jNull: () => null,
    jBool: (b) => b({"true": () => true, "false": () => false}),
    jNumber: (n) => Number(n),
    jFloat: (f) => f,
    jString: (s) => s,
    jArray: (arr) => toList(arr).map(toJS),
    jObject: (pairs) => {
      const obj = {};
      toList(pairs).forEach(p => {
        p({ '_,_': (k, v2) => { obj[k] = toJS(v2); } });
      });
      return obj;
    }
  };
  for (var i = 0; i < expectedKeys.length; i++) {
    if (!(expectedKeys[i] in dispatch)) {
      throw new Error('decodeValue: missing Scott key ' + expectedKeys[i] + ' — JsonValue constructors may have been renamed');
    }
  }
  function toJS(v) { return v(dispatch); }
  const jsValue = toJS(json);
  const result = decoder.decode(jsValue);
  if (result.tag === 'ok') {
    return b => b["ok"](result.value);
  }
  return b => b["err"](result.error);
}; } #-}

------------------------------------------------------------------------
-- Encoder type
------------------------------------------------------------------------

postulate
  Encoder : Set → Set

{-# COMPILE JS Encoder = function(x) { return x; } #-}

------------------------------------------------------------------------
-- Primitive encoders
------------------------------------------------------------------------

postulate
  encodeString : Encoder String
  encodeNat : Encoder ℕ
  encodeInt : Encoder ℤ
  encodeFloat : Encoder Float
  encodeBool : Encoder Bool
  encodeNull : Encoder ⊤

  -- Encode array
  encodeArray : ∀ {A : Set} → Encoder A → Encoder (Array A)

  -- Encode list
  encodeList : ∀ {A : Set} → Encoder A → Encoder (List A)

  -- Encode maybe (null if nothing)
  encodeMaybe : ∀ {A : Set} → Encoder A → Encoder (Maybe A)

{-# COMPILE JS encodeString = { encode: (s) => s } #-}
-- Note: Number(n) loses precision for values > 2^53 (Number.MAX_SAFE_INTEGER).
-- Agda's ℕ/ℤ are BigInt-backed, but JSON has no BigInt type. This is acceptable
-- for a browser UI framework where such large values are uncommon.
{-# COMPILE JS encodeNat = { encode: (n) => Number(n) } #-}
-- FFI-FRAGILE: +_ (ℤ), -[1+_] (ℤ)
{-# COMPILE JS encodeInt = { encode: (n) => n({"+_": pos => Number(pos), "-[1+_]": neg => -(Number(neg) + 1)}) } #-}
{-# COMPILE JS encodeFloat = { encode: (f) => f } #-}
-- FFI-FRAGILE: true (Bool), false (Bool)
{-# COMPILE JS encodeBool = { encode: (b) => b({"true": () => true, "false": () => false}) } #-}
{-# COMPILE JS encodeNull = { encode: (_) => null } #-}

{-# COMPILE JS encodeArray = function(encoder) {
  return { encode: (arr) => arr.map(x => encoder.encode(x)) };
} #-}

-- FFI-FRAGILE: [] (List), _∷_ (List)
{-# COMPILE JS encodeList = function(encoder) {
  return {
    encode: (list) => {
      const arr = [];
      let current = list;
      let done = false;
      while (!done) {
        current({
          '[]': () => { done = true; },
          '_∷_': (head, tail) => { arr.push(encoder.encode(head)); current = tail; }
        });
      }
      return arr;
    }
  };
} #-}

-- FFI-FRAGILE: just (Maybe), nothing (Maybe)
{-# COMPILE JS encodeMaybe = function(encoder) {
  return {
    encode: (maybe) => {
      return maybe({
        just: (x) => encoder.encode(x),
        nothing: () => null
      });
    }
  };
} #-}

------------------------------------------------------------------------
-- Object encoding
------------------------------------------------------------------------

-- Opaque type for raw JS values produced by encoders.
-- Not Scott-encoded — cannot be passed to decodeValue or pattern-matched.
-- Use encodeToString to get a String, or pass directly to JS FFI.
postulate RawJson : Set
{-# COMPILE JS RawJson = function(x) { return x; } #-}

postulate
  -- Build object from key-value pairs
  object : List (String × JsonValue) → JsonValue

  -- Encode a value to a raw JS representation.
  encodeWith : ∀ {A : Set} → Encoder A → A → RawJson

  -- Encode to JSON string
  encodeToString : ∀ {A : Set} → Encoder A → A → String

-- NOTE: arr contains Scott-encoded pairs (cb => cb["_,_"](k, v)).
-- decodeValue.toJS relies on this — it calls p({"_,_": (k,v) => ...}).
-- Do NOT convert pairs to native JS objects here.
-- FFI-FRAGILE: [] (List), _∷_ (List), jObject (JsonValue)
{-# COMPILE JS object = function(pairs) {
  const arr = [];
  let current = pairs;
  let done = false;
  while (!done) {
    current({
      '[]': () => { done = true; },
      '_∷_': (head, tail) => {
        arr.push(head);
        current = tail;
      }
    });
  }
  return (cases) => cases["jObject"](arr);
} #-}

{-# COMPILE JS encodeWith = function(encoder) { return function(value) {
  return encoder.encode(value);
}; } #-}

{-# COMPILE JS encodeToString = function(encoder) { return function(value) {
  return JSON.stringify(encoder.encode(value));
}; } #-}

------------------------------------------------------------------------
-- Helper: build object encoder from fields
------------------------------------------------------------------------

postulate
  -- Object encoder builder
  ObjectEncoder : Set → Set

  -- Start building object encoder
  objectEncoder : ∀ {A : Set} → ObjectEncoder A

  -- Add required field
  withField : ∀ {A B : Set} → String → (A → B) → Encoder B → ObjectEncoder A → ObjectEncoder A

  -- Add optional field (omit if nothing)
  withOptionalField : ∀ {A B : Set} → String → (A → Maybe B) → Encoder B → ObjectEncoder A → ObjectEncoder A

  -- Finalize to Encoder
  buildEncoder : ∀ {A : Set} → ObjectEncoder A → Encoder A

{-# COMPILE JS ObjectEncoder = function(x) { return x; } #-}

{-# COMPILE JS objectEncoder = { fields: [] } #-}

{-# COMPILE JS withField = function(name) { return function(getter) { return function(encoder) { return function(obj) {
  return {
    fields: [...obj.fields, { name, getter, encoder, optional: false }]
  };
}; }; }; } #-}

{-# COMPILE JS withOptionalField = function(name) { return function(getter) { return function(encoder) { return function(obj) {
  return {
    fields: [...obj.fields, { name, getter, encoder, optional: true }]
  };
}; }; }; } #-}

{-# COMPILE JS buildEncoder = function(obj) {
  return {
    encode: (value) => {
      const result = {};
      for (const field of obj.fields) {
        const fieldValue = field.getter(value);
        if (field.optional) {
          fieldValue({
            just: (x) => { result[field.name] = field.encoder.encode(x); },
            nothing: () => {}
          });
        } else {
          result[field.name] = field.encoder.encode(fieldValue);
        }
      }
      return result;
    }
  };
} #-}

------------------------------------------------------------------------
-- Convenience: map2 through map8 for record decoding
------------------------------------------------------------------------

postulate
  map2 : ∀ {A B R : Set} → (A → B → R) → Decoder A → Decoder B → Decoder R
  map3 : ∀ {A B C R : Set} → (A → B → C → R) → Decoder A → Decoder B → Decoder C → Decoder R
  map4 : ∀ {A B C D R : Set} → (A → B → C → D → R) → Decoder A → Decoder B → Decoder C → Decoder D → Decoder R
  map5 : ∀ {A B C D E R : Set} → (A → B → C → D → E → R) → Decoder A → Decoder B → Decoder C → Decoder D → Decoder E → Decoder R
  map6 : ∀ {A B C D E F R : Set} → (A → B → C → D → E → F → R) → Decoder A → Decoder B → Decoder C → Decoder D → Decoder E → Decoder F → Decoder R
  map7 : ∀ {A B C D E F G R : Set} → (A → B → C → D → E → F → G → R) → Decoder A → Decoder B → Decoder C → Decoder D → Decoder E → Decoder F → Decoder G → Decoder R
  map8 : ∀ {A B C D E F G H R : Set} → (A → B → C → D → E → F → G → H → R) → Decoder A → Decoder B → Decoder C → Decoder D → Decoder E → Decoder F → Decoder G → Decoder H → Decoder R

{-# COMPILE JS map2 = function(f) { return function(da) { return function(db) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      return { tag: 'ok', value: f(ra.value)(rb.value) };
    }
  };
}; }; } #-}

{-# COMPILE JS map3 = function(f) { return function(da) { return function(db) { return function(dc) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value) };
    }
  };
}; }; }; } #-}

{-# COMPILE JS map4 = function(f) { return function(da) { return function(db) { return function(dc) { return function(dd) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      const rd = dd.decode(json);
      if (rd.tag === 'err') return rd;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value)(rd.value) };
    }
  };
}; }; }; }; } #-}

{-# COMPILE JS map5 = function(f) { return function(da) { return function(db) { return function(dc) { return function(dd) { return function(de) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      const rd = dd.decode(json);
      if (rd.tag === 'err') return rd;
      const re = de.decode(json);
      if (re.tag === 'err') return re;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value)(rd.value)(re.value) };
    }
  };
}; }; }; }; }; } #-}

{-# COMPILE JS map6 = function(f) { return function(da) { return function(db) { return function(dc) { return function(dd) { return function(de) { return function(df) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      const rd = dd.decode(json);
      if (rd.tag === 'err') return rd;
      const re = de.decode(json);
      if (re.tag === 'err') return re;
      const rf = df.decode(json);
      if (rf.tag === 'err') return rf;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value)(rd.value)(re.value)(rf.value) };
    }
  };
}; }; }; }; }; }; } #-}

{-# COMPILE JS map7 = function(f) { return function(da) { return function(db) { return function(dc) { return function(dd) { return function(de) { return function(df) { return function(dg) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      const rd = dd.decode(json);
      if (rd.tag === 'err') return rd;
      const re = de.decode(json);
      if (re.tag === 'err') return re;
      const rf = df.decode(json);
      if (rf.tag === 'err') return rf;
      const rg = dg.decode(json);
      if (rg.tag === 'err') return rg;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value)(rd.value)(re.value)(rf.value)(rg.value) };
    }
  };
}; }; }; }; }; }; }; } #-}

{-# COMPILE JS map8 = function(f) { return function(da) { return function(db) { return function(dc) { return function(dd) { return function(de) { return function(df) { return function(dg) { return function(dh) {
  return {
    decode: (json) => {
      const ra = da.decode(json);
      if (ra.tag === 'err') return ra;
      const rb = db.decode(json);
      if (rb.tag === 'err') return rb;
      const rc = dc.decode(json);
      if (rc.tag === 'err') return rc;
      const rd = dd.decode(json);
      if (rd.tag === 'err') return rd;
      const re = de.decode(json);
      if (re.tag === 'err') return re;
      const rf = df.decode(json);
      if (rf.tag === 'err') return rf;
      const rg = dg.decode(json);
      if (rg.tag === 'err') return rg;
      const rh = dh.decode(json);
      if (rh.tag === 'err') return rh;
      return { tag: 'ok', value: f(ra.value)(rb.value)(rc.value)(rd.value)(re.value)(rf.value)(rg.value)(rh.value) };
    }
  };
}; }; }; }; }; }; }; }; } #-}

------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------

infixl 4 _<$>_ _<*>_
infixl 1 _>>=_

_<$>_ : ∀ {A B : Set} → (A → B) → Decoder A → Decoder B
_<$>_ = mapDecoder

_<*>_ : ∀ {A B : Set} → Decoder (A → B) → Decoder A → Decoder B
_<*>_ = apply

_>>=_ : ∀ {A B : Set} → Decoder A → (A → Decoder B) → Decoder B
d >>= f = andThen f d
