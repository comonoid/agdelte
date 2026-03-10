{-# OPTIONS --without-K #-}

-- Native JavaScript Arrays for Agdelte
-- Provides O(1) random access and efficient operations

module Agdelte.Data.Array where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

------------------------------------------------------------------------
-- Ordering type for comparisons
------------------------------------------------------------------------

data Ordering : Set where
  lt : Ordering
  eq : Ordering
  gt : Ordering

------------------------------------------------------------------------
-- Array type (opaque, backed by JS Array)
------------------------------------------------------------------------

postulate
  Array : Set → Set

{-# COMPILE JS Array = function(x) { return x; } #-}

------------------------------------------------------------------------
-- Construction
------------------------------------------------------------------------

postulate
  -- Empty array
  empty : ∀ {A : Set} → Array A

  -- Singleton array
  singleton : ∀ {A : Set} → A → Array A

  -- From list (O(n))
  fromList : ∀ {A : Set} → List A → Array A

  -- Replicate: array of n copies of x
  replicate : ∀ {A : Set} → ℕ → A → Array A

{-# COMPILE JS empty = [] #-}

{-# COMPILE JS singleton = function(x) { return [x]; } #-}

{-# COMPILE JS fromList = function(list) {
  const arr = [];
  let current = list;
  let done = false;
  while (!done) {
    current({
      '[]': () => { done = true; },
      '_∷_': (head, tail) => { arr.push(head); current = tail; }
    });
  }
  return arr;
} #-}

{-# COMPILE JS replicate = function(n) { return function(x) {
  return Array(Number(n)).fill(x);
}; } #-}

------------------------------------------------------------------------
-- Query
------------------------------------------------------------------------

postulate
  -- Length (O(1))
  length : ∀ {A : Set} → Array A → ℕ

  -- Is empty? (O(1))
  null : ∀ {A : Set} → Array A → Bool

  -- Safe index (O(1))
  index : ∀ {A : Set} → ℕ → Array A → Maybe A

  -- Unsafe index (O(1)) - returns undefined if out of bounds
  unsafeIndex : ∀ {A : Set} → ℕ → Array A → A

{-# COMPILE JS length = function(arr) { return BigInt(arr.length); } #-}

-- FFI-FRAGILE: true (Bool), false (Bool)
{-# COMPILE JS null = function(arr) {
  return arr.length === 0
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
} #-}

-- FFI-FRAGILE: just (Maybe), nothing (Maybe)
{-# COMPILE JS index = function(i) { return function(arr) {
  const idx = Number(i);
  if (idx < arr.length) {
    return (cases) => cases.just(arr[idx]);
  } else {
    return (cases) => cases.nothing();
  }
}; } #-}

{-# COMPILE JS unsafeIndex = function(i) { return function(arr) {
  return arr[Number(i)];
}; } #-}

------------------------------------------------------------------------
-- Modification (immutable - returns new array)
------------------------------------------------------------------------

postulate
  -- Append element at end (O(n) copy)
  snoc : ∀ {A : Set} → Array A → A → Array A

  -- Prepend element at start (O(n) copy)
  cons : ∀ {A : Set} → A → Array A → Array A

  -- Concatenate two arrays (O(n+m))
  append : ∀ {A : Set} → Array A → Array A → Array A

  -- Update at index (O(n) copy)
  update : ∀ {A : Set} → ℕ → A → Array A → Array A

  -- Slice: subarray from start to end (exclusive)
  slice : ∀ {A : Set} → ℕ → ℕ → Array A → Array A

  -- Take first n elements
  take : ∀ {A : Set} → ℕ → Array A → Array A

  -- Drop first n elements
  drop : ∀ {A : Set} → ℕ → Array A → Array A

{-# COMPILE JS snoc = function(arr) { return function(x) {
  return [...arr, x];
}; } #-}

{-# COMPILE JS cons = function(x) { return function(arr) {
  return [x, ...arr];
}; } #-}

{-# COMPILE JS append = function(a) { return function(b) {
  return [...a, ...b];
}; } #-}

{-# COMPILE JS update = function(i) { return function(x) { return function(arr) {
  const idx = Number(i);
  if (idx >= arr.length) return arr;
  const result = [...arr];
  result[idx] = x;
  return result;
}; }; } #-}

{-# COMPILE JS slice = function(start) { return function(end) { return function(arr) {
  return arr.slice(Number(start), Number(end));
}; }; } #-}

{-# COMPILE JS take = function(n) { return function(arr) {
  return arr.slice(0, Number(n));
}; } #-}

{-# COMPILE JS drop = function(n) { return function(arr) {
  return arr.slice(Number(n));
}; } #-}

------------------------------------------------------------------------
-- Transformation
------------------------------------------------------------------------

postulate
  -- Map function over array
  map : ∀ {A B : Set} → (A → B) → Array A → Array B

  -- Filter elements
  filter : ∀ {A : Set} → (A → Bool) → Array A → Array A

  -- Reverse array
  reverse : ∀ {A : Set} → Array A → Array A

  -- Sort with comparator
  sortBy : ∀ {A : Set} → (A → A → Ordering) → Array A → Array A

{-# COMPILE JS map = function(f) { return function(arr) {
  return arr.map(f);
}; } #-}

{-# COMPILE JS filter = function(p) { return function(arr) {
  return arr.filter(x => p(x)({"true": () => true, "false": () => false}));
}; } #-}

{-# COMPILE JS reverse = function(arr) {
  return [...arr].reverse();
} #-}

{-# COMPILE JS sortBy = function(cmp) { return function(arr) {
  return [...arr].sort((a, b) =>
    cmp(a)(b)({ lt: () => -1, eq: () => 0, gt: () => 1 })
  );
}; } #-}

------------------------------------------------------------------------
-- Folding
------------------------------------------------------------------------

postulate
  -- Left fold
  foldl : ∀ {A B : Set} → (B → A → B) → B → Array A → B

  -- Right fold
  foldr : ∀ {A B : Set} → (A → B → B) → B → Array A → B

  -- Sum of numbers
  sum : Array ℕ → ℕ

  -- All elements satisfy predicate
  all : ∀ {A : Set} → (A → Bool) → Array A → Bool

  -- Any element satisfies predicate
  any : ∀ {A : Set} → (A → Bool) → Array A → Bool

{-# COMPILE JS foldl = function(f) { return function(z) { return function(arr) {
  return arr.reduce((acc, x) => f(acc)(x), z);
}; }; } #-}

{-# COMPILE JS foldr = function(f) { return function(z) { return function(arr) {
  return arr.reduceRight((acc, x) => f(x)(acc), z);
}; }; } #-}

{-# COMPILE JS sum = function(arr) {
  return arr.reduce((a, b) => a + b, 0n);
} #-}

{-# COMPILE JS all = function(p) { return function(arr) {
  const r = arr.every(x => p(x)({"true": () => true, "false": () => false}));
  return r
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
}; } #-}

{-# COMPILE JS any = function(p) { return function(arr) {
  const r = arr.some(x => p(x)({"true": () => true, "false": () => false}));
  return r
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
}; } #-}

------------------------------------------------------------------------
-- Search
------------------------------------------------------------------------

postulate
  -- Find first element matching predicate
  find : ∀ {A : Set} → (A → Bool) → Array A → Maybe A

  -- Find index of first match
  findIndex : ∀ {A : Set} → (A → Bool) → Array A → Maybe ℕ

  -- Check if element exists (needs equality)
  elem : ∀ {A : Set} → (A → A → Bool) → A → Array A → Bool

-- FFI-FRAGILE: just (Maybe), nothing (Maybe), true (Bool), false (Bool)
{-# COMPILE JS find = function(p) { return function(arr) {
  const idx = arr.findIndex(x => p(x)({"true": () => true, "false": () => false}));
  return idx >= 0
    ? (cases) => cases.just(arr[idx])
    : (cases) => cases.nothing();
}; } #-}

-- FFI-FRAGILE: just (Maybe), nothing (Maybe), true (Bool), false (Bool)
{-# COMPILE JS findIndex = function(p) { return function(arr) {
  const idx = arr.findIndex(x => p(x)({"true": () => true, "false": () => false}));
  return idx >= 0
    ? (cases) => cases.just(BigInt(idx))
    : (cases) => cases.nothing();
}; } #-}

-- FFI-FRAGILE: true (Bool), false (Bool)
{-# COMPILE JS elem = function(eq) { return function(x) { return function(arr) {
  const r = arr.some(y => eq(x)(y)({"true": () => true, "false": () => false}));
  return r
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
}; }; } #-}

------------------------------------------------------------------------
-- Conversion
------------------------------------------------------------------------

postulate
  -- To list (O(n))
  toList : ∀ {A : Set} → Array A → List A

-- FFI-FRAGILE: [] (List), _∷_ (List)
{-# COMPILE JS toList = function(arr) {
  let result = (cases) => cases['[]']();
  for (let i = arr.length - 1; i >= 0; i--) {
    const elem = arr[i];
    const tail = result;
    result = (cases) => cases['_∷_'](elem, tail);
  }
  return result;
} #-}

------------------------------------------------------------------------
-- Iteration helpers for foreach in templates
------------------------------------------------------------------------

postulate
  -- Indexed map: f receives (index, element)
  mapWithIndex : ∀ {A B : Set} → (ℕ → A → B) → Array A → Array B

  -- Generate array from indices: [f(0), f(1), ..., f(n-1)]
  generate : ∀ {A : Set} → ℕ → (ℕ → A) → Array A

{-# COMPILE JS mapWithIndex = function(f) { return function(arr) {
  return arr.map((x, i) => f(BigInt(i))(x));
}; } #-}

{-# COMPILE JS generate = function(n) { return function(f) {
  return Array.from({ length: Number(n) }, (_, i) => f(BigInt(i)));
}; } #-}

------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------

infixr 5 _++_
infixl 9 _!_

_++_ : ∀ {A : Set} → Array A → Array A → Array A
_++_ = append

_!_ : ∀ {A : Set} → Array A → ℕ → Maybe A
arr ! i = index i arr
