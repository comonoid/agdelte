{-# OPTIONS --without-K #-}

-- Form Validation for Agdelte
-- Type-safe form fields with composable validators

module Agdelte.Forms where

open import Data.String using (String; length) renaming (_++_ to _++ˢ_)
open import Data.Nat using (ℕ; _<ᵇ_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map; null)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)

open import Agdelte.Core.Result using (Result; ok; err)

------------------------------------------------------------------------
-- Validation Error
------------------------------------------------------------------------

record ValidationError : Set where
  constructor mkError
  field
    errorField   : String  -- field name
    errorMessage : String  -- human-readable message

open ValidationError public

------------------------------------------------------------------------
-- Validator type
------------------------------------------------------------------------

-- A Validator A checks a value and returns list of errors (empty = valid)
Validator : Set → Set
Validator A = A → List ValidationError

-- Run validator, convert to Result
validate : ∀ {A : Set} → String → Validator A → A → Result (List ValidationError) A
validate fieldName v value with v value
... | [] = ok value
... | errors = err (map (λ e → record e { errorField = fieldName }) errors)

------------------------------------------------------------------------
-- Primitive validators
------------------------------------------------------------------------

-- Always passes
none : ∀ {A : Set} → Validator A
none _ = []

-- Always fails with message
invalid : ∀ {A : Set} → String → Validator A
invalid msg _ = mkError "" msg ∷ []

-- Required: non-empty string
required : Validator String
required s = if length s ≡ᵇ 0 then mkError "" "This field is required" ∷ [] else []
  where open import Data.Nat using (_≡ᵇ_)

-- Minimum length
minLength : ℕ → Validator String
minLength n s = if length s <ᵇ n
  then mkError "" ("Must be at least " ++ˢ showℕ n ++ˢ " characters") ∷ []
  else []
  where
    open import Agda.Builtin.String using (primShowNat)
    showℕ = primShowNat

-- Maximum length
maxLength : ℕ → Validator String
maxLength n s = if n <ᵇ length s
  then mkError "" ("Must be at most " ++ˢ showℕ n ++ˢ " characters") ∷ []
  else []
  where
    open import Agda.Builtin.String using (primShowNat)
    showℕ = primShowNat

-- Length in range
lengthBetween : ℕ → ℕ → Validator String
lengthBetween min max s =
  let len = length s in
  if (len <ᵇ min) ∨ (max <ᵇ len)
  then mkError "" ("Length must be between " ++ˢ showℕ min ++ˢ " and " ++ˢ showℕ max) ∷ []
  else []
  where
    open import Agda.Builtin.String using (primShowNat)
    showℕ = primShowNat

------------------------------------------------------------------------
-- Pattern validators (via FFI)
------------------------------------------------------------------------

postulate
  -- Email format
  email : Validator String

  -- URL format
  url : Validator String

  -- Match regex pattern
  pattern : String → String → Validator String  -- pattern, error message

  -- Numeric string
  numeric : Validator String

  -- Alphanumeric
  alphanumeric : Validator String

{-# COMPILE JS email = function(s) {
  const re = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  if (re.test(s)) return { "[]": null };
  return { "_∷_": [{ "mkError": ["", "Invalid email format"] }, { "[]": null }] };
} #-}

{-# COMPILE JS url = function(s) {
  try {
    new URL(s);
    return { "[]": null };
  } catch {
    return { "_∷_": [{ "mkError": ["", "Invalid URL format"] }, { "[]": null }] };
  }
} #-}

{-# COMPILE JS pattern = function(pat) { return function(errMsg) { return function(s) {
  try {
    const re = new RegExp(pat);
    if (re.test(s)) return { "[]": null };
    return { "_∷_": [{ "mkError": ["", errMsg] }, { "[]": null }] };
  } catch {
    return { "_∷_": [{ "mkError": ["", "Invalid pattern"] }, { "[]": null }] };
  }
}; }; } #-}

{-# COMPILE JS numeric = function(s) {
  if (/^\d+$/.test(s)) return { "[]": null };
  return { "_∷_": [{ "mkError": ["", "Must contain only digits"] }, { "[]": null }] };
} #-}

{-# COMPILE JS alphanumeric = function(s) {
  if (/^[a-zA-Z0-9]+$/.test(s)) return { "[]": null };
  return { "_∷_": [{ "mkError": ["", "Must be alphanumeric"] }, { "[]": null }] };
} #-}

------------------------------------------------------------------------
-- Validator combinators
------------------------------------------------------------------------

-- Combine validators (all must pass)
infixr 5 _<&>_

_<&>_ : ∀ {A : Set} → Validator A → Validator A → Validator A
(v1 <&> v2) a = v1 a ++ v2 a

-- Combine list of validators
all : ∀ {A : Set} → List (Validator A) → Validator A
all [] a = []
all (v ∷ vs) a = v a ++ all vs a

-- First validator that fails (short-circuit)
first : ∀ {A : Set} → List (Validator A) → Validator A
first [] a = []
first (v ∷ vs) a with v a
... | [] = first vs a
... | errors = errors

-- Conditional validator
when : ∀ {A : Set} → (A → Bool) → Validator A → Validator A
when cond v a = if cond a then v a else []

-- Unless condition
unless : ∀ {A : Set} → (A → Bool) → Validator A → Validator A
unless cond = when (not ∘ cond)

-- Transform value before validating
contramap : ∀ {A B : Set} → (A → B) → Validator B → Validator A
contramap f v = v ∘ f

------------------------------------------------------------------------
-- Maybe validators
------------------------------------------------------------------------

-- Validate if Just, pass if Nothing
optional : ∀ {A : Set} → Validator A → Validator (Maybe A)
optional v nothing = []
optional v (just a) = v a

-- Must be Just and pass validation
requiredMaybe : ∀ {A : Set} → Validator A → Validator (Maybe A)
requiredMaybe v nothing = mkError "" "This field is required" ∷ []
requiredMaybe v (just a) = v a

------------------------------------------------------------------------
-- Comparison validators
------------------------------------------------------------------------

postulate
  -- String equality
  equals : String → Validator String

  -- String not equal
  notEquals : String → Validator String

{-# COMPILE JS equals = function(expected) { return function(s) {
  if (s === expected) return { "[]": null };
  return { "_∷_": [{ "mkError": ["", "Must equal \"" + expected + "\""] }, { "[]": null }] };
}; } #-}

{-# COMPILE JS notEquals = function(forbidden) { return function(s) {
  if (s !== forbidden) return { "[]": null };
  return { "_∷_": [{ "mkError": ["", "Must not equal \"" + forbidden + "\""] }, { "[]": null }] };
}; } #-}

------------------------------------------------------------------------
-- Number validators
------------------------------------------------------------------------

postulate
  -- Parse string as number and validate range
  inRange : ℕ → ℕ → Validator String

  -- Positive number (string)
  positive : Validator String

{-# COMPILE JS inRange = function(min) { return function(max) { return function(s) {
  const n = parseInt(s, 10);
  if (isNaN(n)) {
    return { "_∷_": [{ "mkError": ["", "Must be a number"] }, { "[]": null }] };
  }
  const minN = Number(min);
  const maxN = Number(max);
  if (n < minN || n > maxN) {
    return { "_∷_": [{ "mkError": ["", "Must be between " + minN + " and " + maxN] }, { "[]": null }] };
  }
  return { "[]": null };
}; }; } #-}

{-# COMPILE JS positive = function(s) {
  const n = parseInt(s, 10);
  if (isNaN(n) || n <= 0) {
    return { "_∷_": [{ "mkError": ["", "Must be a positive number"] }, { "[]": null }] };
  }
  return { "[]": null };
} #-}

------------------------------------------------------------------------
-- FormField: field with value and validation state
------------------------------------------------------------------------

record FormField (A : Set) : Set where
  constructor mkField
  field
    fieldName      : String
    fieldValue     : A
    fieldValidator : Validator A
    fieldTouched   : Bool
    fieldErrors    : List ValidationError

open FormField public

-- Create new field
newField : ∀ {A : Set} → String → A → Validator A → FormField A
newField name value validator = mkField name value validator false []

-- Update field value and revalidate
updateField : ∀ {A : Set} → A → FormField A → FormField A
updateField value f =
  let errors = fieldValidator f value
  in record f { fieldValue = value ; fieldErrors = errors ; fieldTouched = true }

-- Touch field (show errors without changing value)
touchField : ∀ {A : Set} → FormField A → FormField A
touchField f =
  let errors = fieldValidator f (fieldValue f)
  in record f { fieldTouched = true ; fieldErrors = errors }

-- Check if field is valid
isFieldValid : ∀ {A : Set} → FormField A → Bool
isFieldValid f = null (fieldErrors f)

-- Get field value if valid
getValidValue : ∀ {A : Set} → FormField A → Maybe A
getValidValue f = if isFieldValid f then just (fieldValue f) else nothing

------------------------------------------------------------------------
-- Form: collection of fields
------------------------------------------------------------------------

-- Check if all fields valid (for form-level validation)
postulate
  -- Combine field errors from multiple fields
  combineErrors : List (List ValidationError) → List ValidationError

{-# COMPILE JS combineErrors = function(lists) {
  const result = [];
  let current = lists;
  while (current["_∷_"]) {
    let errors = current["_∷_"][0];
    while (errors["_∷_"]) {
      result.push(errors["_∷_"][0]);
      errors = errors["_∷_"][1];
    }
    current = current["_∷_"][1];
  }
  // Convert back to Agda list
  let agdaList = { "[]": null };
  for (let i = result.length - 1; i >= 0; i--) {
    agdaList = { "_∷_": [result[i], agdaList] };
  }
  return agdaList;
} #-}

------------------------------------------------------------------------
-- Cross-field validation
------------------------------------------------------------------------

private
  postulate eqStr : String → String → Bool
  {-# COMPILE JS eqStr = function(a) { return function(b) { return a === b; }; } #-}

-- Password confirmation
passwordsMatch : String → String → List ValidationError
passwordsMatch pw1 pw2 =
  if eqStr pw1 pw2 then [] else mkError "confirmPassword" "Passwords do not match" ∷ []

-- Generic equality check between two fields
mustMatch : String → String → String → List ValidationError
mustMatch fieldName v1 v2 =
  if eqStr v1 v2 then [] else mkError fieldName "Fields must match" ∷ []
