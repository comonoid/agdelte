{-# OPTIONS --without-K #-}

-- Role-based access control for the video course platform.
-- Defines roles, role serialization, and role extraction from JWT payload.

module Agdelte.Auth.Role where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.String using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Roles
------------------------------------------------------------------------

data Role : Set where
  Student    : Role
  Instructor : Role
  Admin      : Role

------------------------------------------------------------------------
-- Serialization (for JWT payload and WAL)
------------------------------------------------------------------------

showRole : Role → String
showRole Student    = "student"
showRole Instructor = "instructor"
showRole Admin      = "admin"

parseRole : String → Maybe Role
parseRole s with s ≟ "student"
... | yes _ = just Student
... | no _ with s ≟ "instructor"
...   | yes _ = just Instructor
...   | no _ with s ≟ "admin"
...     | yes _ = just Admin
...     | no _  = nothing

------------------------------------------------------------------------
-- Role comparison
------------------------------------------------------------------------

roleEq : Role → Role → Bool
roleEq Student    Student    = true
roleEq Instructor Instructor = true
roleEq Admin      Admin      = true
roleEq _          _          = false

------------------------------------------------------------------------
-- Role checks
------------------------------------------------------------------------

-- | Is this role at least as privileged as the required role?
-- Student < Instructor < Admin
roleAtLeast : (required : Role) → (actual : Role) → Bool
roleAtLeast Student    _          = true
roleAtLeast Instructor Instructor = true
roleAtLeast Instructor Admin      = true
roleAtLeast Admin      Admin      = true
roleAtLeast _          _          = false
