{-# OPTIONS --without-K #-}

-- Map from ℕ to values, backed by Haskell Data.IntMap.Strict.
-- Server-only (GHC backend).

module Agdelte.Storage.NatMap where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.List using (List; []; _∷_; foldr; reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Type
------------------------------------------------------------------------

postulate
  NatMap : Set → Set

------------------------------------------------------------------------
-- Construction
------------------------------------------------------------------------

postulate
  empty    : ∀ {V} → NatMap V
  insert   : ∀ {V} → Nat → V → NatMap V → NatMap V
  delete   : ∀ {V} → Nat → NatMap V → NatMap V
  lookup   : ∀ {V} → Nat → NatMap V → Maybe V
  member   : ∀ {V} → Nat → NatMap V → Bool
  size     : ∀ {V} → NatMap V → Nat
  values   : ∀ {V} → NatMap V → List V
  foldl    : ∀ {V} {A : Set} → (A → Nat → V → A) → A → NatMap V → A

-- toList / fromList are DERIVED in pure Agda (not FFI): a (Nat × V) pair uses
-- Agda's Σ, which MAlonzo cannot translate across a COMPILE GHC boundary.
-- Building them from foldl/insert/empty keeps the FFI Σ-free.
toList : ∀ {V} → NatMap V → List (Nat × V)
toList m = reverse (foldl (λ acc k v → (k , v) ∷ acc) [] m)

fromList : ∀ {V} → List (Nat × V) → NatMap V
fromList xs = foldr (λ p acc → insert (proj₁ p) (proj₂ p) acc) empty xs

------------------------------------------------------------------------
-- GHC compilation
------------------------------------------------------------------------

-- Agda ℕ compiles to Integer. We back the map with Data.Map keyed by Integer
-- (not Data.IntMap, whose Int keys truncate ids ≥ 2^63 and could collide —
-- e.g. attacker-controlled ids replayed from a WAL/snapshot).
-- NB: the Haskell type is given INLINE in the COMPILE pragma rather than as a
-- `type` decl inside a FOREIGN block — MAlonzo appends its own imports (e.g.
-- Data.Text) after FOREIGN blocks, and an import after a `type` decl is a parse
-- error. (NatMap was JS-only before; this surfaced on its first GHC compile.)
{-# FOREIGN GHC import qualified Data.Map.Strict as M #-}

{-# COMPILE GHC NatMap = type M.Map Integer #-}

{-# COMPILE GHC empty    = \ _ -> M.empty #-}
{-# COMPILE GHC insert   = \ _ k -> M.insert k #-}
{-# COMPILE GHC delete   = \ _ k -> M.delete k #-}
{-# COMPILE GHC lookup   = \ _ k -> M.lookup k #-}
{-# COMPILE GHC member   = \ _ k -> M.member k #-}
{-# COMPILE GHC size     = \ _ m -> fromIntegral (M.size m) #-}
{-# COMPILE GHC values   = \ _ -> M.elems #-}
{-# COMPILE GHC foldl    = \ _ _ f z m -> M.foldlWithKey' (\a k v -> f a k v) z m #-}
