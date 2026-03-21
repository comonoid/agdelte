{-# OPTIONS --without-K #-}

-- Map from ℕ to values, backed by Haskell Data.IntMap.Strict.
-- Server-only (GHC backend).

module Agdelte.Storage.NatMap where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Product using (_×_)

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
  toList   : ∀ {V} → NatMap V → List (Nat × V)
  fromList : ∀ {V} → List (Nat × V) → NatMap V
  values   : ∀ {V} → NatMap V → List V
  foldl    : ∀ {V} {A : Set} → (A → Nat → V → A) → A → NatMap V → A

------------------------------------------------------------------------
-- GHC compilation
------------------------------------------------------------------------

{-# FOREIGN GHC
  import qualified Data.IntMap.Strict as IM
  import Data.Maybe (maybe)

  type AgdaNatMap v = IM.IntMap v

  -- Agda ℕ compiles to Integer, but IntMap uses Int keys.
  -- All key-taking functions must convert via fromIntegral.
  fi :: Integer -> Int
  fi = fromIntegral
  #-}

{-# COMPILE GHC NatMap = type AgdaNatMap #-}

{-# COMPILE GHC empty    = \ _ -> IM.empty #-}
{-# COMPILE GHC insert   = \ _ k -> IM.insert (fi k) #-}
{-# COMPILE GHC delete   = \ _ k -> IM.delete (fi k) #-}
{-# COMPILE GHC lookup   = \ _ k -> IM.lookup (fi k) #-}
{-# COMPILE GHC member   = \ _ k -> IM.member (fi k) #-}
{-# COMPILE GHC size     = \ _ m -> fromIntegral (IM.size m) #-}
{-# COMPILE GHC toList   = \ _ m -> map (\(k,v) -> (fromIntegral k, v)) (IM.toList m) #-}
{-# COMPILE GHC fromList = \ _ xs -> IM.fromList (map (\(k,v) -> (fi k, v)) xs) #-}
{-# COMPILE GHC values   = \ _ -> IM.elems #-}
{-# COMPILE GHC foldl    = \ _ _ f z m -> IM.foldlWithKey' (\a k v -> f a (fromIntegral k) v) z m #-}
