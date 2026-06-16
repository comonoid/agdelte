{-# OPTIONS --without-K #-}

-- IndexedMap: a NatMap with declared secondary indexes, auto-maintained on
-- insert / delete. Pure Agda over Agdelte.Storage.NatMap — no new FFI.
--
-- Abstract: the record is `private`, so importers cannot construct or pattern
-- match — they use only the operations below, and the index-consistency invariant
-- (`indexes ≡ rebuild entries`) holds BY CONSTRUCTION. (Concept: §3 of
-- docs/concepts/storage-model.md.)
--
-- An index is declared by an extractor `V → List ℕ` (the index-keys of a value),
-- supplied to `empty`; its POSITION in that list selects it in `byIndex`. A typed
-- per-entity index-name enum maps to a position at the use site (domain layer).
module Agdelte.Storage.IndexedMap where

open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Bool using (Bool; not)
open import Data.Maybe using (Maybe; just; nothing; maybe′; fromMaybe)
open import Data.List using (List; []; _∷_; map; foldr; take; dropWhileᵇ; filterᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Storage.NatMap as NM using (NatMap)

------------------------------------------------------------------------
-- Internal representation (private — not exported)
------------------------------------------------------------------------

private
  -- one secondary index: index-key (ℕ) → list of primary ids that have it
  IdxMap : Set
  IdxMap = NatMap (List ℕ)

  record Slot (V : Set) : Set where
    constructor mkSlot
    field
      extract : V → List ℕ      -- index-keys of a value (e.g. [uuidHash] or [foreignKey])
      imap    : IdxMap

  record IM (V : Set) : Set where
    constructor mkIM
    field
      primary : NatMap V
      slots   : List (Slot V)

  -- add / remove a primary id under one index key
  addKey : ℕ → ℕ → IdxMap → IdxMap
  addKey key id im = NM.insert key (id ∷ fromMaybe [] (NM.lookup key im)) im

  -- Remove `id` from `key`'s bucket; DELETE the key when the bucket becomes empty
  -- so empty buckets don't accumulate monotonically with index-key history (L7).
  -- byIndex already maps a missing key to [] (fromMaybe []), so this is behaviourally
  -- invariant.
  removeKey : ℕ → ℕ → IdxMap → IdxMap
  removeKey key id im with filterᵇ (λ x → not (x == id)) (fromMaybe [] (NM.lookup key im))
  ... | []       = NM.delete key im
  ... | (y ∷ ys) = NM.insert key (y ∷ ys) im

  addKeys : List ℕ → ℕ → IdxMap → IdxMap
  addKeys keys id im = foldr (λ k acc → addKey k id acc) im keys

  removeKeys : List ℕ → ℕ → IdxMap → IdxMap
  removeKeys keys id im = foldr (λ k acc → removeKey k id acc) im keys

  -- upsert one slot: retract the OLD value's keys (if any), then add the new
  -- value's keys (N3: stops stale index entries when an indexed field changes).
  slotUpsert : ∀ {V} → ℕ → Maybe V → V → Slot V → Slot V
  slotUpsert id mOld v s =
    let retr = maybe′ (λ o → removeKeys (Slot.extract s o) id (Slot.imap s)) (Slot.imap s) mOld
    in mkSlot (Slot.extract s) (addKeys (Slot.extract s v) id retr)

  slotDelete : ∀ {V} → ℕ → V → Slot V → Slot V
  slotDelete id o s = mkSlot (Slot.extract s) (removeKeys (Slot.extract s o) id (Slot.imap s))

  slotAt : ∀ {V} → ℕ → List (Slot V) → Maybe (Slot V)
  slotAt _       []           = nothing
  slotAt zero    (s ∷ _)      = just s
  slotAt (suc n) (_ ∷ rest)   = slotAt n rest

------------------------------------------------------------------------
-- Public opaque type + operations
------------------------------------------------------------------------

IndexedMap : Set → Set
IndexedMap = IM

-- Build an empty IndexedMap with the given index extractors (fixes the index set).
empty : ∀ {V} → List (V → List ℕ) → IndexedMap V
empty exts = mkIM NM.empty (map (λ e → mkSlot e NM.empty) exts)

lookup : ∀ {V} → ℕ → IndexedMap V → Maybe V
lookup id m = NM.lookup id (IM.primary m)

-- Upsert id↦v, maintaining all indexes (retract old keys, add new).
insert : ∀ {V} → ℕ → V → IndexedMap V → IndexedMap V
insert id v m =
  mkIM (NM.insert id v (IM.primary m))
       (map (slotUpsert id (NM.lookup id (IM.primary m)) v) (IM.slots m))

-- Remove id (hard delete), retracting its index keys.
delete : ∀ {V} → ℕ → IndexedMap V → IndexedMap V
delete id m =
  mkIM (NM.delete id (IM.primary m))
       (maybe′ (λ o → map (slotDelete id o) (IM.slots m)) (IM.slots m)
               (NM.lookup id (IM.primary m)))

-- Secondary lookup: index position → index-key → primary ids.
byIndex : ∀ {V} → ℕ → ℕ → IndexedMap V → List ℕ
byIndex pos key m =
  maybe′ (λ s → fromMaybe [] (NM.lookup key (Slot.imap s))) []
         (slotAt pos (IM.slots m))

-- Ordered page by primary id: entries with id > afterId, up to `limit`.
-- (NM.toList is ascending by key.) NB: includes soft-deleted rows — a live page
-- filters them at the call site (P4).
entriesFrom : ∀ {V} → ℕ → ℕ → IndexedMap V → List (ℕ × V)
entriesFrom afterId limit m =
  take limit (dropWhileᵇ (λ p → proj₁ p ≤ᵇ afterId) (NM.toList (IM.primary m)))

-- All entries in id order (for reindex / property tests).
toList : ∀ {V} → IndexedMap V → List (ℕ × V)
toList m = NM.toList (IM.primary m)
