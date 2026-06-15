{-# OPTIONS --without-K #-}

-- CRM identity domain (SPEC §5.2) on the WAL + in-memory engine.
-- Reference entity slice: `party`. Mirrors the AppStore pattern — records +
-- NatMap "tables" + an Op sum type + a pure applyOp — but neutral (services-core).
--
-- Tenancy is intentionally omitted for the single-operator MVP (one operator ⇒
-- multitenancy is near-pointless); it returns when this becomes SaaS. Persistence
-- (WalConfig serialization) is wired in a later Store module once entities settle.
module Crm.Identity where

open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)

open import Agdelte.Storage.NatMap as NM using (NatMap)

------------------------------------------------------------------------
-- Party (person | org) — SPEC §5.1/§5.2
------------------------------------------------------------------------

PartyId : Set
PartyId = ℕ

data PartyType : Set where
  Person : PartyType
  Org    : PartyType

record PartyRecord : Set where
  constructor mkParty
  field
    pId          : PartyId
    pType        : PartyType
    pDisplayName : String
    pTz          : String          -- IANA tz; reminder rendering (§5.4)
    pCreatedAt   : ℕ               -- unix seconds
    pDeletedAt   : Maybe ℕ         -- soft-delete (§5.7); nothing = live

open PartyRecord public

------------------------------------------------------------------------
-- In-memory state
------------------------------------------------------------------------

record CrmState : Set where
  constructor mkCrmState
  field
    csParties    : NatMap PartyRecord
    csNextPartyId : ℕ

open CrmState public

emptyCrmState : CrmState
emptyCrmState = mkCrmState NM.empty 0

------------------------------------------------------------------------
-- Operations (WAL log entries)
------------------------------------------------------------------------

data CrmOp : Set where
  CreateParty     : PartyRecord → CrmOp
  RenameParty     : PartyId → String → CrmOp
  SoftDeleteParty : PartyId → ℕ → CrmOp        -- id, deletion timestamp

------------------------------------------------------------------------
-- Apply (pure state transition)
------------------------------------------------------------------------

private
  renameIn : PartyId → String → NatMap PartyRecord → NatMap PartyRecord
  renameIn pid name ps with NM.lookup pid ps
  ... | nothing = ps
  ... | just p  = NM.insert pid (record p { pDisplayName = name }) ps

  softDeleteIn : PartyId → ℕ → NatMap PartyRecord → NatMap PartyRecord
  softDeleteIn pid at ps with NM.lookup pid ps
  ... | nothing = ps
  ... | just p  = NM.insert pid (record p { pDeletedAt = just at }) ps

applyOp : CrmOp → CrmState → CrmState
applyOp (CreateParty p) s =
  record s { csParties    = NM.insert (pId p) p (csParties s)
           ; csNextPartyId = suc (pId p) ⊔ csNextPartyId s
           }
applyOp (RenameParty pid name) s =
  record s { csParties = renameIn pid name (csParties s) }
applyOp (SoftDeleteParty pid at) s =
  record s { csParties = softDeleteIn pid at (csParties s) }

------------------------------------------------------------------------
-- Queries (read-side, over in-memory state)
------------------------------------------------------------------------

lookupParty : PartyId → CrmState → Maybe PartyRecord
lookupParty pid s = NM.lookup pid (csParties s)

-- Live (non-soft-deleted) parties.
liveParties : CrmState → List PartyRecord
liveParties s = NM.foldl keep [] (csParties s)
  where
    keep : List PartyRecord → ℕ → PartyRecord → List PartyRecord
    keep acc _ p with pDeletedAt p
    ... | nothing = p ∷ acc
    ... | just _  = acc
