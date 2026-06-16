{-# OPTIONS --without-K #-}

-- CRM domain records (SPEC §5.2) — records ONLY (no state/ops/queries; those live
-- in Crm.Store, Phase 2). Neutral service-core domain on the WAL + in-memory engine.
--
-- Addressable entities carry `uuid` (external id, §13) alongside the internal `id`.
-- M:N is a fact-record (Participation). Tenancy omitted for the single-operator MVP.
-- (Concept: docs/concepts/storage-model.md §1.)
module Crm.Identity where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Maybe using (Maybe)

------------------------------------------------------------------------
-- Shared
------------------------------------------------------------------------

PartyId Uuid : Set
PartyId = ℕ
Uuid     = String

Role : Set       -- participation role — config-driven (e.g. "client","provider","payer")
Role = String

data PartyType : Set where
  Person : PartyType
  Org    : PartyType

data ActStatus : Set where
  Scheduled : ActStatus
  Completed : ActStatus
  Canceled  : ActStatus
  NoShow    : ActStatus

------------------------------------------------------------------------
-- Party (person | org) — §5.1/§5.2
------------------------------------------------------------------------

record Party : Set where
  constructor mkParty
  field
    pId          : ℕ
    pUuid        : Uuid             -- external id (§13)
    pType        : PartyType
    pDisplayName : String
    pTz          : String           -- IANA tz; reminder rendering (§5.4)
    pCreatedAt   : ℕ                -- unix seconds (supplied from IO, §1)
    pDeletedAt   : Maybe ℕ          -- soft-delete (§5.7); nothing = live

open Party public

------------------------------------------------------------------------
-- Engagement (the "кейс") — §5.2
------------------------------------------------------------------------

record Engagement : Set where
  constructor mkEngagement
  field
    eId        : ℕ
    eUuid      : Uuid
    eCaseType  : ℕ                  -- case_type id
    eStage     : ℕ                  -- current stage id
    eTitle     : Maybe String
    eCreatedAt : ℕ
    eDeletedAt : Maybe ℕ

open Engagement public

------------------------------------------------------------------------
-- Activity (session/meeting; 1:N under engagement) — §5.3
------------------------------------------------------------------------

record Activity : Set where
  constructor mkActivity
  field
    aId           : ℕ
    aUuid         : Uuid
    aEngagementId : ℕ               -- FK → engagement (1:N)
    aStartsAt     : ℕ               -- unix seconds
    aStatus       : ActStatus
    aCreatedAt    : ℕ
    aDeletedAt    : Maybe ℕ

open Activity public

------------------------------------------------------------------------
-- Participation (M:N party↔engagement, with role) — fact-record, §5.1
------------------------------------------------------------------------

record Participation : Set where
  constructor mkParticipation
  field
    prId           : ℕ              -- synthetic row id (primary key)
    prEngagementId : ℕ
    prPartyId      : ℕ
    prRole         : Role
    prCreatedAt    : ℕ

open Participation public

------------------------------------------------------------------------
-- Account (a balance in minor units; invariant: never negative) — §5.x money
------------------------------------------------------------------------

record Account : Set where
  constructor mkAccount
  field
    acId        : ℕ
    acUuid      : Uuid
    acBalance   : ℕ                 -- minor units (kopecks); guarded ≥ 0 by construction
    acCreatedAt : ℕ

open Account public
