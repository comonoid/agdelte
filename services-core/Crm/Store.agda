{-# OPTIONS --without-K #-}

-- CRM store assembly (Phase 2): Base = self-indexing IndexedMaps per entity, a
-- typed CrmOp (per-entity constructors, #N5), pure `apply` (maintains indexes via
-- IndexedMap + advances nextId, #N1), Err, and the op codec via Crm.Wire (#D).
-- No separate Indexes/reindex (#2). WAL wiring (walTxn/WalConfig) is Phase 3.
-- (Concept: docs/concepts/storage-model.md §6/§16.)
module Crm.Store where

open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.String using (String; toList; fromList) renaming (_++_ to _<>_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Char using (Char)
open import Agda.Builtin.Char using (primCharEquality)

open import Crm.Identity
open import Crm.Wire
  using ( encParty; decParty; encEngagement; decEngagement
        ; encActivity; decActivity; encParticipation; decParticipation )
open import Agdelte.Storage.Wire using (encℕ; decℕ)
open import Agdelte.Storage.IndexedMap as IM using (IndexedMap)

------------------------------------------------------------------------
-- Index extractors (FK-based ℕ indexes; byUuid hashing deferred to the API layer)
------------------------------------------------------------------------

extActEng : Activity → List ℕ
extActEng a = aEngagementId a ∷ []

extPartEng : Participation → List ℕ
extPartEng p = prEngagementId p ∷ []

extPartParty : Participation → List ℕ
extPartParty p = prPartyId p ∷ []

-- secondary-index positions (typed-name layer over IndexedMap's ℕ positions, #P3)
actByEngagement  : ℕ
actByEngagement  = 0
partByEngagement : ℕ
partByEngagement = 0
partByParty      : ℕ
partByParty      = 1

------------------------------------------------------------------------
-- Base (no separate Indexes — they live inside each IndexedMap, #2)
------------------------------------------------------------------------

record Base : Set where
  constructor mkBase
  field
    parties        : IndexedMap Party
    engagements    : IndexedMap Engagement
    activities     : IndexedMap Activity         -- index 0: byEngagement
    participations : IndexedMap Participation     -- index 0: byEngagement, 1: byParty
    nextId         : ℕ
open Base public

emptyBase : Base
emptyBase = mkBase
  (IM.empty [])
  (IM.empty [])
  (IM.empty (extActEng ∷ []))
  (IM.empty (extPartEng ∷ extPartParty ∷ []))
  1

------------------------------------------------------------------------
-- Operations (typed per entity, #N5) + errors
------------------------------------------------------------------------

data CrmOp : Set where
  SetParty         : Party → CrmOp
  SetEngagement    : Engagement → CrmOp
  SetActivity      : Activity → CrmOp
  SetParticipation : Participation → CrmOp
  DelParty         : ℕ → CrmOp
  DelEngagement    : ℕ → CrmOp
  DelActivity      : ℕ → CrmOp
  DelParticipation : ℕ → CrmOp

data Err : Set where
  NotFound          : Err
  Conflict          : Err
  Insufficient      : Err
  InvalidTransition : Err
  Forbidden         : Err
  Invariant         : String → Err

------------------------------------------------------------------------
-- Apply (pure; maintains indexes via IndexedMap, advances nextId #N1)
------------------------------------------------------------------------

private
  bump : ℕ → ℕ → ℕ
  bump id n = suc id ⊔ n           -- nextId := max(nextId, id+1)

apply : CrmOp → Base → Base
apply (SetParty p) b =
  record b { parties = IM.insert (pId p) p (parties b) ; nextId = bump (pId p) (nextId b) }
apply (SetEngagement e) b =
  record b { engagements = IM.insert (eId e) e (engagements b) ; nextId = bump (eId e) (nextId b) }
apply (SetActivity a) b =
  record b { activities = IM.insert (aId a) a (activities b) ; nextId = bump (aId a) (nextId b) }
apply (SetParticipation p) b =
  record b { participations = IM.insert (prId p) p (participations b) ; nextId = bump (prId p) (nextId b) }
apply (DelParty id) b         = record b { parties        = IM.delete id (parties b) }
apply (DelEngagement id) b    = record b { engagements    = IM.delete id (engagements b) }
apply (DelActivity id) b      = record b { activities     = IM.delete id (activities b) }
apply (DelParticipation id) b = record b { participations = IM.delete id (participations b) }

------------------------------------------------------------------------
-- Op codec (tagged; record bodies via Crm.Wire). For the WAL (#D).
------------------------------------------------------------------------

encodeOp : CrmOp → String
encodeOp (SetParty p)          = "P" <> encParty p
encodeOp (SetEngagement e)     = "E" <> encEngagement e
encodeOp (SetActivity a)       = "A" <> encActivity a
encodeOp (SetParticipation p)  = "T" <> encParticipation p
encodeOp (DelParty id)         = "p" <> encℕ id
encodeOp (DelEngagement id)    = "e" <> encℕ id
encodeOp (DelActivity id)      = "a" <> encℕ id
encodeOp (DelParticipation id) = "t" <> encℕ id

private
  mP : Maybe Party → Maybe CrmOp
  mP (just x) = just (SetParty x)
  mP nothing  = nothing
  mE : Maybe Engagement → Maybe CrmOp
  mE (just x) = just (SetEngagement x)
  mE nothing  = nothing
  mA : Maybe Activity → Maybe CrmOp
  mA (just x) = just (SetActivity x)
  mA nothing  = nothing
  mT : Maybe Participation → Maybe CrmOp
  mT (just x) = just (SetParticipation x)
  mT nothing  = nothing
  mDel : (ℕ → CrmOp) → Maybe ℕ → Maybe CrmOp
  mDel f (just n) = just (f n)
  mDel f nothing  = nothing

decodeOp : String → Maybe CrmOp
decodeOp s with toList s
... | []         = nothing
... | (c ∷ rest) =
  let body = fromList rest in
  if      primCharEquality c 'P' then mP (decParty body)
  else if primCharEquality c 'E' then mE (decEngagement body)
  else if primCharEquality c 'A' then mA (decActivity body)
  else if primCharEquality c 'T' then mT (decParticipation body)
  else if primCharEquality c 'p' then mDel DelParty (decℕ body)
  else if primCharEquality c 'e' then mDel DelEngagement (decℕ body)
  else if primCharEquality c 'a' then mDel DelActivity (decℕ body)
  else if primCharEquality c 't' then mDel DelParticipation (decℕ body)
  else nothing
