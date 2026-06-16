{-# OPTIONS --without-K #-}

-- Crm.Commands — real domain transactions (Phase 4), the measure of whether the
-- store/Txn abstraction reads like ordinary FP. Each command is a `Txn`:
-- `getBase` to inspect, `requireJust`/`guardT` for invariants, `emit` to mutate,
-- `abort` to reject. Ids are allocated from `nextId b` (deterministic state);
-- uuids/timestamps come in as parameters from the IO boundary (#N2).
--
-- Demonstrated invariants:
--   * addParticipant      — FK: engagement & party must exist and be live;
--   * bookSession         — slot-free check via the byEngagement reverse index;
--   * cancelActivity      — status-transition guard (Scheduled → Canceled only);
--   * hardDeleteEngagement — cascade via reverse indexes (no dangling FK).
module Crm.Commands where

open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _≤?_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (yes; no)

open import Crm.Identity
open import Crm.Store
  using ( Base; CrmOp; Err
        ; SetParty; SetEngagement; SetActivity; SetParticipation; SetAccount
        ; DelActivity; DelParticipation; DelEngagement
        ; NotFound; Conflict; InvalidTransition; Insufficient
        ; engagements; parties; activities; participations; accounts; nextId
        ; actByEngagement; partByEngagement )
open import Crm.Txn
open import Agdelte.Storage.IndexedMap as IM using ()

------------------------------------------------------------------------
-- Small pure predicates
------------------------------------------------------------------------

live : Maybe ℕ → Bool                    -- soft-delete check: nothing = live
live nothing  = true
live (just _) = false

freesSlot : ActStatus → Bool             -- a canceled session releases its time slot
freesSlot Canceled = true
freesSlot _        = false

canCancel : ActStatus → Bool             -- only a scheduled session may be canceled
canCancel Scheduled = true
canCancel _         = false

anyℕ : (ℕ → Bool) → List ℕ → Bool
anyℕ p []       = false
anyℕ p (x ∷ xs) = p x ∨ anyℕ p xs

------------------------------------------------------------------------
-- create commands — allocate id from nextId; uuid + timestamp come from IO (#N2)
------------------------------------------------------------------------

createParty : PartyType → (name tz : String) → (now : ℕ) → Txn ℕ
createParty ty name tz now =
  getBase >>=T λ b →
  (let pid = nextId b in
   emit (SetParty (mkParty pid ty name tz now nothing)) >>T returnT pid)

createEngagement : (caseType stage : ℕ) → (now : ℕ) → Txn ℕ
createEngagement caseType stage now =
  getBase >>=T λ b →
  (let eid = nextId b in
   emit (SetEngagement (mkEngagement eid caseType stage nothing now nothing)) >>T returnT eid)

createAccount : (balance now : ℕ) → Txn ℕ
createAccount balance now =
  getBase >>=T λ b →
  (let aid = nextId b in
   emit (SetAccount (mkAccount aid balance now)) >>T returnT aid)

------------------------------------------------------------------------
-- addParticipant — FK check on both ends (exist + live), then link
------------------------------------------------------------------------

addParticipant : (engId partyId : ℕ) → Role → (now : ℕ) → Txn ℕ
addParticipant engId partyId role now =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup engId    (engagements b)) >>=T λ e →
  guardT (live (eDeletedAt e)) NotFound >>T
  requireJust NotFound (IM.lookup partyId  (parties b))     >>=T λ p →
  guardT (live (pDeletedAt p)) NotFound >>T
  (let pid = nextId b in
   emit (SetParticipation (mkParticipation pid engId partyId role now)) >>T
   returnT pid)

------------------------------------------------------------------------
-- bookSession — the slot must be free (no live, non-canceled activity at the
-- same time in this engagement). Reads the byEngagement reverse index.
------------------------------------------------------------------------

slotFree : Base → ℕ → ℕ → Bool
slotFree b engId t =
  not (anyℕ conflicts (IM.byIndex actByEngagement engId (activities b)))
  where
    conflicts : ℕ → Bool
    conflicts aid with IM.lookup aid (activities b)
    ... | nothing = false
    ... | just a  = (aStartsAt a == t) ∧ not (freesSlot (aStatus a)) ∧ live (aDeletedAt a)

bookSession : (engId : ℕ) → (startsAt now : ℕ) → Txn ℕ
bookSession engId startsAt now =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup engId (engagements b)) >>=T λ e →
  guardT (live (eDeletedAt e)) NotFound >>T
  guardT (slotFree b engId startsAt) Conflict >>T
  (let aid = nextId b in
   emit (SetActivity (mkActivity aid engId startsAt Scheduled now nothing)) >>T
   returnT aid)

------------------------------------------------------------------------
-- cancelActivity — status transition guarded (Scheduled → Canceled)
------------------------------------------------------------------------

cancelActivity : (actId : ℕ) → Txn ⊤
cancelActivity actId =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup actId (activities b)) >>=T λ a →
  guardT (canCancel (aStatus a)) InvalidTransition >>T
  emit (SetActivity (record a { aStatus = Canceled }))

------------------------------------------------------------------------
-- hardDeleteEngagement — explicit cascade via reverse indexes (no dangling FK)
------------------------------------------------------------------------

hardDeleteEngagement : (engId : ℕ) → Txn ⊤
hardDeleteEngagement engId =
  getBase >>=T λ b →
  forEachT (IM.byIndex actByEngagement  engId (activities b))     (λ aid → emit (DelActivity aid))      >>T
  forEachT (IM.byIndex partByEngagement engId (participations b)) (λ pid → emit (DelParticipation pid)) >>T
  emit (DelEngagement engId)

------------------------------------------------------------------------
-- soft-delete (SPEC §5.7: tombstone, not physical removal). Sets *DeletedAt;
-- the `live` FK-guards then reject it, and read endpoints filter it out (L3).
-- NB: reverse indexes still contain the tombstone — call sites filter `live`
-- (slotFree, list reads); a future live-aware extractor could drop them eagerly.
------------------------------------------------------------------------

softDeleteParty : (partyId now : ℕ) → Txn ⊤
softDeleteParty pid now =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup pid (parties b)) >>=T λ p →
  emit (SetParty (record p { pDeletedAt = just now }))

softDeleteEngagement : (engId now : ℕ) → Txn ⊤
softDeleteEngagement eid now =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup eid (engagements b)) >>=T λ e →
  emit (SetEngagement (record e { eDeletedAt = just now }))

------------------------------------------------------------------------
-- charge — value-invariant CORRECT-BY-CONSTRUCTION (balance never negative).
--
-- `debit` cannot even be CALLED without a proof `amt ≤ bal`; the only way to
-- obtain that proof is the `yes` branch of the decidable `_≤?_`, and the `no`
-- branch is forced to `abort Insufficient`. So no `charge` that typechecks can
-- silently underflow/clamp the balance. No postulate / primTrustMe / TERMINATING.
------------------------------------------------------------------------

debit : (bal amt : ℕ) → amt ≤ bal → ℕ      -- proof-gated; result is the true difference
debit bal amt _ = bal ∸ amt

private
  chargeAcc : Account → ℕ → Txn ⊤
  chargeAcc a amt with amt ≤? acBalance a
  ... | yes pf = emit (SetAccount (record a { acBalance = debit (acBalance a) amt pf }))
  ... | no  _  = abort Insufficient

charge : (accId amt : ℕ) → Txn ⊤
charge accId amt =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup accId (accounts b)) >>=T λ a →
  chargeAcc a amt

credit : (accId amt : ℕ) → Txn ⊤           -- top-up; no proof obligation
credit accId amt =
  getBase >>=T λ b →
  requireJust NotFound (IM.lookup accId (accounts b)) >>=T λ a →
  emit (SetAccount (record a { acBalance = acBalance a + amt }))
