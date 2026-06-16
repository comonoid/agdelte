{-# OPTIONS --without-K #-}

-- Wire codecs for the CRM domain records (Phase 1). encode : A → String /
-- decode : String → Maybe A, built from the pure Agdelte.Storage.Wire primitives
-- (GHC + JS). Each record = concatenation of length-prefixed fields, decoded with
-- the reader monad. Must be round-trip: decode (encode x) ≡ just x (#N6).
module Crm.Wire where

open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Maybe using (Maybe; just; nothing)

open import Crm.Identity
open import Agdelte.Storage.Wire as W using (lp; encℕ; decℕ; encStr; decStr; encMaybeℕ; decMaybeℕ; encMaybeStr; decMaybeStr; fieldR; _>>=R_; returnR; runR)

------------------------------------------------------------------------
-- Enum codecs
------------------------------------------------------------------------

encPartyType : PartyType → String
encPartyType Person = "P"
encPartyType Org    = "O"
decPartyType : String → Maybe PartyType
decPartyType "P" = just Person
decPartyType "O" = just Org
decPartyType _   = nothing

encActStatus : ActStatus → String
encActStatus Scheduled = "S"
encActStatus Completed = "C"
encActStatus Canceled  = "X"
encActStatus NoShow    = "N"
decActStatus : String → Maybe ActStatus
decActStatus "S" = just Scheduled
decActStatus "C" = just Completed
decActStatus "X" = just Canceled
decActStatus "N" = just NoShow
decActStatus _   = nothing

------------------------------------------------------------------------
-- Party
------------------------------------------------------------------------

encParty : Party → String
encParty p =
  lp (encℕ (pId p)) <> lp (encPartyType (pType p)) <>
  lp (encStr (pDisplayName p)) <> lp (encStr (pTz p)) <> lp (encℕ (pCreatedAt p)) <>
  lp (encMaybeℕ (pDeletedAt p))

decParty : String → Maybe Party
decParty = runR (
  fieldR decℕ                >>=R λ i →
  fieldR decPartyType        >>=R λ t →
  fieldR decStr              >>=R λ dn →
  fieldR decStr              >>=R λ tz →
  fieldR decℕ                >>=R λ ca →
  fieldR decMaybeℕ     >>=R λ dd →
  returnR (mkParty i t dn tz ca dd))

------------------------------------------------------------------------
-- Engagement
------------------------------------------------------------------------

encEngagement : Engagement → String
encEngagement e =
  lp (encℕ (eId e)) <> lp (encℕ (eCaseType e)) <>
  lp (encℕ (eStage e)) <> lp (encMaybeStr (eTitle e)) <>
  lp (encℕ (eCreatedAt e)) <> lp (encMaybeℕ (eDeletedAt e))

decEngagement : String → Maybe Engagement
decEngagement = runR (
  fieldR decℕ                >>=R λ i →
  fieldR decℕ                >>=R λ ct →
  fieldR decℕ                >>=R λ st →
  fieldR decMaybeStr   >>=R λ ti →
  fieldR decℕ                >>=R λ ca →
  fieldR decMaybeℕ     >>=R λ dd →
  returnR (mkEngagement i ct st ti ca dd))

------------------------------------------------------------------------
-- Activity
------------------------------------------------------------------------

encActivity : Activity → String
encActivity a =
  lp (encℕ (aId a)) <> lp (encℕ (aEngagementId a)) <>
  lp (encℕ (aStartsAt a)) <> lp (encActStatus (aStatus a)) <>
  lp (encℕ (aCreatedAt a)) <> lp (encMaybeℕ (aDeletedAt a))

decActivity : String → Maybe Activity
decActivity = runR (
  fieldR decℕ                >>=R λ i →
  fieldR decℕ                >>=R λ eng →
  fieldR decℕ                >>=R λ sa →
  fieldR decActStatus        >>=R λ st →
  fieldR decℕ                >>=R λ ca →
  fieldR decMaybeℕ     >>=R λ dd →
  returnR (mkActivity i eng sa st ca dd))

------------------------------------------------------------------------
-- Participation (M:N fact)
------------------------------------------------------------------------

encParticipation : Participation → String
encParticipation p =
  lp (encℕ (prId p)) <> lp (encℕ (prEngagementId p)) <> lp (encℕ (prPartyId p)) <>
  lp (encStr (prRole p)) <> lp (encℕ (prCreatedAt p))

decParticipation : String → Maybe Participation
decParticipation = runR (
  fieldR decℕ                >>=R λ i →
  fieldR decℕ                >>=R λ eng →
  fieldR decℕ                >>=R λ pty →
  fieldR decStr              >>=R λ role →
  fieldR decℕ                >>=R λ ca →
  returnR (mkParticipation i eng pty role ca))

------------------------------------------------------------------------
-- Account (balance)
------------------------------------------------------------------------

encAccount : Account → String
encAccount a =
  lp (encℕ (acId a)) <> lp (encℕ (acBalance a)) <> lp (encℕ (acCreatedAt a))

decAccount : String → Maybe Account
decAccount = runR (
  fieldR decℕ                >>=R λ i →
  fieldR decℕ                >>=R λ bal →
  fieldR decℕ                >>=R λ ca →
  returnR (mkAccount i bal ca))
