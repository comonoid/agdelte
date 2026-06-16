{-# OPTIONS --without-K --guardedness #-}

-- Crm.Api — headless HTTP entry (Phase 5, SPEC §13). GHC-only.
--   GET  → walRead + query → {"data": …}
--   POST → parse JSON body → build a Txn → walTxn → {"data": …} | {"error": …}
-- The engine (walTxn/walRead) is domain-agnostic; this module is the thin glue
-- that maps HTTP ↔ Crm.Commands and shapes the {data}/{error} envelope.
module Crm.Api where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using () renaming (_++_ to _<>_)
open import Agdelte.Util using (case_of_)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse; reqMethod; reqPath; reqBody; reqHeaders; lookupHeader
  ; mkResponse; eqStrCI; _>>=_; _>>_; pure )
open import Agdelte.FFI.Json using (jsonGetField; jsonGetNat; escapeJsonString)
open import Agdelte.FFI.Time using (getCurrentTime)
open import Agdelte.Storage.WAL using
  ( WalConfig; mkWalConfig; WalHandle; walRead; walTxn
  ; WalOutcome; committed; rejected; ioFailed )
import Agdelte.Storage.IndexedMap as IM

open import Crm.Identity
open import Crm.Store
open import Crm.Txn using (Txn; runTxn)
open import Crm.Commands

------------------------------------------------------------------------
-- WAL config for the CRM
------------------------------------------------------------------------

crmConfig : String → WalConfig Base CrmOp
crmConfig path = mkWalConfig path apply encodeOp decodeOp emptyBase

------------------------------------------------------------------------
-- Envelope + Err mapping
------------------------------------------------------------------------

okJson : String → HttpResponse
okJson body = mkResponse 200 ("{\"data\":" <> body <> "}")

-- structured error envelope {"error":{"code","message"}} (§13)
errJson : ℕ → String → String → HttpResponse
errJson status code msg =
  mkResponse status ("{\"error\":{\"code\":\"" <> code <> "\",\"message\":\""
                     <> escapeJsonString msg <> "\"}}")

errResp : Err → HttpResponse
errResp NotFound          = errJson 404 "not_found"          "not found"
errResp Conflict          = errJson 409 "conflict"           "conflict"
errResp Insufficient      = errJson 402 "insufficient_funds" "insufficient funds"
errResp InvalidTransition = errJson 409 "invalid_transition" "invalid transition"
errResp Forbidden         = errJson 403 "forbidden"          "forbidden"
errResp (Invariant m)     = errJson 400 "validation"         m

-- run a Txn returning an id, render {data} / {error}
commit : WalHandle Base CrmOp → Txn ℕ → IO HttpResponse
commit h tx =
  walTxn h (runTxn tx) >>= λ where
    (committed id) → pure (okJson ("{\"id\":" <> show id <> "}"))
    (rejected e)   → pure (errResp e)
    ioFailed       → pure (errJson 503 "internal" "storage write failed")

------------------------------------------------------------------------
-- JSON encoders for reads (minimal, hand-written)
------------------------------------------------------------------------

private
  str : String → String
  str s = "\"" <> escapeJsonString s <> "\""

  array : List String → String
  array xs = "[" <> foldr joinC "" xs <> "]"
    where
      joinC : String → String → String
      joinC x ""   = x
      joinC x acc  = x <> "," <> acc

partyJson : Party → String
partyJson p =
  "{\"id\":" <> show (pId p) <> ",\"name\":" <> str (pDisplayName p) <> "}"

accountJson : Account → String
accountJson a =
  "{\"id\":" <> show (acId a) <> ",\"balance\":" <> show (acBalance a) <> "}"

------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------

private
  -- "P"/"O" → PartyType (default Person)
  parseType : Maybe String → PartyType
  parseType (just "O") = Org
  parseType _          = Person

  listJson : ∀ {V : Set} → (V → String) → IM.IndexedMap V → String
  listJson enc m = array (map (λ p → enc (proj₂ p)) (IM.toList m))

  -- list only rows the predicate keeps (L3: drop soft-deleted from read endpoints)
  liveJson : ∀ {V : Set} → (V → Bool) → (V → String) → IM.IndexedMap V → String
  liveJson keep enc m = array (map (λ p → enc (proj₂ p)) (filterᵇ (λ p → keep (proj₂ p)) (IM.toList m)))

-- POST /parties  {"name":…, "type":"P"|"O", "tz":…}
postParty : WalHandle Base CrmOp → HttpRequest → IO HttpResponse
postParty h req =
  let body = reqBody req in
  case jsonGetField "name" body of λ where
    nothing      → pure (errJson 400 "validation" "missing name")
    (just name)  →
      getCurrentTime >>= λ now →
      let ty = parseType (jsonGetField "type" body)
          tz = maybeStr (jsonGetField "tz" body)
      in commit h (createParty ty name tz now)
  where
    maybeStr : Maybe String → String
    maybeStr (just s) = s
    maybeStr nothing  = "UTC"

-- POST /accounts  {"balance":N}
postAccount : WalHandle Base CrmOp → HttpRequest → IO HttpResponse
postAccount h req =
  let body = reqBody req in
  case jsonGetNat "balance" body of λ where
    nothing      → pure (errJson 400 "validation" "missing balance")
    (just bal)   →
      getCurrentTime >>= λ now →
      commit h (createAccount bal now)

-- POST /charge  {"acc":id, "amt":N}
postCharge : WalHandle Base CrmOp → HttpRequest → IO HttpResponse
postCharge h req =
  let body = reqBody req in
  case (jsonGetNat "acc" body , jsonGetNat "amt" body) of λ where
    (just acc , just amt) →
      walTxn h (runTxn (charge acc amt)) >>= λ where
        (committed _) → pure (okJson "{\"ok\":true}")
        (rejected e)  → pure (errResp e)
        ioFailed      → pure (errJson 503 "internal" "storage write failed")
    _ → pure (errJson 400 "validation" "missing acc/amt")

-- GET /parties → live parties only (L3); GET /accounts → all accounts (no soft-delete field)
getParties : WalHandle Base CrmOp → IO HttpResponse
getParties h = walRead h >>= λ b →
  pure (okJson (liveJson (λ p → live (pDeletedAt p)) partyJson (parties b)))

getAccounts : WalHandle Base CrmOp → IO HttpResponse
getAccounts h = walRead h >>= λ b → pure (okJson (listJson accountJson (accounts b)))

------------------------------------------------------------------------
-- Router (with optional bearer-token gate, H1)
------------------------------------------------------------------------

private
  is : String → String → Bool
  is a b = eqStrCI a b

  -- token "" ⇒ no auth required (loopback-only deploys); else require exact Bearer
  authOk : String → HttpRequest → Bool
  authOk tok req with primStringEquality tok ""
  ... | true  = true
  ... | false with lookupHeader "authorization" (reqHeaders req)
  ...   | just v  = primStringEquality v ("Bearer " <> tok)
  ...   | nothing = false

  dispatch : WalHandle Base CrmOp → HttpRequest → IO HttpResponse
  dispatch h req =
    let m = reqMethod req ; p = reqPath req in
    if is m "GET" then
      (if is p "/parties"  then getParties h
       else if is p "/accounts" then getAccounts h
       else pure (errJson 404 "not_found" "no route"))
    else if is m "POST" then
      (if is p "/parties"  then postParty h req
       else if is p "/accounts" then postAccount h req
       else if is p "/charge"   then postCharge h req
       else pure (errJson 404 "not_found" "no route"))
    else pure (errJson 405 "validation" "method not allowed")

-- token comes from the entry module (env CRM_TOKEN; "" = open, loopback-only)
route : String → WalHandle Base CrmOp → HttpRequest → IO HttpResponse
route token h req =
  if authOk token req then dispatch h req
  else pure (errJson 401 "unauthorized" "missing or invalid bearer token")
