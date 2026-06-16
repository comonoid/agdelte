{-# OPTIONS --without-K --guardedness #-}

-- Write-Ahead Log (WAL) persistence — WAL-ONLY (no snapshots; see ADR 0001).
-- All state lives in memory. A mutation is:
--   1. appended to the log as ONE length-prefixed TRANSACTION record + fsync
--      (durable) — a whole `List Op` is one atomic unit;
--   2. only then made visible in the in-memory MVar.
-- Recovery = replay the log from the empty state. Concept: docs/concepts/
-- storage-model.md §18 (framing/atomicity), §6 (Txn).
--
-- Crash-safety design (Phase 3):
--   * unit of durability = the transaction (full op-list), one fsync (B/#1);
--   * durable-before-visible: modifyMVarMasked writes+fsyncs inside the masked
--     callback, then publishes the new state only after (C/E/F/#N4/#P2);
--   * recovery reads length-prefixed records: a torn TAIL record is dropped
--     WHOLE (atomicity preserved); a fully-present but undecodable record is
--     CORRUPTION → refuse to start (D), never silently skip;
--   * the log is read leniently (readWalLog) so a torn UTF-8 tail can't make a
--     strict decode throw and discard the entire history (A).

module Agdelte.Storage.WAL where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.String using (String; toList; fromList) renaming (_++_ to _<>_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_; length; splitAt; foldr)
open import Data.Char using (Char; isDigit)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Char using (primCharToNat; primCharEquality)

open import Agdelte.FFI.Server using
  ( MVar; newMVar; readMVar; modifyMVarMasked; Pair2; mkPair2; die
  ; _>>=_; _>>_; pure )
open import Agdelte.FFI.FileSystem using
  ( appendFileText; readWalLog )
open import Agdelte.Storage.Wire using (lp; readField)

------------------------------------------------------------------------
-- WAL configuration (WAL-only: no snapshot fields)
------------------------------------------------------------------------

record WalConfig (S Op : Set) : Set where
  constructor mkWalConfig
  field
    walLogPath       : String            -- path to WAL log file
    walApply         : Op → S → S        -- pure state transition
    walSerializeOp   : Op → String       -- operation → string (length-prefixed by framing)
    walDeserializeOp : String → Maybe Op -- string → operation (nothing = undecodable)
    walEmptyState    : S                 -- initial empty state (replay starts here)

open WalConfig public

------------------------------------------------------------------------
-- WAL handle (mutable, single-writer; reads are non-exclusive)
------------------------------------------------------------------------

record WalHandle (S Op : Set) : Set where
  constructor mkWalHandle
  field
    walConfig : WalConfig S Op
    walState  : MVar S
open WalHandle public

------------------------------------------------------------------------
-- Transaction framing (pure; reuses Wire's length-prefix `lp`)
--
--   record  = lp ( concat [ lp (serializeOp opᵢ) | opᵢ ∈ txn ] )
--
-- outer lp frames the whole transaction as one atomic record; inner lp frames
-- each op so recovery can split them. Character-level lengths are consistent
-- across the UTF-8 round-trip (we always parse the decoded text, never bytes).
------------------------------------------------------------------------

frameTxn : ∀ {S Op} → WalConfig S Op → List Op → String
frameTxn cfg ops = lp (foldr (λ op acc → lp (walSerializeOp cfg op) <> acc) "" ops)

------------------------------------------------------------------------
-- Recovery: a length-verifying record stream reader.
--
-- Wire.readField is NOT enough here: its splitAt silently truncates, so it
-- can't tell a torn tail from a short payload. This reader checks that the
-- declared length is actually present, distinguishing:
--   recOk   — one complete record body + rest
--   recTorn — trailing partial record (drop it; atomicity preserved)
--   recBad  — malformed header (corruption → fatal)
--   recEnd  — clean end of input
------------------------------------------------------------------------

private
  spanDigits : List Char → (List Char × List Char)
  spanDigits []       = ([] , [])
  spanDigits (c ∷ cs) = if isDigit c
    then (let r = spanDigits cs in (c ∷ proj₁ r , proj₂ r))
    else ([] , c ∷ cs)

  -- read the natural number formed by `ds` (all digit chars)
  readNat : List Char → ℕ
  readNat = go 0
    where
      go : ℕ → List Char → ℕ
      go acc []       = acc
      go acc (c ∷ cs) = go (acc * 10 + (primCharToNat c ∸ primCharToNat '0')) cs

data RecRead : Set where
  recEnd  : RecRead
  recTorn : RecRead
  recBad  : RecRead
  recOk   : String → List Char → RecRead

readRecord : List Char → RecRead
readRecord []         = recEnd
readRecord cs@(_ ∷ _) with spanDigits cs
... | ([]     , _)            = recBad             -- expected a length prefix
... | (d ∷ ds , [])           = recTorn            -- digits but no ':' yet → torn header
... | (d ∷ ds , sep ∷ rest)   =
        if primCharEquality sep ':'
        then (let n  = readNat (d ∷ ds)
                  sp = splitAt n rest
                  body = proj₁ sp
              in if length body ≡ᵇ n
                 then recOk (fromList body) (proj₂ sp)   -- full record present
                 else recTorn)                            -- declared len > available → torn tail
        else recBad

------------------------------------------------------------------------
-- Apply one record's ops ATOMICALLY (all or — on inner corruption — none).
------------------------------------------------------------------------

-- Both replay loops walk a List Char that the framing readers shrink by ≥2
-- chars per step (≥1 length digit + ':'), but neither reader exposes that
-- structurally — so we recurse on explicit length-fuel (= initial length),
-- which is a sound decreasing measure. Out-of-fuel with input left is
-- unreachable; we fail closed (nothing) rather than silently drop.
private
  applyRecord : ∀ {S Op} → WalConfig S Op → S → String → Maybe S
  applyRecord cfg s body = go (length (toList body)) s (toList body)
    where
      go : ℕ → _ → List Char → Maybe _
      go _        acc []          = just acc
      go zero     acc (_ ∷ _)     = nothing
      go (suc fu) acc cs@(_ ∷ _) with readField cs
      ... | nothing               = nothing                       -- malformed inner framing
      ... | just (payload , rest) with walDeserializeOp cfg payload
      ...   | nothing = nothing                                   -- undecodable op
      ...   | just op = go fu (walApply cfg op acc) rest

  replayGo : ∀ {S Op} → ℕ → WalConfig S Op → S → List Char → Maybe S
  -- nothing ⇒ corruption (fatal); just s ⇒ recovered state (torn tail dropped)
  replayGo _        cfg s []         = just s
  replayGo zero     cfg s (_ ∷ _)    = nothing
  replayGo (suc fu) cfg s cs@(_ ∷ _) with readRecord cs
  ... | recEnd        = just s
  ... | recTorn       = just s                       -- drop torn trailing record
  ... | recBad        = nothing                      -- malformed → fatal
  ... | recOk body more with applyRecord cfg s body
  ...   | nothing = nothing                           -- inner corruption → fatal
  ...   | just s' = replayGo fu cfg s' more

  replayRecords : ∀ {S Op} → WalConfig S Op → S → List Char → Maybe S
  replayRecords cfg s cs = replayGo (length cs) cfg s cs

------------------------------------------------------------------------
-- Open: replay log from empty state
------------------------------------------------------------------------

walOpen : ∀ {S Op} → WalConfig S Op → IO (WalHandle S Op)
walOpen cfg =
  readWalLog (walLogPath cfg) >>= λ d →
  (maybe (λ s₁ → newMVar s₁ >>= λ v → pure (mkWalHandle cfg v))
         (die "WAL recovery: corrupt log record — refusing to start (data-loss guard)")
         (replayRecords cfg (walEmptyState cfg) (toList d)))

------------------------------------------------------------------------
-- Read current state (non-exclusive snapshot)
------------------------------------------------------------------------

walRead : ∀ {S Op} → WalHandle S Op → IO S
walRead h = readMVar (walState h)

------------------------------------------------------------------------
-- walTxn — the transaction primitive.
--
-- The txn is a PURE function S → Either E (S × List Op × A): it inspects the
-- current state and either rejects (Left e, no change) or yields the new state,
-- the ops it emitted, and a result. walTxn runs it inside modifyMVarMasked, so:
--   * forcing the txn and the durable write happen under one mask (C/E/F);
--   * the ops are framed as ONE record + ONE fsync, durable BEFORE the new
--     state is published (#1/B/#N4);
--   * a rejection writes nothing and leaves state untouched;
--   * an IO failure (disk) → modifyMVarMasked restores state, re-raises →
--     surfaced as `ioFailed` (state unchanged, caller may retry).
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

data WalOutcome (E A : Set) : Set where
  committed : A → WalOutcome E A   -- durably logged + applied
  rejected  : E → WalOutcome E A   -- txn said no; nothing written
  ioFailed  : WalOutcome E A       -- durable write failed; state unchanged

open import Agdelte.FFI.Server using (tryCatch)

walTxn : ∀ {S Op E A} → WalHandle S Op
       → (S → (E ⊎ (S × (List Op × A)))) → IO (WalOutcome E A)
walTxn {S} {Op} {E} {A} h txn =
  let cfg = walConfig h in
  tryCatch
    (modifyMVarMasked (walState h) (λ s →
      commit cfg s (txn s)))
    >>= λ where
      (just o) → pure o            -- callback returned an outcome
      nothing  → pure ioFailed     -- exception (disk/IO) → state restored
  where
    -- inside the masked callback: durable write THEN publish new state
    commit : WalConfig S Op → S → (E ⊎ (S × (List Op × A)))
           → IO (Pair2 S (WalOutcome E A))
    commit cfg s (inj₁ e)               = pure (mkPair2 s (rejected e))   -- no write, no change
    commit cfg s (inj₂ (s' , ops , a)) =
      appendFileText (walLogPath cfg) (frameTxn cfg ops) >>   -- durable (write+fsync)
      pure (mkPair2 s' (committed a))                          -- visible only after durable

------------------------------------------------------------------------
-- walStep / walModify — single-op convenience wrappers over the same framing.
-- Kept for existing callers (Payment, Auth). On IO failure they re-raise (like
-- before); domain code that needs the error channel should use walTxn.
------------------------------------------------------------------------

walStep : ∀ {S Op} → WalHandle S Op → Op → IO S
walStep h op =
  let cfg = walConfig h in
  modifyMVarMasked (walState h) (λ s →
    let s' = walApply cfg op s in
    appendFileText (walLogPath cfg) (frameTxn cfg (op ∷ [])) >>
    pure (mkPair2 s' s'))

walModify : ∀ {S Op} → WalHandle S Op → (S → Maybe Op) → IO (Maybe S)
walModify h f =
  let cfg = walConfig h in
  modifyMVarMasked (walState h) (λ s →
    maybe (λ op →
            let s' = walApply cfg op s in
            appendFileText (walLogPath cfg) (frameTxn cfg (op ∷ [])) >>
            pure (mkPair2 s' (just s')))
          (pure (mkPair2 s nothing))      -- nothing → no change, no write
          (f s))
