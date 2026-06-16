{-# OPTIONS --without-K --guardedness #-}

-- Write-Ahead Log (WAL) persistence — WAL-ONLY (no snapshots; see ADR 0001).
-- All state lives in memory. A mutation is:
--   1. appended to the log as ONE byte-length-framed TRANSACTION record + fsync
--      (durable) — a whole `List Op` is one atomic unit;
--   2. only then made visible in the in-memory MVar.
-- Recovery = replay the log from the empty state. Concept: docs/concepts/
-- storage-model.md §18 (framing/atomicity), §6 (Txn).
--
-- Crash-safety design (Phase 3, hardened after review):
--   * unit of durability = the transaction (full op-list), one fsync (#1);
--   * durable-before-visible: modifyMVarMasked writes+fsyncs inside the masked
--     callback, then publishes the new state only after (#N4/#P2);
--   * OUTER framing (splitting the log into transaction records) is BYTE-level,
--     in the FFI (`appendWalRecord`/`readWalRecords`): tearing is a byte event and
--     lenient UTF-8 decode is not length-preserving, so char-length framing could
--     mis-classify a torn multi-byte tail. Byte framing drops a torn TAIL exactly;
--     mid-stream corruption (a boundary that isn't `<digits>:`) → `readWalRecords`
--     returns `nothing` → we refuse to start (never silently skip);
--   * INNER framing (the ops inside one record) is char-level here in Agda — safe,
--     because a complete record is intact, valid UTF-8;
--   * a complete record whose inner op is undecodable is also corruption → die.

module Agdelte.Storage.WAL where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; toList) renaming (_++_ to _<>_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Char using (Char)
open import Data.Product using (_×_; _,_)

open import Agdelte.FFI.Server using
  ( MVar; newMVar; readMVar; modifyMVarMasked; Pair2; mkPair2; die; tryCatch
  ; _>>=_; _>>_; pure )
open import Agdelte.FFI.FileSystem using
  ( appendWalRecord; readWalRecords )
open import Agdelte.Storage.Wire using (lp; readField)

------------------------------------------------------------------------
-- WAL configuration (WAL-only: no snapshot fields)
------------------------------------------------------------------------

record WalConfig (S Op : Set) : Set where
  constructor mkWalConfig
  field
    walLogPath       : String            -- path to WAL log file
    walApply         : Op → S → S        -- pure state transition
    walSerializeOp   : Op → String       -- operation → string (char-framed inside a record)
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
-- Transaction payload (INNER framing; the OUTER byte frame is added by
-- appendWalRecord). One transaction's ops, each char-length-prefixed:
--   payload = concat [ lp (serializeOp opᵢ) | opᵢ ∈ txn ]
------------------------------------------------------------------------

serializeTxn : ∀ {S Op} → WalConfig S Op → List Op → String
serializeTxn cfg ops = foldr (λ op acc → lp (walSerializeOp cfg op) <> acc) "" ops

------------------------------------------------------------------------
-- Apply one record's ops ATOMICALLY (all, or — on inner corruption — none).
-- The record is a complete, intact string (the FFI guaranteed byte-completeness),
-- so inner char-level framing within it is exact. Recurse on length-fuel because
-- Wire.readField doesn't expose a structural decrease (each op consumes ≥2 chars,
-- so fuel = length is sound; out-of-fuel-with-input-left is unreachable, fail closed).
------------------------------------------------------------------------

private
  applyRecord : ∀ {S Op} → WalConfig S Op → S → String → Maybe S
  applyRecord cfg s body = go (length (toList body)) s (toList body)
    where
      go : ℕ → _ → List Char → Maybe _
      go _        acc []          = just acc
      go zero     acc (_ ∷ _)     = nothing
      go (suc fu) acc cs@(_ ∷ _) with readField cs
      ... | nothing               = nothing                  -- malformed inner framing
      ... | just (payload , rest) with walDeserializeOp cfg payload
      ...   | nothing = nothing                              -- undecodable op
      ...   | just op = go fu (walApply cfg op acc) rest

  -- replay the complete records the FFI returned (torn tail already dropped).
  -- Structural recursion on the list; nothing ⇒ corruption inside a record.
  replayAll : ∀ {S Op} → WalConfig S Op → S → List String → Maybe S
  replayAll cfg s []       = just s
  replayAll cfg s (r ∷ rs) with applyRecord cfg s r
  ... | nothing = nothing
  ... | just s' = replayAll cfg s' rs

------------------------------------------------------------------------
-- Open: replay log from empty state
------------------------------------------------------------------------

walOpen : ∀ {S Op} → WalConfig S Op → IO (WalHandle S Op)
walOpen cfg =
  readWalRecords (walLogPath cfg) >>= λ where
    nothing   → die "WAL recovery: corrupt log framing — refusing to start (data-loss guard)"
    (just rs) → maybe (λ s₁ → newMVar s₁ >>= λ v → pure (mkWalHandle cfg v))
                      (die "WAL recovery: undecodable record — refusing to start (data-loss guard)")
                      (replayAll cfg (walEmptyState cfg) rs)

------------------------------------------------------------------------
-- Read current state (non-exclusive snapshot)
------------------------------------------------------------------------

walRead : ∀ {S Op} → WalHandle S Op → IO S
walRead h = readMVar (walState h)

------------------------------------------------------------------------
-- walTxn — the transaction primitive.
--
-- The txn is a PURE function S → E ⊎ (S × List Op × A): inspects the state and
-- either rejects (inj₁ e, no change) or yields the new state, the ops it emitted,
-- and a result. walTxn runs it inside modifyMVarMasked, so:
--   * forcing the txn and the durable write happen under one mask (#P2);
--   * the ops are one byte-framed record + one fsync, durable BEFORE the new
--     state is published (#1/#N4);
--   * a rejection writes nothing and leaves state untouched;
--   * an IO failure (disk) — OR an async cancellation — → modifyMVarMasked
--     restores state, re-raises → surfaced as `ioFailed` (state unchanged).
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

data WalOutcome (E A : Set) : Set where
  committed : A → WalOutcome E A   -- durably logged + applied
  rejected  : E → WalOutcome E A   -- txn said no; nothing written
  ioFailed  : WalOutcome E A       -- durable write failed / interrupted; state unchanged

walTxn : ∀ {S Op E A} → WalHandle S Op
       → (S → (E ⊎ (S × (List Op × A)))) → IO (WalOutcome E A)
walTxn {S} {Op} {E} {A} h txn =
  let cfg = walConfig h in
  tryCatch
    (modifyMVarMasked (walState h) (λ s → commit cfg s (txn s)))
    >>= λ where
      (just o) → pure o            -- callback returned an outcome
      nothing  → pure ioFailed     -- exception (disk/IO/cancel) → state restored
  where
    -- inside the masked callback: durable write THEN publish new state
    commit : WalConfig S Op → S → (E ⊎ (S × (List Op × A)))
           → IO (Pair2 S (WalOutcome E A))
    commit cfg s (inj₁ e)               = pure (mkPair2 s (rejected e))   -- no write, no change
    commit cfg s (inj₂ (s' , ops , a)) =
      appendWalRecord (walLogPath cfg) (serializeTxn cfg ops) >>   -- durable (write+fsync)
      pure (mkPair2 s' (committed a))                              -- visible only after durable

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
    appendWalRecord (walLogPath cfg) (serializeTxn cfg (op ∷ [])) >>
    pure (mkPair2 s' s'))

walModify : ∀ {S Op} → WalHandle S Op → (S → Maybe Op) → IO (Maybe S)
walModify h f =
  let cfg = walConfig h in
  modifyMVarMasked (walState h) (λ s →
    maybe (λ op →
            let s' = walApply cfg op s in
            appendWalRecord (walLogPath cfg) (serializeTxn cfg (op ∷ [])) >>
            pure (mkPair2 s' (just s')))
          (pure (mkPair2 s nothing))      -- nothing → no change, no write
          (f s))
