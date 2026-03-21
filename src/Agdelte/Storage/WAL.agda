{-# OPTIONS --without-K --guardedness #-}

-- Write-Ahead Log (WAL) persistence.
-- All state lives in memory. Mutations are:
--   1. Appended to log file (durability)
--   2. Applied to in-memory state (speed)
-- Periodic snapshots allow log truncation.
-- Recovery: load snapshot + replay log.

module Agdelte.Storage.WAL where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_)

open import Agdelte.FFI.Server using
  ( IORef; newIORef; readIORef; writeIORef
  ; MVar; newMVar; takeMVar; putMVar
  ; _>>=_; _>>_; pure; bracket; mask; onException
  )
open import Agdelte.FFI.FileSystem using
  ( readFileSafe; writeFileText; appendFileText; doesFileExist'; renameFile )

------------------------------------------------------------------------
-- WAL configuration
------------------------------------------------------------------------

record WalConfig (S Op : Set) : Set where
  constructor mkWalConfig
  field
    walLogPath      : String            -- path to WAL log file
    walSnapshotPath : String            -- path to snapshot file
    walApply        : Op → S → S        -- pure state transition
    walSerializeOp  : Op → String       -- operation → one line
    walDeserializeOp : String → Maybe Op -- line → operation (Nothing = skip)
    walSerializeState : S → String      -- state → snapshot string
    walDeserializeState : String → S    -- snapshot string → state
    walEmptyState   : S                 -- initial empty state

open WalConfig public

------------------------------------------------------------------------
-- WAL handle (mutable, thread-safe)
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)

record WalHandle (S Op : Set) : Set where
  constructor mkWalHandle
  field
    walConfig  : WalConfig S Op
    walState   : MVar S              -- mutex-protected state
    walOpCount : IORef ℕ             -- operations since last snapshot

open WalHandle public

------------------------------------------------------------------------
-- Split string by newlines (for log replay)
------------------------------------------------------------------------

postulate
  splitLines : String → List String

{-# FOREIGN GHC
  import qualified Data.Text as T

  splitLinesImpl :: T.Text -> [T.Text]
  splitLinesImpl t = filter (not . T.null) (T.lines t)
  #-}
{-# COMPILE GHC splitLines = splitLinesImpl #-}

------------------------------------------------------------------------
-- Initialize: load snapshot + replay log
------------------------------------------------------------------------

private
  replayLog : ∀ {S Op} → WalConfig S Op → S → List String → S
  replayLog _ s [] = s
  replayLog cfg s (line ∷ lines) with walDeserializeOp cfg line
  ... | nothing = replayLog cfg s lines
  ... | just op = replayLog cfg (walApply cfg op s) lines

  loadSnapshot : ∀ {S Op} → WalConfig S Op → IO S
  loadSnapshot cfg =
    doesFileExist' (walSnapshotPath cfg) >>= λ where
      false → pure (walEmptyState cfg)
      true  → readFileSafe (walSnapshotPath cfg) >>= λ d →
              pure (walDeserializeState cfg d)

  loadAndReplay : ∀ {S Op} → WalConfig S Op → S → IO S
  loadAndReplay cfg s₀ =
    doesFileExist' (walLogPath cfg) >>= λ where
      false → pure s₀
      true  → readFileSafe (walLogPath cfg) >>= λ d →
              pure (replayLog cfg s₀ (splitLines d))

walOpen : ∀ {S Op} → WalConfig S Op → IO (WalHandle S Op)
walOpen cfg =
  loadSnapshot cfg >>= λ s₀ →
  loadAndReplay cfg s₀ >>= λ s₁ →
  newMVar s₁ >>= λ stateVar →
  newIORef zero >>= λ countRef →
  pure (mkWalHandle cfg stateVar countRef)

------------------------------------------------------------------------
-- Step: append to log + apply to state (atomic)
------------------------------------------------------------------------

walStep : ∀ {S Op} → WalHandle S Op → Op → IO S
walStep h op =
  let cfg = walConfig h
      line = walSerializeOp cfg op ++ "\n"
  in
  takeMVar (walState h) >>= λ s →
  onException
    (appendFileText (walLogPath cfg) line >>
     let s' = walApply cfg op s
     in mask (putMVar (walState h) s' >>
              readIORef (walOpCount h) >>= λ n →
              writeIORef (walOpCount h) (suc n)) >>
        pure s')
    (putMVar (walState h) s)  -- restore MVar on exception

------------------------------------------------------------------------
-- Read current state (no mutation)
------------------------------------------------------------------------

walRead : ∀ {S Op} → WalHandle S Op → IO S
walRead h =
  bracket (takeMVar (walState h)) (putMVar (walState h)) (λ s → pure s)

------------------------------------------------------------------------
-- Atomic read-modify-write
------------------------------------------------------------------------

-- | Read state under lock, apply guard function.
-- If it returns Just op → append to log, apply, return Just newState.
-- If Nothing → no change, return Nothing.
-- Prevents TOCTOU races between walRead and walStep.
walModify : ∀ {S Op} → WalHandle S Op → (S → Maybe Op) → IO (Maybe S)
walModify h f =
  takeMVar (walState h) >>= λ s →
  maybe
    (λ op →
      let cfg  = walConfig h
          line = walSerializeOp cfg op ++ "\n"
      in onException
        (appendFileText (walLogPath cfg) line >>
         let s' = walApply cfg op s
         in mask (putMVar (walState h) s' >>
                  readIORef (walOpCount h) >>= λ n →
                  writeIORef (walOpCount h) (suc n)) >>
            pure (just s'))
        (putMVar (walState h) s))
    (putMVar (walState h) s >> pure nothing)
    (f s)

------------------------------------------------------------------------
-- Snapshot: write full state, truncate log
------------------------------------------------------------------------

walSnapshot : ∀ {S Op} → WalHandle S Op → IO ⊤
walSnapshot h =
  let cfg = walConfig h
      tmpPath = walSnapshotPath cfg ++ ".tmp"
  in
  takeMVar (walState h) >>= λ s →
  onException
    (-- Atomic snapshot: write to temp file, then rename (POSIX atomic)
     writeFileText tmpPath (walSerializeState cfg s) >>
     renameFile tmpPath (walSnapshotPath cfg) >>
     -- Only truncate log AFTER snapshot is safely on disk
     writeFileText (walLogPath cfg) "" >>
     writeIORef (walOpCount h) zero >>
     putMVar (walState h) s)
    (putMVar (walState h) s)  -- restore MVar on exception

------------------------------------------------------------------------
-- Step + auto-snapshot (every N operations)
------------------------------------------------------------------------

walStepAutoSnapshot : ∀ {S Op} → WalHandle S Op → ℕ → Op → IO S
walStepAutoSnapshot h threshold op =
  walStep h op >>= λ s' →
  readIORef (walOpCount h) >>= λ n →
  (if threshold <ᵇ n then walSnapshot h else pure tt) >>
  pure s'
  where
    open import Agda.Builtin.Unit using (tt)
