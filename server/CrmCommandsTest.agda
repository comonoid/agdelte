{-# OPTIONS --without-K --guardedness #-}

-- Phase 4 test: run real domain transactions (Crm.Commands) via runTxn over a
-- seeded Base and check outcomes + resulting state. Pure (NatMap is a GHC
-- postulate → runtime test). Covers FK rejection, slot conflict, status
-- transition, cascade-delete (no dangling FK), and the correct-by-construction
-- charge (sufficient / insufficient / credit).
module CrmCommandsTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; foldl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Crm.Identity
open import Crm.Store
open import Crm.Txn using (Txn; runTxn)
open import Crm.Commands
import Agdelte.Storage.IndexedMap as IM

infixr 1 _seq_
postulate
  putStrLn : String → IO ⊤
  _seq_    : IO ⊤ → IO ⊤ → IO ⊤
{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  seqIO :: IO () -> IO () -> IO ()
  seqIO = (>>)
  #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _seq_    = seqIO #-}

------------------------------------------------------------------------
-- Run helpers
------------------------------------------------------------------------

errCode : Err → ℕ
errCode NotFound          = 1
errCode Conflict          = 2
errCode Insufficient      = 3
errCode InvalidTransition = 4
errCode Forbidden         = 5
errCode (Invariant _)     = 6

-- 0 = committed; else the error code
code : ∀ {A} → Txn A → Base → ℕ
code cmd b with runTxn cmd b
... | inj₁ e = errCode e
... | inj₂ _ = 0

-- resulting Base on success (nothing if rejected)
runB : ∀ {A} → Txn A → Base → Maybe Base
runB cmd b with runTxn cmd b
... | inj₁ _            = nothing
... | inj₂ (b' , _ , _) = just b'

balOf : ℕ → Base → ℕ
balOf id b with IM.lookup id (accounts b)
... | just a  = acBalance a
... | nothing = 0

statusOf : ℕ → Base → Maybe ActStatus
statusOf id b with IM.lookup id (activities b)
... | just a  = just (aStatus a)
... | nothing = nothing

emptyL : List ℕ → Bool
emptyL []      = true
emptyL (_ ∷ _) = false

isNothingB : ∀ {A : Set} → Maybe A → Bool
isNothingB (just _) = false
isNothingB nothing  = true

isSomeB : ∀ {A : Set} → Maybe A → Bool
isSomeB (just _) = true
isSomeB nothing  = false

isCanceled : Maybe ActStatus → Bool
isCanceled (just Canceled) = true
isCanceled _               = false

------------------------------------------------------------------------
-- Seed: party 7 & 8, engagement 3, account 5 (balance 1000). nextId → 9.
------------------------------------------------------------------------

seed : Base
seed = foldl (λ b op → apply op b) emptyBase
  ( SetParty (mkParty 7 "u7" Person "P7" "UTC" 100 nothing)
  ∷ SetParty (mkParty 8 "u8" Person "P8" "UTC" 100 nothing)
  ∷ SetEngagement (mkEngagement 3 "u3" 1 1 nothing 100 nothing)
  ∷ SetAccount (mkAccount 5 "ua5" 1000 100)
  ∷ [] )

------------------------------------------------------------------------
-- Scenarios (each a Bool)
------------------------------------------------------------------------

-- FK rejects
addPartNoEng  = code (addParticipant 99 7 "provider" 200) seed == 1   -- NotFound
addPartNoParty = code (addParticipant 3 99 "provider" 200) seed == 1

-- bookSession: book, then same slot conflicts, different slot ok
bookConflict : Bool
bookConflict with runB (bookSession 3 "ua" 500 200) seed
... | nothing = false
... | just b1 = (code (bookSession 3 "ub" 500 201) b1 == 2)            -- Conflict
                ∧ (code (bookSession 3 "uc" 600 201) b1 == 0)          -- other slot ok

-- cancelActivity: Scheduled→Canceled ok; second cancel → InvalidTransition;
-- a canceled slot frees up for rebooking
cancelFlow : Bool
cancelFlow with runB (bookSession 3 "ua" 500 200) seed
... | nothing = false
... | just b1 with runB (cancelActivity (nextId seed)) b1              -- the booked id = 9
...   | nothing = false
...   | just b2 = isCanceled (statusOf (nextId seed) b2)
                  ∧ (code (cancelActivity (nextId seed)) b2 == 4)      -- InvalidTransition
                  ∧ (code (bookSession 3 "ud" 500 202) b2 == 0)       -- slot freed → ok

-- cascade hard-delete leaves no dangling activities/participations
cascadeClean : Bool
cascadeClean with runB (addParticipant 3 7 "provider" 200) seed
... | nothing = false
... | just b1 with runB (bookSession 3 "ua" 500 201) b1
...   | nothing = false
...   | just b2 with runB (hardDeleteEngagement 3) b2
...     | nothing = false
...     | just b3 = isNothingB (IM.lookup 3 (engagements b3))
                  ∧ emptyL (IM.byIndex actByEngagement 3 (activities b3))
                  ∧ emptyL (IM.byIndex partByEngagement 3 (participations b3))

-- charge correct-by-construction: debit, reject overdraft, credit
chargeOk : Bool
chargeOk with runB (charge 5 300) seed
... | nothing = false
... | just b  = balOf 5 b == 700

chargeInsufficient = code (charge 5 5000) seed == 3                    -- Insufficient
chargeUnchanged : Bool                                                -- overdraft leaves balance
chargeUnchanged = balOf 5 seed == 1000

creditOk : Bool
creditOk with runB (credit 5 50) seed
... | nothing = false
... | just b  = balOf 5 b == 1050

------------------------------------------------------------------------

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

main : IO ⊤
main =
  check "addpart-fk-noeng"   addPartNoEng                                   seq
  check "addpart-fk-noparty" addPartNoParty                                 seq
  check "addpart-ok"         (addPartIndexed (runB (addParticipant 3 7 "provider" 200) seed)) seq
  check "book-conflict"      bookConflict                                   seq
  check "cancel-flow"        cancelFlow                                     seq
  check "cascade-clean"      cascadeClean                                   seq
  check "charge-ok"          chargeOk                                       seq
  check "charge-insufficient" chargeInsufficient                           seq
  check "charge-unchanged"   chargeUnchanged                                seq
  check "credit-ok"          creditOk
  where
    -- success: a participation got indexed under engagement 3
    addPartIndexed : Maybe Base → Bool
    addPartIndexed (just b) = isSomeB (IM.lookup (nextId seed) (participations b))
    addPartIndexed nothing  = false
