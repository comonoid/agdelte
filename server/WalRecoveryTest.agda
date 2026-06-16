{-# OPTIONS --without-K --guardedness #-}

-- Phase 3 fault-injection test (#8): prove WAL durability/recovery on GHC.
--
-- Scenario 1 (torn tail + invalid UTF-8 — findings A, B, atomicity #1):
--   write a 2-op transaction (one record) + a 1-op transaction (another), then
--   append a TORN record ending in a lone 0xFF byte (invalid UTF-8). Reopen:
--   the two complete records must survive (a STRICT decode would have thrown on
--   0xFF → whole log discarded → parties NOT found; lenient decode + length-
--   framing drop only the torn tail). The 2-op record proves transaction
--   framing replays atomically.
--
-- Scenario 2 (mid-log corruption — finding D):
--   a fully-present record whose inner op is undecodable must make recovery
--   REFUSE to start (die), not silently skip. We catch the abort with tryCatch
--   and assert it fired.
module WalRecoveryTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Server using (_>>=_; _>>_; pure; putStrLn; tryCatch)
open import Agdelte.FFI.FileSystem using (writeFileText)
open import Agdelte.Storage.Wire using (lp)
open import Agdelte.Storage.WAL using
  ( WalConfig; mkWalConfig; WalHandle; walOpen; walRead; walStep; walTxn
  ; WalOutcome; committed; rejected; ioFailed; frameTxn )
import Agdelte.Storage.IndexedMap as IM

open import Crm.Identity
open import Crm.Store using
  ( Base; CrmOp; SetParty; SetEngagement; Err; emptyBase; apply
  ; encodeOp; decodeOp; parties; engagements; nextId )
open import Crm.Txn using (Txn; emit; _>>T_; runTxn)

------------------------------------------------------------------------
-- Append a torn record ending in a lone 0xFF (invalid UTF-8). "20:abc" claims
-- 20 chars but only 4 survive (incl. the U+FFFD replacement) → torn → dropped;
-- the 0xFF would make a STRICT reader throw.
------------------------------------------------------------------------

postulate
  corruptTail : String → IO ⊤
{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.ByteString as BS
  corruptTailHS :: T.Text -> IO ()
  corruptTailHS path =
    BS.appendFile (T.unpack path) (BS.pack [0x32,0x30,0x3a,0x61,0x62,0x63,0xff])
  #-}
{-# COMPILE GHC corruptTail = corruptTailHS #-}

------------------------------------------------------------------------
-- Config + sample data
------------------------------------------------------------------------

cfg : String → WalConfig Base CrmOp
cfg path = mkWalConfig path apply encodeOp decodeOp emptyBase

p7  = mkParty 7 "u7" Person "P7" "UTC" 100 nothing
p8  = mkParty 8 "u8" Person "P8" "UTC" 100 nothing
e3  = mkEngagement 3 "u3" 1 1 nothing 100 nothing

-- one transaction emitting TWO ops (single atomic record)
tx2 : Txn ⊤
tx2 = emit (SetParty p7) >>T emit (SetParty p8)

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing  = false

committed? : ∀ {E A} → WalOutcome E A → Bool
committed? (committed _) = true
committed? _             = false

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

------------------------------------------------------------------------
-- Scenario 1
------------------------------------------------------------------------

path1 : String
path1 = "/tmp/agdelte-wal-rec-1.log"

scenario1 : IO ⊤
scenario1 =
  writeFileText path1 "" >>                       -- clean start (truncate)
  walOpen (cfg path1) >>= λ h →
  walTxn h (runTxn tx2) >>= λ o →                 -- 2-op atomic record
  walStep h (SetEngagement e3) >>= λ _ →          -- 1-op record
  corruptTail path1 >>                            -- torn tail + bad UTF-8 byte
  walOpen (cfg path1) >>= λ h2 →                  -- recover
  walRead h2 >>= λ st →
  check "txn-committed"   (committed? o) >>
  check "party7-survived" (isJust (IM.lookup 7 (parties st))) >>
  check "party8-survived" (isJust (IM.lookup 8 (parties st))) >>
  check "eng3-survived"   (isJust (IM.lookup 3 (engagements st))) >>
  check "nextId-rebuilt"  (nextId st == 9)        -- max id 8 (+1) ⊓ 4 = 9

------------------------------------------------------------------------
-- Scenario 2 — mid-log corruption must refuse (die), caught here
------------------------------------------------------------------------

path2 : String
path2 = "/tmp/agdelte-wal-rec-2.log"

-- a complete record (real op) followed by a complete record whose inner
-- payload is NOT a decodable op ("garbage" — no valid tag char).
corruptMiddle : String
corruptMiddle = frameTxn (cfg path2) (SetParty p7 ∷ [])
              <> lp (lp "garbage")
  where open import Data.List using (List; []; _∷_)

scenario2 : IO ⊤
scenario2 =
  writeFileText path2 corruptMiddle >>
  tryCatch (walOpen (cfg path2)) >>= λ r →
  check "corruption-refused" (refused r)
  where
    refused : ∀ {A : Set} → Maybe A → Bool
    refused (just _) = false      -- opened despite corruption → wrong
    refused nothing  = true       -- die fired, caught → correct

main : IO ⊤
main = scenario1 >> scenario2
