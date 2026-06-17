{-# OPTIONS --without-K --guardedness #-}

-- Phase 3 fault-injection test (#8), hardened after review.
--
-- S1 (byte-framing + multi-byte tear — the review's CONFIRMED bug):
--   write a transaction whose payload is RUSSIAN text containing ':' and '|'
--   (multi-byte + would-be delimiters), then append a TORN record whose body is
--   cut mid-cyrillic-char (raw bytes "30:" + D0 9F D0). With CHAR-length framing
--   a torn multi-byte tail can be mis-counted as complete → die on a recoverable
--   log; with BYTE-length framing the torn tail (3 body bytes < 30) is dropped and
--   the earlier record survives with its text intact. Also proves ':'/'|'/multi-
--   byte survive framing, and a strict decode would have thrown on the D0 tail.
--
-- S2 (mid-log corruption — finding D): a complete record whose inner op is
--   undecodable must make recovery REFUSE to start (die), caught via tryCatch.
--
-- S3 (rejected path): a txn that aborts writes nothing and leaves state unchanged.
-- S4 (ioFailed path): a durable-write failure surfaces as ioFailed, state intact.
module WalRecoveryTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Storage.FFI using (_>>=_; _>>_; pure; tryCatch; writeFileText; appendWalRecord)

postulate putStrLn : String → IO ⊤
open import Agdelte.Storage.Wire using (lp)
open import Agdelte.Storage.WAL using
  ( WalConfig; mkWalConfig; WalHandle; walOpen; walRead; walTxn
  ; WalOutcome; committed; rejected; ioFailed; serializeTxn )
import Agdelte.Storage.IndexedMap as IM

open import Crm.Identity
open import Crm.Store using
  ( Base; CrmOp; SetParty; Err; NotFound; emptyBase; apply
  ; encodeOp; decodeOp; parties; nextId )
open import Crm.Txn using (Txn; emit; abort; _>>T_; runTxn)

------------------------------------------------------------------------
-- Append a TORN record cut mid-cyrillic: "30:" then D0 9F D0 (П + a dangling
-- lead byte). Declared body = 30 bytes, present = 3 → torn → dropped. The lone
-- D0 is invalid UTF-8 (a strict reader would throw on it).
------------------------------------------------------------------------

-- Append a TORN record (valid CRC-format prefix, payload incomplete + cut
-- mid-cyrillic): "30:123:" then D0 9F D0. Declared payload = 30 bytes, present = 3
-- → torn → dropped. The lone D0 is invalid UTF-8 (a strict reader would throw).
postulate
  corruptCyrillicTail : String → IO ⊤
  -- Flip one byte in the middle of an existing record's payload → CRC mismatch →
  -- recovery must refuse to start (die), not silently accept (M5).
  flipMidByte : String → IO ⊤
{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.IO as TIO
  import qualified Data.ByteString as BS
  import Data.Bits (xor)
  corruptCyrillicTailHS :: T.Text -> IO ()
  corruptCyrillicTailHS path =
    BS.appendFile (T.unpack path) (BS.pack [0x33,0x30,0x3a,0x31,0x32,0x33,0x3a,0xd0,0x9f,0xd0])
  flipMidByteHS :: T.Text -> IO ()
  flipMidByteHS path = do
    bs <- BS.readFile (T.unpack path)
    let i = BS.length bs `div` 2
        b = BS.index bs i
        bs' = BS.concat [BS.take i bs, BS.singleton (b `xor` 0x20), BS.drop (i+1) bs]
    BS.writeFile (T.unpack path) bs'
  #-}
{-# COMPILE GHC putStrLn            = TIO.putStrLn #-}
{-# COMPILE GHC corruptCyrillicTail = corruptCyrillicTailHS #-}
{-# COMPILE GHC flipMidByte         = flipMidByteHS #-}

------------------------------------------------------------------------
-- Config + sample data
------------------------------------------------------------------------

cfg : String → WalConfig Base CrmOp
cfg path = mkWalConfig path apply encodeOp decodeOp emptyBase

ruName : String
ruName = "Полунин: имя | с спецсимволами"      -- multi-byte + ':' + '|'

p7  = mkParty 7 Person ruName "Europe/Moscow" 100 nothing ""
p8  = mkParty 8 Org "Орг8" "UTC" 100 nothing ""

tx2 : Txn ⊤
tx2 = emit (SetParty p7) >>T emit (SetParty p8)

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing  = false

committed? rejected? ioFailed? : ∀ {E A} → WalOutcome E A → Bool
committed? (committed _) = true
committed? _             = false
rejected?  (rejected _)  = true
rejected?  _             = false
ioFailed?  ioFailed      = true
ioFailed?  _             = false

nameOf : Maybe Party → String
nameOf (just p) = pDisplayName p
nameOf nothing  = "<none>"

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

------------------------------------------------------------------------
-- S1 — byte-framing survives a mid-cyrillic torn tail
------------------------------------------------------------------------

path1 = "/tmp/agdelte-wal-rec-1.log"

scenario1 : IO ⊤
scenario1 =
  writeFileText path1 "" >>
  walOpen (cfg path1) >>= λ h →
  walTxn h (runTxn tx2) >>= λ o →            -- 2-op atomic record, cyrillic payload
  corruptCyrillicTail path1 >>               -- torn mid-cyrillic tail
  walOpen (cfg path1) >>= λ h2 →             -- recover
  walRead h2 >>= λ st →
  check "txn-committed"     (committed? o) >>
  check "party7-survived"   (isJust (IM.lookup 7 (parties st))) >>
  check "party8-survived"   (isJust (IM.lookup 8 (parties st))) >>
  check "name-roundtrip"    (primStringEquality (nameOf (IM.lookup 7 (parties st))) ruName) >>
  check "nextId-rebuilt"    (nextId st == 9)

------------------------------------------------------------------------
-- S2 — mid-log corruption refused (die), caught
------------------------------------------------------------------------

path2 = "/tmp/agdelte-wal-rec-2.log"

scenario2 : IO ⊤
scenario2 =
  writeFileText path2 "" >>
  appendWalRecord path2 (serializeTxn (cfg path2) (SetParty p7 ∷ [])) >>  -- a good record
  appendWalRecord path2 (lp "garbage") >>                                 -- complete record, undecodable op
  tryCatch (walOpen (cfg path2)) >>= λ r →
  check "corruption-refused" (refused r)
  where
    refused : ∀ {A : Set} → Maybe A → Bool
    refused (just _) = false
    refused nothing  = true

------------------------------------------------------------------------
-- S3 — abort writes nothing, state unchanged
------------------------------------------------------------------------

path3 = "/tmp/agdelte-wal-rec-3.log"

txReject : Txn ⊤
txReject = emit (SetParty p7) >>T abort NotFound

scenario3 : IO ⊤
scenario3 =
  writeFileText path3 "" >>
  walOpen (cfg path3) >>= λ h →
  walTxn h (runTxn txReject) >>= λ o →
  walRead h >>= λ st →
  check "txn-rejected"      (rejected? o) >>
  check "reject-no-write"   (not (isJust (IM.lookup 7 (parties st)))) >>
  check "reject-nextId-1"   (nextId st == 1)

------------------------------------------------------------------------
-- S4 — durable-write failure → ioFailed, state intact
-- ("/tmp" is a directory: appendWalRecord throws; readWalRecords → Just [] → empty)
------------------------------------------------------------------------

scenario4 : IO ⊤
scenario4 =
  walOpen (cfg "/tmp") >>= λ h →
  walTxn h (runTxn (emit (SetParty p7))) >>= λ o →
  walRead h >>= λ st →
  check "txn-iofailed"      (ioFailed? o) >>
  check "iofail-state-intact" (nextId st == 1)

------------------------------------------------------------------------
-- S5 — CRC mismatch on a committed record → refuse to start (M5)
------------------------------------------------------------------------

path5 = "/tmp/agdelte-wal-rec-5.log"

scenario5 : IO ⊤
scenario5 =
  writeFileText path5 "" >>
  walOpen (cfg path5) >>= λ h →
  walTxn h (runTxn tx2) >>= λ _ →        -- a real committed record
  flipMidByte path5 >>                    -- bit-rot one payload byte → CRC breaks
  tryCatch (walOpen (cfg path5)) >>= λ r →
  check "crc-mismatch-refused" (refused r)
  where
    refused : ∀ {A : Set} → Maybe A → Bool
    refused (just _) = false
    refused nothing  = true

main : IO ⊤
main = scenario1 >> scenario2 >> scenario3 >> scenario4 >> scenario5
