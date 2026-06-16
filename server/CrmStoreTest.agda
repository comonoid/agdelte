{-# OPTIONS --without-K --guardedness #-}

-- Phase 2 test: build a Base by replaying ops (foldl apply), then check the
-- self-maintained relation indexes (byEngagement / byParty), nextId reconstruction
-- (#N1), entity lookup, and op-codec round-trip. Runtime (NatMap is a GHC postulate).
module CrmStoreTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; foldl)
open import Data.String using () renaming (_++_ to _<>_)

open import Crm.Identity
open import Crm.Store
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

listEq : List ℕ → List ℕ → Bool
listEq []       []       = true
listEq (x ∷ xs) (y ∷ ys) = (x == y) ∧ listEq xs ys
listEq _        _        = false

pass : String → Bool → IO ⊤
pass name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

checkL : String → List ℕ → List ℕ → IO ⊤
checkL name got exp = pass name (listEq got exp)

checkN : String → ℕ → ℕ → IO ⊤
checkN name got exp = pass name (got == exp)

isJustA : Maybe Activity → Bool
isJustA (just _) = true
isJustA nothing  = false

rtOp : CrmOp → Bool
rtOp op with decodeOp (encodeOp op)
... | just op' = primStringEquality (encodeOp op') (encodeOp op)
... | nothing  = false

p7  = mkParty 7 "u7" Person "P7" "UTC" 100 nothing
p8  = mkParty 8 "u8" Person "P8" "UTC" 100 nothing
e3  = mkEngagement 3 "u3" 1 1 nothing 100 nothing
a9  = mkActivity 9 "u9" 3 200 Scheduled 100 nothing
pp11 = mkParticipation 11 3 7 "provider" 100
pp12 = mkParticipation 12 3 8 "client" 100

ops : List CrmOp
ops = SetParty p7 ∷ SetParty p8 ∷ SetEngagement e3 ∷ SetActivity a9 ∷
      SetParticipation pp11 ∷ SetParticipation pp12 ∷ []

st : Base
st = foldl (λ b op → apply op b) emptyBase ops   -- = replay

main : IO ⊤
main =
  checkL "part-by-eng3"   (IM.byIndex partByEngagement 3 (participations st)) (12 ∷ 11 ∷ []) seq
  checkL "part-by-party7" (IM.byIndex partByParty 7 (participations st))      (11 ∷ [])      seq
  checkL "part-by-party8" (IM.byIndex partByParty 8 (participations st))      (12 ∷ [])      seq
  checkL "act-by-eng3"    (IM.byIndex actByEngagement 3 (activities st))      (9 ∷ [])       seq
  checkN "nextId"         (nextId st) 13                                                     seq
  pass   "lookup-act9"    (isJustA (IM.lookup 9 (activities st)))                            seq
  pass   "op-roundtrip"   (rtOp (SetParty p7) ∧ rtOp (DelParticipation 11)
                           ∧ rtOp (SetAccount (mkAccount 5 "ua5" 1000 100)) ∧ rtOp (DelAccount 5))
