{-# OPTIONS --without-K --guardedness #-}

-- Test the GENERIC transaction monad Agdelte.Storage.Txn (from agdelte-store)
-- on a TOY domain (a single ℕ counter) — i.e. with NO CRM involvement. Proves the
-- extraction produced a reusable, domain-parameterized monad: emit / getBase /
-- abort / guardT / runTxn, plus live ≡ replay (the emitted ops, replayed via the
-- same `apply`, reach the same state runTxn computed).
module StoreTxnTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (suc; _==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; length; foldl)
open import Data.String using () renaming (_++_ to _<>_)

-- toy domain: a single ℕ counter
data Op : Set where
  inc   : Op
  setTo : ℕ → Op

applyOp : Op → ℕ → ℕ
applyOp inc       n = suc n
applyOp (setTo m) _ = m

-- instantiate the generic monad at (ℕ, Op, String, applyOp)
open import Agdelte.Storage.Txn ℕ Op String applyOp

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

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

-- inc, inc, read state, then setTo 100, return the read value
prog : Txn ℕ
prog = emit inc >>T emit inc >>T (getBase >>=T λ n → emit (setTo 100) >>T returnT n)

progAbort : Txn ⊤
progAbort = emit inc >>T abort "stop"

progGuard : Txn ⊤
progGuard = getBase >>=T λ n → guardT (n == 0) "not-zero" >>T emit inc

main : IO ⊤
main =
  -- committed run from state 0: result = 2 (read after two incs), final = 100
  (case runTxn prog 0 of λ where
     (inj₁ _)            → check "commit" false
     (inj₂ (s , ops , r)) →
       check "result-2"      (r == 2)             seq
       check "final-100"     (s == 100)           seq
       check "ops-3"         (length ops == 3)    seq
       -- live ≡ replay: replaying the emitted ops via applyOp from 0 reaches s
       check "live≡replay"   (foldl (λ acc op → applyOp op acc) 0 ops == s))
  seq
  (case runTxn progAbort 0 of λ where
     (inj₁ e) → check "abort"        (primStringEquality e "stop")
     (inj₂ _) → check "abort"        false)
  seq
  (case runTxn progGuard 0 of λ where
     (inj₂ _) → check "guard-pass"   true
     (inj₁ _) → check "guard-pass"   false)
  seq
  (case runTxn progGuard 5 of λ where
     (inj₁ e) → check "guard-abort"  (primStringEquality e "not-zero")
     (inj₂ _) → check "guard-abort"  false)
  where open import Function using (case_of_)
