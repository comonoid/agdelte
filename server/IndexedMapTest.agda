{-# OPTIONS --without-K --guardedness #-}

-- Runtime test for Agdelte.Storage.IndexedMap. NatMap is a GHC-backed postulate
-- (no Agda reduction), so we compile + run rather than check with refl.
-- Exercises the tricky case N3: an UPDATE that changes an indexed field must
-- retract the old index key (no stale entries).
module IndexedMapTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (_++_)

import Agdelte.Storage.IndexedMap as IX

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

check : String → List ℕ → List ℕ → IO ⊤
check name got exp = putStrLn (if listEq got exp then ("PASS " ++ name) else ("FAIL " ++ name))

-- value = (someField , indexedField); index on the second field
ext : (ℕ × ℕ) → List ℕ
ext p = proj₂ p ∷ []

m0 m1 m2 m3 m4 m5 : IX.IndexedMap (ℕ × ℕ)
m0 = IX.empty (ext ∷ [])
m1 = IX.insert 1 (10 , 100) m0
m2 = IX.insert 2 (20 , 100) m1
m3 = IX.insert 3 (30 , 200) m2
m4 = IX.insert 2 (20 , 200) m3   -- UPDATE id 2: indexed field 100 → 200 (N3 retract)
m5 = IX.delete 1 m4

main : IO ⊤
main =
  -- after inserts 1,2,3 (addKey conses → reverse-insertion order)
  check "k100@m3" (IX.byIndex 0 100 m3) (2 ∷ 1 ∷ []) seq
  check "k200@m3" (IX.byIndex 0 200 m3) (3 ∷ [])      seq
  -- after update 2 (100→200): id 2 retracted from 100, added to 200
  check "k100@m4" (IX.byIndex 0 100 m4) (1 ∷ [])      seq
  check "k200@m4" (IX.byIndex 0 200 m4) (2 ∷ 3 ∷ [])  seq
  -- after delete 1
  check "k100@m5" (IX.byIndex 0 100 m5) ([])
