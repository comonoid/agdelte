{-# OPTIONS --without-K --guardedness #-}

-- Test the hand-rolled JSON parser in Agdelte.FFI.Json (audit M2): string values
-- with escaped quotes must NOT truncate; only TOP-LEVEL keys consulted; cyrillic;
-- jsonGetNat rejects non-integers; malformed input → nothing. Runtime (GHC FFI).
module JsonTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Json using (jsonGetField; jsonGetNat)

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

eqS : Maybe String → Maybe String → Bool
eqS (just a) (just b) = primStringEquality a b
eqS nothing  nothing  = true
eqS _        _        = false

eqN : Maybe ℕ → Maybe ℕ → Bool
eqN (just a) (just b) = a == b
eqN nothing  nothing  = true
eqN _        _        = false

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

-- JSON literals (Agda escapes): the value of "name" here is the 3 chars a " b
escQuote  = "{\"name\":\"a\\\"b\"}"
cyr       = "{\"name\":\"Полунин: и | спец\"}"
nested    = "{\"y\":{\"x\":1},\"x\":\"top\"}"
floatN    = "{\"n\":3.5}"
intN      = "{\"n\":30}"
bad       = "not json at all"

main : IO ⊤
main =
  check "escaped-quote-not-truncated" (eqS (jsonGetField "name" escQuote) (just "a\"b")) seq
  check "cyrillic-value"              (eqS (jsonGetField "name" cyr)      (just "Полунин: и | спец")) seq
  check "top-level-not-nested"        (eqS (jsonGetField "x"    nested)   (just "top")) seq
  check "missing-field"               (eqS (jsonGetField "z"    intN)     nothing) seq
  check "nat-ok"                      (eqN (jsonGetNat   "n"    intN)     (just 30)) seq
  check "nat-rejects-float"           (eqN (jsonGetNat   "n"    floatN)   nothing) seq
  check "malformed-nothing"           (eqS (jsonGetField "name" bad)      nothing)
