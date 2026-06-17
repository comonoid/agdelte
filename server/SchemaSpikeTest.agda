{-# OPTIONS --without-K --guardedness #-}

-- Validation for Agdelte.Storage.Schema (docs/concepts/declarative-storage.md): declare
-- the Account entity as a value-level Schema and check the DERIVED interpreters — the
-- WAL codec is BYTE-FOR-BYTE the hand-written encAccount/decAccount (and cross-interops
-- both ways), and the same schema yields a CREATE TABLE. The DSL now lives in
-- agdelte-store; this is its round-trip + format-match guard for the rollout.
module SchemaSpikeTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length; take)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList; fromList) renaming (_++_ to _<>_)

open import Agdelte.Storage.Schema using
  ( ColTy; CNat; CFK; CEnumS; Column; mkCol; idxCol; Schema; Row
  ; encodeRow; decodeRow; encAtom; decAtom; ddlOf; imIndexes; indexDDLs )
open import Crm.Identity using (Account; mkAccount; acId; acBalance; acCreatedAt)
open import Crm.Wire using (encAccount; decAccount)

postulate
  putStrLn : String → IO ⊤
  _seq_    : IO ⊤ → IO ⊤ → IO ⊤
infixr 1 _seq_
{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  seqIO :: IO () -> IO () -> IO ()
  seqIO = (>>)
  #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _seq_    = seqIO #-}

-- declare the schema once; plug the record in/out
accountSchema : Schema
accountSchema = mkCol "id"         CNat
              ∷ mkCol "balance"    CNat
              ∷ mkCol "created_at" CNat
              ∷ []

toRow : Account → Row accountSchema
toRow a = acId a , acBalance a , acCreatedAt a , tt

fromRow : Row accountSchema → Account
fromRow (i , bal , ca , tt) = mkAccount i bal ca

-- the derived codec, drop-in for encAccount/decAccount
encAccount′ : Account → String
encAccount′ a = encodeRow accountSchema (toRow a)

decAccount′ : String → Maybe Account
decAccount′ s = map fromRow (decodeRow accountSchema s)

------------------------------------------------------------------------
-- Checks
------------------------------------------------------------------------

_==ˢ_ : String → String → Bool
a ==ˢ b = primStringEquality a b

acEq : Account → Account → Bool
acEq x y = (acId x == acId y) ∧ (acBalance x == acBalance y) ∧ (acCreatedAt x == acCreatedAt y)

a1 : Account
a1 = mkAccount 7 1500 100
a2 : Account
a2 = mkAccount 13 0 999999

rtVia : (Account → String) → (String → Maybe Account) → Account → Bool
rtVia enc dec a with dec (enc a)
... | just a′ = acEq a′ a
... | nothing = false

ddl : String
ddl = ddlOf "account" accountSchema

contains : String → String → Bool
contains hay needle = go (toList hay)
  where
    nl : List Char
    nl = toList needle
    eqAt : List Char → Bool
    eqAt cs = primStringEquality (fromList (take (length nl) cs)) needle
    go : List Char → Bool
    go [] = eqAt []
    go (x ∷ xs) = if eqAt (x ∷ xs) then true else go xs

chk : String → Bool → String × Bool
chk n b = n , b

------------------------------------------------------------------------
-- Index derivation + CEnumS (the step-3 interpreter), over a 2-index schema
------------------------------------------------------------------------

stCodes : List String
stCodes = "P" ∷ "S" ∷ []

idxSchema : Schema
idxSchema = mkCol "id" CNat ∷ idxCol "eng" (CFK "engagement")
          ∷ idxCol "st" (CEnumS stCodes) ∷ []

sampleRow : Row idxSchema           -- id=5, eng=7, st=1 ("S")
sampleRow = 5 , 7 , 1 , tt

lℕ= : List ℕ → List ℕ → Bool
lℕ= []       []       = true
lℕ= (x ∷ xs) (y ∷ ys) = (x == y) ∧ lℕ= xs ys
lℕ= _        _        = false

-- the two derived extractors (positions 0=eng, 1=st) project the right keys
idxKeys : Bool
idxKeys with imIndexes idxSchema (λ r → r)
... | e0 ∷ e1 ∷ [] = lℕ= (e0 sampleRow) (7 ∷ []) ∧ lℕ= (e1 sampleRow) (1 ∷ [])
... | _            = false

enumDec : Bool                       -- code → ordinal
enumDec with decAtom (CEnumS stCodes) "S"
... | just n  = n == 1
... | nothing = false

enumDecBad : Bool                    -- unknown code ⇒ strict failure (nothing)
enumDecBad with decAtom (CEnumS stCodes) "Q"
... | just _  = false
... | nothing = true

ixddl2 : Bool                        -- one CREATE INDEX per idxCol (2 here)
ixddl2 with indexDDLs "activity" idxSchema
... | _ ∷ _ ∷ [] = true
... | _          = false

checks : List (String × Bool)
checks =
  chk "format-matches-handwritten-a1" (encAccount′ a1 ==ˢ encAccount a1) ∷
  chk "format-matches-handwritten-a2" (encAccount′ a2 ==ˢ encAccount a2) ∷
  chk "roundtrip-derived-a1"  (rtVia encAccount′ decAccount′ a1) ∷
  chk "roundtrip-derived-a2"  (rtVia encAccount′ decAccount′ a2) ∷
  chk "cross-new-enc-old-dec" (rtVia encAccount′ decAccount  a1) ∷
  chk "cross-old-enc-new-dec" (rtVia encAccount  decAccount′ a1) ∷
  chk "ddl-table"   (contains ddl "CREATE TABLE account") ∷
  chk "ddl-pk"      (contains ddl "id BIGINT PRIMARY KEY") ∷
  chk "ddl-notnull" (contains ddl "balance BIGINT NOT NULL") ∷
  chk "index-keys-derived"  idxKeys ∷
  chk "cenums-enc-ordinal0" (encAtom (CEnumS stCodes) 0 ==ˢ "P") ∷
  chk "cenums-enc-ordinal1" (encAtom (CEnumS stCodes) 1 ==ˢ "S") ∷
  chk "cenums-dec-ordinal"  enumDec ∷
  chk "cenums-dec-strict"   enumDecBad ∷
  chk "index-ddl-per-idxcol" ixddl2 ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn ("DDL = " <> ddl) seq putStrLn "schema-spike done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
