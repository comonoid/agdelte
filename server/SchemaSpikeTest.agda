{-# OPTIONS --without-K --guardedness #-}

-- SPIKE: declarative storage (docs/concepts/declarative-storage.md). Describe an entity
-- as a value-level Schema (ColTy/Column), and DERIVE two interpreters from it — the WAL
-- codec and the SQL DDL — the way the reactive runtime derives DOM from a Node template.
-- Validates on Account (3×ℕ): the derived codec is BYTE-FOR-BYTE the hand-written one,
-- round-trips, and the same Schema yields a CREATE TABLE. Self-contained (no lib changes
-- yet); promote the DSL to agdelte-store once the pattern is proven.
module SchemaSpikeTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList; fromList) renaming (_++_ to _<>_)

open import Agdelte.Storage.Wire using (R; lp; encℕ; decℕ; encStr; decStr; fieldR; _>>=R_; returnR; runR)
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

------------------------------------------------------------------------
-- The declarative core (DSL). The structure-preserving subset is enforced BY ColTy —
-- no functions / polymorphism / nested datatypes can be expressed here.
------------------------------------------------------------------------

data ColTy : Set where
  CNat CStr CBool : ColTy
  CEnum  : ℕ → ColTy
  CMaybe : ColTy → ColTy
  CFK    : String → ColTy        -- = CNat + reference to table T

record Column : Set where
  constructor mkCol
  field cname : String ; cty : ColTy
open Column public

Schema : Set
Schema = List Column

⟦_⟧ : ColTy → Set                 -- a column's Agda value type
⟦ CNat ⟧     = ℕ
⟦ CStr ⟧     = String
⟦ CBool ⟧    = Bool
⟦ CEnum _ ⟧  = ℕ
⟦ CMaybe t ⟧ = Maybe ⟦ t ⟧
⟦ CFK _ ⟧    = ℕ

Row : Schema → Set                -- a row = heterogeneous product typed by the schema
Row []       = ⊤
Row (c ∷ cs) = ⟦ cty c ⟧ × Row cs

------------------------------------------------------------------------
-- Interpreter 1 — the WAL codec, DERIVED from the schema
------------------------------------------------------------------------

private
  encBool : Bool → String
  encBool true  = "1"
  encBool false = "0"
  decBool : String → Bool
  decBool "1" = true
  decBool _   = false

  encAtom : (t : ColTy) → ⟦ t ⟧ → String
  encAtom CNat       v        = encℕ v
  encAtom CStr       v        = encStr v
  encAtom CBool      v        = encBool v
  encAtom (CEnum _)  v        = encℕ v
  encAtom (CFK _)    v        = encℕ v
  encAtom (CMaybe t) nothing  = "0"
  encAtom (CMaybe t) (just x) = "1" <> encAtom t x

  decAtom : (t : ColTy) → String → Maybe ⟦ t ⟧
  decAtom CNat       = decℕ
  decAtom CStr       = decStr
  decAtom CBool s    = just (decBool s)
  decAtom (CEnum _)  = decℕ
  decAtom (CFK _)    = decℕ
  decAtom (CMaybe t) s = goM (toList s)
    where goM : List Char → Maybe (Maybe ⟦ t ⟧)
          goM []         = just nothing
          goM (c ∷ rest) = if primCharEquality c '1'
                           then map just (decAtom t (fromList rest))
                           else just nothing

encodeRow : (s : Schema) → Row s → String
encodeRow []       _        = ""
encodeRow (c ∷ cs) (v , vs) = lp (encAtom (cty c) v) <> encodeRow cs vs

decodeRowR : (s : Schema) → R (Row s)
decodeRowR []       = returnR tt
decodeRowR (c ∷ cs) = fieldR (decAtom (cty c)) >>=R λ v →
                      decodeRowR cs            >>=R λ vs →
                      returnR (v , vs)

decodeRow : (s : Schema) → String → Maybe (Row s)
decodeRow s = runR (decodeRowR s)

------------------------------------------------------------------------
-- Interpreter 2 — the SQL DDL, DERIVED from the SAME schema
------------------------------------------------------------------------

sqlTy : ColTy → String
sqlTy CNat      = "BIGINT"
sqlTy CStr      = "TEXT"
sqlTy CBool     = "BOOLEAN"
sqlTy (CEnum _) = "SMALLINT"
sqlTy (CMaybe t) = sqlTy t
sqlTy (CFK _)   = "BIGINT"

fkRef : ColTy → String
fkRef (CFK t) = " REFERENCES " <> t
fkRef _       = ""

nullableOf : ColTy → String
nullableOf (CMaybe _) = ""
nullableOf _          = " NOT NULL"

colDDL : Bool → Column → String        -- first column = PK
colDDL first c =
  cname c <> " " <> sqlTy (cty c)
  <> (if first then " PRIMARY KEY" else nullableOf (cty c))
  <> fkRef (cty c)

ddlOf : String → Schema → String
ddlOf table []       = "CREATE TABLE " <> table <> " ()"
ddlOf table (c ∷ cs) = "CREATE TABLE " <> table <> " (" <> colDDL true c <> rest cs <> ")"
  where rest : Schema → String
        rest []        = ""
        rest (x ∷ xs)  = ", " <> colDDL false x <> rest xs

------------------------------------------------------------------------
-- The Account spike: declare the schema once, plug the record in/out
------------------------------------------------------------------------

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

contains : String → String → Bool          -- crude substring (ok for the smoke)
contains hay needle = go (toList hay)
  where
    open import Data.List using (length; take; drop)
    nl : List Char
    nl = toList needle
    eqAt : List Char → Bool
    eqAt cs = primStringEquality (fromList (take (length nl) cs)) needle
    go : List Char → Bool
    go [] = eqAt []
    go (x ∷ xs) = if eqAt (x ∷ xs) then true else go xs

chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  -- the DERIVED codec is byte-for-byte the hand-written one (drop-in)
  chk "format-matches-handwritten-a1" (encAccount′ a1 ==ˢ encAccount a1) ∷
  chk "format-matches-handwritten-a2" (encAccount′ a2 ==ˢ encAccount a2) ∷
  -- round-trips through the derived codec
  chk "roundtrip-derived-a1"  (rtVia encAccount′ decAccount′ a1) ∷
  chk "roundtrip-derived-a2"  (rtVia encAccount′ decAccount′ a2) ∷
  -- cross-codec: new encode → OLD decode, and OLD encode → new decode
  chk "cross-new-enc-old-dec" (rtVia encAccount′ decAccount  a1) ∷
  chk "cross-old-enc-new-dec" (rtVia encAccount  decAccount′ a1) ∷
  -- the SAME schema yields a CREATE TABLE
  chk "ddl-table"   (contains ddl "CREATE TABLE account") ∷
  chk "ddl-pk"      (contains ddl "id BIGINT PRIMARY KEY") ∷
  chk "ddl-notnull" (contains ddl "balance BIGINT NOT NULL") ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn ("DDL = " <> ddl) seq putStrLn "schema-spike done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
