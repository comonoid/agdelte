{-# OPTIONS --without-K --guardedness #-}

-- Runtime smoke test for the extracted video-course platform (agdelte-courses):
-- prove AppStore actually RUNS on the extracted store — applyOp through NatMap
-- (= Data.Map), id reconstruction, queries, and the pipe-codec round-trip. This
-- closes the "agdelte-courses is typecheck-only" gap with a real GHC run.
module CoursesSmokeTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Auth.Role using (Student)
open import Agdelte.Storage.AppStore
  using ( AppState; AppOp; AddUser; UserRecord; mkUserRecord
        ; emptyAppState; applyOp; findUserById; urEmail; asNextUserId
        ; serializeOp; deserializeOp )

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

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing  = false

emailOf : Maybe UserRecord → String
emailOf (just u) = urEmail u
emailOf nothing  = "<none>"

-- pipe-codec round-trip (string-compare avoids needing record Eq)
rtOp : AppOp → Bool
rtOp op with deserializeOp (serializeOp op)
... | just op' = primStringEquality (serializeOp op') (serializeOp op)
... | nothing  = false

u1 = mkUserRecord 1 "polunin: с : спец" "hash1" Student   -- ':' would break a pipe field if unescaped
u2 = mkUserRecord 2 "d@e.f" "hash2" Student

seed : AppState
seed = applyOp (AddUser u2) (applyOp (AddUser u1) emptyAppState)

main : IO ⊤
main =
  check "user1-found"   (isJust (findUserById 1 seed)) seq
  check "user2-found"   (isJust (findUserById 2 seed)) seq
  check "email-intact"  (primStringEquality (emailOf (findUserById 1 seed)) "polunin: с : спец") seq
  check "nextId-3"      (asNextUserId seed == 3) seq
  check "codec-rt-u1"   (rtOp (AddUser u1)) seq
  check "codec-rt-u2"   (rtOp (AddUser u2))
