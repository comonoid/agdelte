{-# OPTIONS --without-K --guardedness #-}

-- Pure unit tests for Agdelte.Auth.RBAC: permission wildcard matching, the role
-- hierarchy (transitive inheritance), cycle-safety, the `can` check, and the
-- separation-of-duty constraints. Prints "PASS <name>"/"FAIL <name>" per check.
module RbacTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Auth.RBAC

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
-- A sample policy with a hierarchy and a cycle
--   viewer  : engagement:read
--   operator: activity:cancel, activity:complete  ⊃ viewer
--   admin   : *:*                                 ⊃ operator (⊃ viewer)
--   cycA ⊃ cycB ⊃ cycA  (misconfigured cycle — resolution must still terminate)
------------------------------------------------------------------------

pol : Policy
pol =
  role "viewer"   (perm "engagement" "read" ∷ []) [] ∷
  role "operator" (perm "activity" "cancel" ∷ perm "activity" "complete" ∷ []) ("viewer" ∷ []) ∷
  role "admin"    (perm "*" "*" ∷ []) ("operator" ∷ []) ∷
  role "cycA"     (perm "x" "a" ∷ []) ("cycB" ∷ []) ∷
  role "cycB"     (perm "y" "b" ∷ []) ("cycA" ∷ []) ∷
  []

sod : SoD
sod = ("operator" , "auditor") ∷ []

chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  -- wildcard matching
  chk "cover-exact"        (covers (perm "activity" "cancel") (perm "activity" "cancel")) ∷
  chk "cover-action-star"  (covers (perm "activity" "*")      (perm "activity" "cancel")) ∷
  chk "cover-super"        (covers (perm "*" "*")             (perm "activity" "cancel")) ∷
  chk "cover-res-miss"     (not (covers (perm "engagement" "*") (perm "activity" "cancel"))) ∷
  chk "cover-act-miss"     (not (covers (perm "activity" "read") (perm "activity" "cancel"))) ∷
  -- can: direct grant
  chk "can-direct"         (can pol ("operator" ∷ []) (perm "activity" "cancel")) ∷
  chk "can-direct-deny"    (not (can pol ("viewer" ∷ []) (perm "activity" "cancel"))) ∷
  -- can: via hierarchy (operator ⊃ viewer; admin ⊃ operator ⊃ viewer)
  chk "can-inherit-1"      (can pol ("operator" ∷ []) (perm "engagement" "read")) ∷
  chk "can-inherit-2"      (can pol ("admin" ∷ []) (perm "engagement" "read")) ∷
  chk "can-admin-wild"     (can pol ("admin" ∷ []) (perm "anything" "goes")) ∷
  chk "can-deny-unknown"   (not (can pol ("operator" ∷ []) (perm "engagement" "delete"))) ∷
  chk "can-no-roles"       (not (can pol [] (perm "engagement" "read"))) ∷
  chk "can-multi-role"     (can pol ("viewer" ∷ "operator" ∷ []) (perm "activity" "complete")) ∷
  -- cycle-safe resolution (must terminate AND collect both sides)
  chk "cycle-self"         (can pol ("cycA" ∷ []) (perm "x" "a")) ∷
  chk "cycle-cross"        (can pol ("cycA" ∷ []) (perm "y" "b")) ∷
  chk "cycle-deny"         (not (can pol ("cycA" ∷ []) (perm "z" "c"))) ∷
  -- separation of duty
  chk "sod-ok"             (assignmentValid sod ("operator" ∷ "viewer" ∷ [])) ∷
  chk "sod-violation"      (not (assignmentValid sod ("operator" ∷ "auditor" ∷ []))) ∷
  chk "sod-detect"         (violatesSoD sod ("auditor" ∷ "operator" ∷ [])) ∷
  -- parse / show
  chk "show"               (showPerm (perm "activity" "cancel") ==ˢ "activity:cancel") ∷
  chk "parse-res"          (resource (parsePerm "activity:cancel") ==ˢ "activity") ∷
  chk "parse-act"          (action   (parsePerm "activity:cancel") ==ˢ "cancel") ∷
  chk "parse-nocolon"      (action   (parsePerm "lonely") ==ˢ "*") ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "rbac done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
