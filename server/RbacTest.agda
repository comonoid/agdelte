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
open import Agdelte.Auth.RBAC.Presets as Pre using (policyOf; canStr; superAdmin)
open import Agdelte.Auth.RBAC.Scoped  as Sc  using (scopeCovers; canOn; canAssign)
import Agdelte.Auth.RBAC.Typed as Ty

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

-- Presets facade: policy from plain string config
prePol : Policy
prePol = policyOf (("op" , ("activity:cancel" ∷ [])) ∷ ("admin" , ("*:*" ∷ [])) ∷ [])

-- Scoped/ARBAC sample policy
scPol : Policy
scPol = role "operator" (perm "activity" "cancel" ∷ []) []
      ∷ role "owner"    (perm "role" "assign" ∷ []) []
      ∷ []

-- Typed mechanism: a domain plugs its own Resource/Action enums
data TR : Set where TActivity TEngagement : TR
data TA : Set where TRead TCancel : TA
showTR : TR → String
showTR TActivity   = "activity"
showTR TEngagement = "engagement"
showTA : TA → String
showTA TRead   = "read"
showTA TCancel = "cancel"
open Ty.Builder showTR showTA

tyPol : Policy
tyPol = role "op" (tperm TActivity TCancel ∷ []) [] ∷ []

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
  -- Presets facade (string config, no Perm records)
  chk "preset-allow"       (canStr prePol ("op" ∷ []) "activity:cancel") ∷
  chk "preset-deny"        (not (canStr prePol ("op" ∷ []) "activity:read")) ∷
  chk "preset-superadmin"  (canStr prePol ("admin" ∷ []) "whatever:goes") ∷
  -- Scoped / ARBAC delegation
  chk "scope-self"         (scopeCovers "ws/42" "ws/42") ∷
  chk "scope-subtree"      (scopeCovers "ws/42" "ws/42/x") ∷
  chk "scope-sibling-no"   (not (scopeCovers "ws/42" "ws/420")) ∷
  chk "scope-outside-no"   (not (scopeCovers "ws/42" "ws")) ∷
  chk "canOn-in-scope"     (canOn scPol (("operator" , "ws/42") ∷ []) (perm "activity" "cancel") "ws/42/sub") ∷
  chk "canOn-out-scope"    (not (canOn scPol (("operator" , "ws/42") ∷ []) (perm "activity" "cancel") "ws/99")) ∷
  chk "canAssign-owner"    (canAssign scPol (("owner" , "ws/42") ∷ []) "ws/42/x") ∷
  chk "canAssign-out"      (not (canAssign scPol (("owner" , "ws/42") ∷ []) "ws/99")) ∷
  -- Typed mechanism (domain-supplied enums, typo-proof)
  chk "typed-allow"        (tcan tyPol ("op" ∷ []) TActivity TCancel) ∷
  chk "typed-deny"         (not (tcan tyPol ("op" ∷ []) TActivity TRead)) ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "rbac done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
