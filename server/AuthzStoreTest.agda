{-# OPTIONS --without-K --guardedness #-}

-- End-to-end authz: the CRM store (role-assignment DATA) ⇄ the agdelte-auth RBAC engine
-- (the policy/decision) ⇄ the domain policy (Psych.Authz). Runs assignRole commands over
-- a Base, reads them back with scopedRolesOf, and feeds those (roleId,scope) pairs into
-- RBAC.Scoped.canOn against the coaching policy. Proves the data half + engine + policy
-- compose: "this principal may do X on scope Y" decided from persisted assignments.
module AuthzStoreTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using () renaming (_++_ to _<>_)

open import Crm.Store using (Base; emptyBase)
open import Crm.Txn using (Txn; runTxn)
open import Crm.Commands using (assignRole; revokeRole; scopedRolesOf)
open import Agdelte.Auth.RBAC using (perm)
open import Agdelte.Auth.RBAC.Scoped using (canOn)
open import Psych.Authz using (crmPolicy)

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

-- run a command, keep the resulting Base (ignore errors/result)
step : ∀ {A : Set} → Txn A → Base → Base
step cmd b with runTxn cmd b
... | inj₁ _            = b
... | inj₂ (b' , _ , _) = b'

-- ivan = operator in ws/42 ; boss = admin globally ("*")
b1 : Base
b1 = step (assignRole "ivan" "operator" "ws/42" 0) emptyBase

b2 : Base
b2 = step (assignRole "boss" "admin" "*" 0) b1

b3 : Base                        -- ivan's assignment (id 1) revoked
b3 = step (revokeRole 1) b1

chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  chk "sro-count-1"      (length (scopedRolesOf b1 "ivan") == 1) ∷
  chk "sro-count-0"      (length (scopedRolesOf b1 "bob")  == 0) ∷
  -- operator may cancel activities within ws/42 subtree
  chk "authz-allow"      (canOn crmPolicy (scopedRolesOf b1 "ivan") (perm "activity" "cancel") "ws/42/x") ∷
  -- operator ⊃ public ⇒ may read availability
  chk "authz-inherit"    (canOn crmPolicy (scopedRolesOf b1 "ivan") (perm "availability" "read") "ws/42") ∷
  -- wrong scope → denied
  chk "authz-scope-deny" (not (canOn crmPolicy (scopedRolesOf b1 "ivan") (perm "activity" "cancel") "ws/99")) ∷
  -- operator lacks config:write → denied
  chk "authz-perm-deny"  (not (canOn crmPolicy (scopedRolesOf b1 "ivan") (perm "config" "write") "ws/42")) ∷
  -- unknown subject → no roles → denied
  chk "authz-none"       (not (canOn crmPolicy (scopedRolesOf b1 "bob") (perm "activity" "cancel") "ws/42")) ∷
  -- admin in global scope → anything anywhere
  chk "authz-admin-glob" (canOn crmPolicy (scopedRolesOf b2 "boss") (perm "anything" "goes") "ws/77") ∷
  -- after revoke, ivan has nothing
  chk "revoke"           (length (scopedRolesOf b3 "ivan") == 0) ∷
  chk "revoke-denies"    (not (canOn crmPolicy (scopedRolesOf b3 "ivan") (perm "activity" "cancel") "ws/42")) ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "authz-store done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
