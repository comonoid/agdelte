{-# OPTIONS --without-K #-}

-- Crm.Txn — the transaction monad (Phase 3). A `Txn A` threads the working
-- `Base` and an accumulator of emitted ops; it either aborts with `Err`
-- (nothing committed) or yields a new Base, the ops it emitted, and a result.
--
-- The single mutating primitive is `emit op`, which BOTH applies the op to the
-- working Base (so later reads in the same transaction see it) AND records it
-- for the WAL. Because `emit` uses the very same `Store.apply` that recovery
-- replays, the live result equals the replayed result by construction
-- (live ≡ replay). Serial single-writer ⇒ serializable.
--
-- The op accumulator is a DIFFERENCE LIST (O(1) snoc), not `++` — a bulk/
-- cascade transaction that emits n ops would otherwise be O(n²) (#P1).
--
-- `runTxn` produces exactly the `Base → Err ⊎ (Base × List CrmOp × A)` shape
-- that `Agdelte.Storage.WAL.walTxn` consumes.
module Crm.Txn where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)

open import Crm.Store using (Base; CrmOp; Err; apply)

------------------------------------------------------------------------
-- Difference list of ops (O(1) snoc; #P1)
------------------------------------------------------------------------

private
  DList : Set
  DList = List CrmOp → List CrmOp

  dnil : DList
  dnil xs = xs

  dsnoc : DList → CrmOp → DList
  dsnoc d op xs = d (op ∷ xs)
    where open import Data.List using (_∷_)

  drun : DList → List CrmOp
  drun d = d []

------------------------------------------------------------------------
-- The monad
------------------------------------------------------------------------

-- working Base → ops-so-far → abort | (new Base × ops × result)
Txn : Set → Set
Txn A = Base → DList → Err ⊎ (Base × DList × A)

returnT : ∀ {A} → A → Txn A
returnT a b d = inj₂ (b , d , a)

infixl 1 _>>=T_ _>>T_

_>>=T_ : ∀ {A B} → Txn A → (A → Txn B) → Txn B
(m >>=T f) b d with m b d
... | inj₁ e               = inj₁ e
... | inj₂ (b' , d' , a)   = f a b' d'

_>>T_ : ∀ {A B} → Txn A → Txn B → Txn B
m >>T n = m >>=T λ _ → n

------------------------------------------------------------------------
-- Primitives
------------------------------------------------------------------------

-- read the current working Base (reflects ops emitted earlier in this txn)
getBase : Txn Base
getBase b d = inj₂ (b , d , b)

-- reject the whole transaction; nothing is committed
abort : ∀ {A} → Err → Txn A
abort e b d = inj₁ e

-- apply op to the working Base AND record it for the WAL (the only mutation)
emit : CrmOp → Txn ⊤
emit op b d = inj₂ (apply op b , dsnoc d op , tt)

-- guard: continue iff the condition holds, else abort
require : ∀ {A : Set} → (A ⊎ Err) → Txn A
require (inj₁ a) b d = inj₂ (b , d , a)
require (inj₂ e) b d = inj₁ e

------------------------------------------------------------------------
-- Derived combinators (so domain commands read like ordinary FP)
------------------------------------------------------------------------

-- unwrap a lookup or abort with the given error (FK / existence checks)
requireJust : ∀ {A} → Err → Maybe A → Txn A
requireJust e nothing  = abort e
requireJust e (just a) = returnT a

-- continue iff the guard holds, else abort (invariants / slot-free / transitions)
guardT : Bool → Err → Txn ⊤
guardT true  _ = returnT tt
guardT false e = abort e

-- emit once per element, in order (cascades over reverse-index id lists)
forEachT : ∀ {A : Set} → List A → (A → Txn ⊤) → Txn ⊤
forEachT []       f = returnT tt
forEachT (x ∷ xs) f = f x >>T forEachT xs f

------------------------------------------------------------------------
-- Run — to the shape walTxn consumes
------------------------------------------------------------------------

runTxn : ∀ {A} → Txn A → Base → Err ⊎ (Base × (List CrmOp × A))
runTxn m b with m b dnil
... | inj₁ e             = inj₁ e
... | inj₂ (b' , d , a)  = inj₂ (b' , drun d , a)
