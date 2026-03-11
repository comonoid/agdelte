{-# OPTIONS --without-K --guardedness #-}

-- Research §1: Recursive / Coinductive Sessions
--
-- Extends Session.agda with looping protocols.
-- Uses Agda's coinductive records (--guardedness) for infinite sessions.
--
-- Design choice: Option 2 from research.md — coinductive Session type.
-- A CoSession is a potentially infinite protocol tree.
-- Finite sessions embed via `done` leaves.
-- Recursive sessions use guarded corecursion.

module Agdelte.Concurrent.CoSession where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- CoSession: coinductive (potentially infinite) protocol
------------------------------------------------------------------------

-- A coinductive session can describe looping protocols.
-- Each observation is one "step" of the protocol.
-- The continuation is lazy (coinductive) — may loop forever.

data SessionStep : Set₁ where
  sendStep   : (A : Set) → SessionStep
  recvStep   : (A : Set) → SessionStep
  offerStep  : SessionStep
  chooseStep : SessionStep
  doneStep   : SessionStep

-- NO_UNIVERSE_CHECK: SessionStep stores Set-level types, so CoSession
-- would need Set₂. Same trade-off as Session.agda — universe polymorphism
-- is possible but adds boilerplate with no practical benefit.
{-# NO_UNIVERSE_CHECK #-}
record CoSession : Set₁ where
  coinductive
  field
    head : SessionStep           -- what happens now
    left : CoSession             -- continuation (or left branch for offer/choose)
    right : CoSession            -- right branch for offer/choose (unused for send/recv/done)

open CoSession public

------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------

-- Terminal session (self-loop on done — coinductively valid)
coDone : CoSession
head coDone  = doneStep
left coDone  = coDone
right coDone = coDone

-- Send A then continue
coSend : (A : Set) → CoSession → CoSession
head (coSend A k)  = sendStep A
left (coSend A k)  = k
right (coSend A k) = coDone

-- Recv A then continue
coRecv : (A : Set) → CoSession → CoSession
head (coRecv A k)  = recvStep A
left (coRecv A k)  = k
right (coRecv A k) = coDone

-- Offer two branches
coOffer : CoSession → CoSession → CoSession
head (coOffer l r)  = offerStep
left (coOffer l r)  = l
right (coOffer l r) = r

-- Choose one of two branches
coChoose : CoSession → CoSession → CoSession
head (coChoose l r)  = chooseStep
left (coChoose l r)  = l
right (coChoose l r) = r

------------------------------------------------------------------------
-- Duality for CoSession
------------------------------------------------------------------------

coDual : CoSession → CoSession
head (coDual s) = dualStep (head s)
  where
    dualStep : SessionStep → SessionStep
    dualStep (sendStep A) = recvStep A
    dualStep (recvStep A) = sendStep A
    dualStep offerStep    = chooseStep
    dualStep chooseStep   = offerStep
    dualStep doneStep     = doneStep
left (coDual s)  = coDual (left s)
right (coDual s) = coDual (right s)

------------------------------------------------------------------------
-- Example: Looping protocols
------------------------------------------------------------------------

-- Echo server: forever recv String, send String
-- Server perspective: recv → send → recv → send → ...
echoLoop : CoSession
head echoLoop           = recvStep String
left echoLoop           = echoSend
  where
    echoSend : CoSession
    head echoSend  = sendStep String
    left echoSend  = echoLoop    -- loop back!
    right echoSend = coDone
right echoLoop          = coDone

-- Chat protocol: each side alternates send/recv
-- A: send → recv → send → recv → ...
chatA : CoSession
head chatA        = sendStep String
left chatA        = chatARecv
  where
    chatARecv : CoSession
    head chatARecv  = recvStep String
    left chatARecv  = chatA    -- loop!
    right chatARecv = coDone
right chatA       = coDone

-- B is dual of A: recv → send → recv → send → ...
chatB : CoSession
chatB = coDual chatA

-- Bounded loop: repeat N times then done
-- Walks through one cycle of the session, replacing the terminal doneStep
-- with the next repetition. For multi-step sessions (e.g. send → recv → done),
-- the entire cycle is preserved in each repetition.
repeatN : Nat → CoSession → CoSession
repeatN zero    _  = coDone
repeatN (suc n) s  = splice s (repeatN n s)
  where
    -- Replace doneStep leaves with the continuation k.
    -- For sendStep/recvStep, only recurse into left (the continuation);
    -- right is always coDone by invariant and must stay that way.
    splice : CoSession → CoSession → CoSession
    head (splice s k) with head s
    ... | doneStep = head k
    ... | other    = other
    left (splice s k) with head s
    ... | doneStep = left k
    ... | _        = splice (left s) k
    -- INVARIANT: sendStep/recvStep nodes have right=coDone (enforced by coSend/coRecv).
    -- Directly constructed CoSession values with non-trivial right branches
    -- will have those branches silently dropped by splice.
    right (splice s k) with head s
    ... | doneStep    = right k
    ... | sendStep _  = coDone
    ... | recvStep _  = coDone
    ... | _           = splice (right s) k

------------------------------------------------------------------------
-- Well-formedness check (N steps)
------------------------------------------------------------------------

-- Check that sendStep/recvStep nodes have right=coDone (the invariant
-- assumed by splice). Inspects up to N levels of the coinductive tree.
open import Data.Bool using (Bool; true; false; _∧_)

private
  isDone : SessionStep → Bool
  isDone doneStep = true
  isDone _        = false

wellFormedN : Nat → CoSession → Bool
wellFormedN zero    _ = true
wellFormedN (suc n) s with head s
... | doneStep   = true
... | sendStep _ = isDone (head (right s)) ∧ wellFormedN n (left s)
... | recvStep _ = isDone (head (right s)) ∧ wellFormedN n (left s)
... | offerStep  = wellFormedN n (left s) ∧ wellFormedN n (right s)
... | chooseStep = wellFormedN n (left s) ∧ wellFormedN n (right s)

------------------------------------------------------------------------
-- Embedding finite Session into CoSession
------------------------------------------------------------------------

open import Agdelte.Concurrent.Session as Fin
  using (Session; send; recv; offer; choose; done)

embedSession : Session → CoSession
embedSession (send A s) = coSend A (embedSession s)
embedSession (recv A s) = coRecv A (embedSession s)
embedSession (offer s₁ s₂) = coOffer (embedSession s₁) (embedSession s₂)
embedSession (choose s₁ s₂) = coChoose (embedSession s₁) (embedSession s₂)
embedSession done = coDone

------------------------------------------------------------------------
-- Unroll: observe N steps of a CoSession
------------------------------------------------------------------------

-- Extract first N steps as a finite Session (truncating with `done`)
unroll : Nat → CoSession → Session
unroll zero    _ = done
unroll (suc n) s with head s
... | sendStep A  = send A (unroll n (left s))
... | recvStep A  = recv A (unroll n (left s))
... | offerStep   = offer (unroll n (left s)) (unroll n (right s))
... | chooseStep  = choose (unroll n (left s)) (unroll n (right s))
... | doneStep    = done
