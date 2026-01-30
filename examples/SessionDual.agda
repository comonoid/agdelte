{-# OPTIONS --without-K --guardedness #-}

-- SessionDual: dual session types — client and server with matching protocols
--
-- Shows: Session, dual, SessionI, SessionO, SessionAgent,
--        mkReqResp, mkOffer, peekLens, stepLens, through,
--        and the duality invariant: dual (dual s) ≡ s
--
-- Scenario: a key-value store protocol
--   Server offers:   get (recv Key, send Value)  |  put (recv Key×Value, send Ok)
--   Client sees:    get (send Key, recv Value)   |  put (send Key×Value, recv Ok)
--   Duality ensures they match.

module SessionDual where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; const; _∘_)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring
open import Agdelte.Concurrent.Session

------------------------------------------------------------------------
-- 1. Protocol definition
------------------------------------------------------------------------

-- Get protocol: server receives key, sends value
GetProto : Session
GetProto = recv String (send String done)

-- Put protocol: server receives key+value pair, sends acknowledgement
PutProto : Session
PutProto = recv String (send String done)
-- (simplified: key is the input, "ok" is the response)

-- Full key-value protocol: server offers get or put
KVProto : Session
KVProto = offer GetProto PutProto

------------------------------------------------------------------------
-- 2. Server implementation
------------------------------------------------------------------------

-- Server state: stores one key-value pair (simplified)
record KVState : Set where
  constructor mkKV
  field
    storedKey : String
    storedVal : String

open KVState public

-- Get agent: receives key, returns stored value (ignores key for simplicity)
getAgent : SessionAgent GetProto KVState
getAgent = mkReqResp
  (mkKV "" "initial")
  (λ s → storedVal s)     -- observe: return stored value
  (λ s _ → s)             -- step: receive key, state unchanged

-- Put agent: receives new value, stores it, returns "ok"
putAgent : SessionAgent PutProto KVState
putAgent = mkReqResp
  (mkKV "" "initial")
  (λ _ → "ok")            -- observe: always "ok"
  (λ _ val → mkKV "key" val)  -- step: store new value

-- Full server: offers get or put
kvServer : SessionAgent KVProto (KVState × KVState)
kvServer = mkOffer {GetProto} {PutProto} getAgent putAgent

------------------------------------------------------------------------
-- 3. Dual protocol: what the client sees
------------------------------------------------------------------------

-- Client sees the dual:
--   dual (offer GetProto PutProto) = choose (dual GetProto) (dual PutProto)
-- where:
--   dual (recv String (send String done)) = send String (recv String done)

ClientKVProto : Session
ClientKVProto = dual KVProto

-- Verify the dual structure
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- dual (offer get put) = choose (send String (recv String done))
--                                (send String (recv String done))
_ : ClientKVProto ≡ choose
                       (send String (recv String done))
                       (send String (recv String done))
_ = refl

------------------------------------------------------------------------
-- 4. Duality is an involution
------------------------------------------------------------------------

-- Importing the proof from Theory
open import Agdelte.Theory.SessionDualProof using (dual-involution; dual-injective)

-- dual (dual KVProto) ≡ KVProto
_ : dual (dual KVProto) ≡ KVProto
_ = dual-involution KVProto

-- The types match: what server sends, client receives
-- SessionO (server) ≡ SessionI (dual = client), definitionally:
--
-- Server output for GetProto:
--   SessionO (recv String (send String done)) = String × ⊤
-- Client input for dual GetProto:
--   SessionI (send String (recv String done)) = String × ⊤
-- They are definitionally equal.

_ : SessionO GetProto ≡ SessionI (dual GetProto)
_ = refl

_ : SessionI GetProto ≡ SessionO (dual GetProto)
_ = refl

------------------------------------------------------------------------
-- 5. Using the server via AgentLens selectors
------------------------------------------------------------------------

-- Select just the "get" interface from the server
-- selectLeft/selectRight from Wiring.agda pick one branch of &
getOnly : Agent (KVState × KVState) (SessionI GetProto) (SessionO GetProto)
getOnly = through selectLeft kvServer

-- Select just the "put" interface
putOnly : Agent (KVState × KVState) (SessionI PutProto) (SessionO PutProto)
putOnly = through selectRight kvServer

------------------------------------------------------------------------
-- 6. End-to-end: server step verification
------------------------------------------------------------------------

private
  -- Step the get branch: send key "x", get stored value
  getInput : SessionI GetProto
  getInput = "x" , tt

  getResult : SessionO GetProto
  getResult = observe getOnly (state getOnly)

  -- Output is (String × ⊤) where String is the stored value
  _ : proj₁ getResult ≡ "initial"
  _ = refl

  -- Step the put branch: send value "hello"
  putInput : SessionI PutProto
  putInput = "hello" , tt

  putResult : SessionO PutProto
  putResult = observe putOnly (state putOnly)

  -- Output is (String × ⊤) where String is "ok"
  _ : proj₁ putResult ≡ "ok"
  _ = refl

  -- After put step, value is stored
  putStepped : KVState × KVState
  putStepped = step putOnly (state putOnly) putInput

  -- The put agent's state now has the new value
  putState : KVState
  putState = proj₂ putStepped

  _ : storedVal putState ≡ "hello"
  _ = refl

------------------------------------------------------------------------
-- 7. Custom protocol: ping-pong
------------------------------------------------------------------------

-- Server sends pong, client sends ping (2 rounds)
PingPong : Session
PingPong = recv ⊤ (send String done)

-- Dual: client sends ping, receives pong
ClientPingPong : Session
ClientPingPong = dual PingPong

_ : ClientPingPong ≡ send ⊤ (recv String done)
_ = refl

-- Types align:
_ : SessionI PingPong ≡ SessionO ClientPingPong
_ = refl

_ : SessionO PingPong ≡ SessionI ClientPingPong
_ = refl

-- Server agent for ping-pong
pingPongServer : SessionAgent PingPong ℕ
pingPongServer = mkReqResp
  zero
  (λ n → "pong-" ++ show n)   -- observe: pong with counter
  (λ n _ → suc n)             -- step: increment on each ping

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- This example demonstrates:
-- 1. Protocol definition with Session (send/recv/offer/choose/done)
-- 2. Server implementation via mkReqResp, mkOffer
-- 3. Automatic duality: dual flips send↔recv, offer↔choose
-- 4. Proven involution: dual (dual s) ≡ s (from SessionDualProof)
-- 5. Type-level guarantee: SessionO server ≡ SessionI client
-- 6. Interface selection via peekLens/stepLens + through
-- 7. Step verification with propositional equality proofs
