{-# OPTIONS --without-K --guardedness #-}

-- Network Inspector
--
-- Inspect agent network state via IOOptic (Big Lens).
-- Given a Diagram, construct IOOptic for each slot,
-- then peek all agents and print their state.
--
-- This is the "DevTools" side of Big Lens:
--   Inspector peeks each agent → displays topology + state
--   Can also send commands (over) to any agent.

module Agdelte.Reactive.Inspector where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Data.String using (_++_)
open import Agdelte.FFI.Server using
  ( _>>=_; _>>_; pure; putStrLn
  ; IORef; newIORef; readIORef; writeIORef
  )
open import Agdelte.Reactive.BigLens using (IOOptic; mkIOOptic; ioPeek; ioOver)
open import Agdelte.Reactive.Diagram using (Diagram; Slot; slots; name; path; agent)
open import Agdelte.Concurrent.Agent using (Agent; state; observe; step)

------------------------------------------------------------------------
-- Agent IOOptic from a wired slot's state ref
------------------------------------------------------------------------

-- After wireSlot, each agent has an IORef String for its state.
-- The inspector can peek that directly (same process) or via IPC.
-- For in-process inspection, we use refOptic from BigLens.
-- For remote inspection, we use processAgentOptic.

open import Agdelte.Reactive.BigLens using (refOptic; processAgentOptic)

------------------------------------------------------------------------
-- Inspect a list of IOOptics
------------------------------------------------------------------------

-- Peek one optic, print result with label
inspectOne : String → IOOptic → IO ⊤
inspectOne label optic =
  ioPeek optic >>= λ result →
  printResult label result
  where
    printResult : String → Maybe String → IO ⊤
    printResult l nothing  = putStrLn ("  " ++ l ++ ": <unavailable>")
    printResult l (just v) = putStrLn ("  " ++ l ++ ": " ++ v)

open import Data.Product using (_×_; _,_)

-- Inspect a list of (name, optic) pairs
inspectAll : List (String × IOOptic) → IO ⊤
inspectAll [] = pure tt
  where open import Agda.Builtin.Unit using (tt)
inspectAll (p ∷ rest) =
  inspectOne (proj₁ p) (proj₂ p) >>
  inspectAll rest
  where open import Data.Product using (proj₁; proj₂)

------------------------------------------------------------------------
-- Inspect a Diagram (pure / initial state)
------------------------------------------------------------------------

-- Pure snapshot: peeks initial state, ioOver steps from init each time
-- (no persistence). For stateful inspection of running agents, use inspectLive.
slotSnapshotOptic : Slot → IOOptic
slotSnapshotOptic s =
  let a = agent s in
  mkIOOptic (pure (just (observe a (state a))))
            (λ input → pure (just (observe a (step a (state a) input))))

-- Stateful optic: tracks agent state across steps via IORef.
-- Unlike slotSnapshotOptic (which always steps from initial state),
-- this persists state: each ioOver mutates the IORef.
slotStatefulOptic : Slot → IO IOOptic
slotStatefulOptic s =
  let a = agent s in
  newIORef (state a) >>= λ ref →
  pure (mkIOOptic
    (readIORef ref >>= λ st → pure (just (observe a st)))
    (λ input → readIORef ref >>= λ st →
      let newSt = step a st input
      in writeIORef ref newSt >>
         pure (just (observe a newSt))))

-- Collect all slot optics from a diagram (initial state)
diagramInitialOptics : Diagram → List (String × IOOptic)
diagramInitialOptics d = go (slots (Diagram.spec d))
  where
    go : List Slot → List (String × IOOptic)
    go [] = []
    go (s ∷ rest) = (name s , slotSnapshotOptic s) ∷ go rest

-- Print diagram inspection from initial state (pure, no IORef needed)
inspectInitial : Diagram → IO ⊤
inspectInitial d =
  putStrLn "=== Network Inspector (initial state) ===" >>
  putStrLn ("Agents: " ++ showCount (slots (Diagram.spec d))) >>
  inspectAll (diagramInitialOptics d) >>
  putStrLn "========================="
  where
    showCount : List Slot → String
    showCount ss = primShowNat (len ss)
      where
        open import Agda.Builtin.String using (primShowNat)
        open import Agda.Builtin.Nat using (Nat; zero; suc)
        len : List Slot → Nat
        len [] = zero
        len (_ ∷ rest) = suc (len rest)

------------------------------------------------------------------------
-- Inspect live state via IORef (for running servers)
------------------------------------------------------------------------

-- Build IOOptic from a live IORef (created by wireSlot/wireAgent)
slotRefOptic : String → IORef String → String × IOOptic
slotRefOptic label ref = label , refOptic ref

-- Print live diagram inspection from a list of (name, IORef) pairs
inspectLive : List (String × IORef String) → IO ⊤
inspectLive refs =
  putStrLn "=== Network Inspector (live) ===" >>
  inspectAll (go refs) >>
  putStrLn "========================="
  where
    go : List (String × IORef String) → List (String × IOOptic)
    go [] = []
    go ((label , ref) ∷ rest) = slotRefOptic label ref ∷ go rest

------------------------------------------------------------------------
-- Remote inspection via Unix socket
------------------------------------------------------------------------

-- Inspect a remote agent by socket path
inspectRemote : String → String → IO ⊤
inspectRemote label socketPath =
  inspectOne label (processAgentOptic socketPath)

------------------------------------------------------------------------
-- Send command to agent (over)
------------------------------------------------------------------------

sendCommand : IOOptic → String → IO (Maybe String)
sendCommand optic input = ioOver optic input

-- Send command and print result
sendAndPrint : String → IOOptic → String → IO ⊤
sendAndPrint label optic input =
  putStrLn ("Sending to " ++ label ++ ": " ++ input) >>
  sendCommand optic input >>= printResult
  where
    printResult : Maybe String → IO ⊤
    printResult (just result) = putStrLn ("  Result: " ++ result)
    printResult nothing       = putStrLn ("  Result: <error>")
