{-# OPTIONS --without-K --guardedness #-}

-- Phase 8 (polynomials.md): Network Inspector
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

open import Agdelte.FFI.Server using
  ( _>>=_; _>>_; pure; putStrLn; _++s_
  ; IORef; readIORef
  )
open import Agdelte.Reactive.BigLens using (IOOptic; mkIOOptic; ioPeek; ioOver)
open import Agdelte.Reactive.Diagram using (Diagram; Slot; slots; name; path; agent)
open import Agdelte.Concurrent.Agent using (Agent; state; observe)

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
    printResult l nothing  = putStrLn ("  " ++s l ++s ": <unavailable>")
    printResult l (just v) = putStrLn ("  " ++s l ++s ": " ++s v)

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
-- Inspect a Diagram (in-process: read agent state directly)
------------------------------------------------------------------------

-- Build IOOptic for each slot using its pure Agent's observe
slotOptic : Slot → IOOptic
slotOptic s =
  let a = agent s in
  mkIOOptic (pure (just (observe a (state a)))) (λ _ → pure (observe a (state a)))

-- NOTE: slotOptic reads the *initial* state of the agent.
-- For live inspection of a running server, use refOptic on the
-- IORef created by wireSlot, or processAgentOptic for remote agents.

-- Collect all slot optics from a diagram
diagramOptics : Diagram → List (String × IOOptic)
diagramOptics d = go (slots d)
  where
    go : List Slot → List (String × IOOptic)
    go [] = []
    go (s ∷ rest) = (name s , slotOptic s) ∷ go rest

-- Print full diagram inspection
inspectDiagram : Diagram → IO ⊤
inspectDiagram d =
  putStrLn "=== Network Inspector ===" >>
  putStrLn ("Agents: " ++s showCount (slots d)) >>
  inspectAll (diagramOptics d) >>
  putStrLn "========================="
  where
    showCount : List Slot → String
    showCount [] = "0"
    showCount (_ ∷ []) = "1"
    showCount (_ ∷ _ ∷ []) = "2"
    showCount (_ ∷ _ ∷ _ ∷ _) = "3+"

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

sendCommand : IOOptic → String → IO String
sendCommand optic input = ioOver optic input

-- Send command and print result
sendAndPrint : String → IOOptic → String → IO ⊤
sendAndPrint label optic input =
  putStrLn ("Sending to " ++s label ++s ": " ++s input) >>
  sendCommand optic input >>= λ result →
  putStrLn ("  Result: " ++s result)
