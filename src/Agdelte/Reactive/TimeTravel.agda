{-# OPTIONS --without-K --guardedness #-}

-- Time-Travel Debugging
--
-- Wraps a ReactiveApp to record state history.
-- Adds Undo/Redo messages that navigate through past states.
--
-- Key idea: a ReactiveApp is a coalgebra of y^Msg.
-- Time-travel wraps it with a history coalgebra:
--   History S = List S × S × List S   (past, present, future)
-- The wrapper adds Undo/Redo as extra messages.

module Agdelte.Reactive.TimeTravel where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- History record
------------------------------------------------------------------------

-- Past is stored newest-first (head = most recent past state).
-- Future is stored oldest-first (head = next redo state).
record History (S : Set) : Set where
  constructor mkHistory
  field
    past    : List S     -- previous states (newest first)
    present : S          -- current state
    future  : List S     -- undone states (oldest first)
    maxSize : Nat        -- max history length (0 = unlimited)

open History public

------------------------------------------------------------------------
-- History operations
------------------------------------------------------------------------

-- Push current state into history (on every normal update)
pushState : ∀ {S} → History S → S → History S
pushState h newState = mkHistory
  (present h ∷ trimPast (past h))
  newState
  []           -- any new action clears redo stack
  (maxSize h)
  where
    trimPast : ∀ {S} → List S → List S
    trimPast {S} xs with maxSize h
    ... | zero = xs  -- unlimited
    ... | suc n = take n xs
      where
        take : Nat → List S → List S
        take zero    _        = []
        take (suc _) []       = []
        take (suc m) (x ∷ rest) = x ∷ take m rest

-- Undo: move present to future, pop past
undo : ∀ {S} → History S → History S
undo h with past h
... | []       = h  -- nothing to undo
... | (p ∷ ps) = mkHistory ps p (present h ∷ future h) (maxSize h)

-- Redo: move present to past, pop future
redo : ∀ {S} → History S → History S
redo h with future h
... | []       = h  -- nothing to redo
... | (f ∷ fs) = mkHistory (present h ∷ past h) f fs (maxSize h)

-- Create initial history
initHistory : ∀ {S} → S → Nat → History S
initHistory s maxSz = mkHistory [] s [] maxSz

-- Get history depth
historyDepth : ∀ {S} → History S → Nat
historyDepth h = length (past h)

open import Agda.Builtin.Bool using (Bool; true; false)

-- Can undo?
canUndo : ∀ {S} → History S → Bool
canUndo h with past h
... | []    = false
... | _ ∷ _ = true

-- Can redo?
canRedo : ∀ {S} → History S → Bool
canRedo h with future h
... | []    = false
... | _ ∷ _ = true

------------------------------------------------------------------------
-- Time-travel message wrapper
------------------------------------------------------------------------

-- Wraps any message type with undo/redo controls
data TTMsg (Msg : Set) : Set where
  appMsg : Msg → TTMsg Msg       -- normal app message (gets recorded)
  ttUndo : TTMsg Msg              -- undo last action
  ttRedo : TTMsg Msg              -- redo undone action

------------------------------------------------------------------------
-- Time-travel ReactiveApp wrapper
------------------------------------------------------------------------

-- Given update : Msg → Model → Model,
-- produce update' : TTMsg Msg → History Model → History Model
ttUpdate : ∀ {Model Msg : Set} →
           (Msg → Model → Model) →
           TTMsg Msg → History Model → History Model
ttUpdate update (appMsg msg) h = pushState h (update msg (present h))
ttUpdate _      ttUndo       h = undo h
ttUpdate _      ttRedo       h = redo h
