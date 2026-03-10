{-# OPTIONS --without-K #-}

-- Combinators: stateful event combinators
-- Demonstrates: foldE (internal state), mapE (transform)

module Combinators where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Nat.DivMod using (_%_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit using (⊤; tt)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd using (Cmd; ε)
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    running    : Bool
    tickCount  : ℕ      -- all ticks
    batchCount : ℕ      -- every-5th-tick batches
    lastBatchAt : ℕ     -- tick number of last batch

open Model public

initialModel : Model
initialModel = mkModel false 0 0 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Toggle    : Msg
  Tick      : Msg           -- regular tick (4 out of 5)
  BatchTick : ℕ → Msg       -- every 5th tick (carries tick number)
  Reset     : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Toggle m = record m { running = not (running m) }
updateModel Tick m = record m { tickCount = suc (tickCount m) }
updateModel (BatchTick n) m = record m
  { tickCount   = suc (tickCount m)
  ; batchCount  = suc (batchCount m)
  ; lastBatchAt = n
  }
updateModel Reset m = record m { running = false ; tickCount = 0 ; batchCount = 0 ; lastBatchAt = 0 }

------------------------------------------------------------------------
-- Subscriptions: foldE + mapE pipeline
--
-- Pipeline:
--   interval 300ms ⊤           -- raw tick source
--   → foldE 0 (λ _ n → suc n) -- count internally: 1, 2, 3, 4, 5, ...
--   → mapE classify            -- every 5th → BatchTick, rest → Tick
------------------------------------------------------------------------

isBatch : ℕ → Bool
isBatch n = (n % 5) ≡ᵇ 0

subs' : Model → Event Msg
subs' m = if running m
  then mapE classify (foldE 0 (λ _ n → suc n) (interval 300 tt))
  else never
  where
    classify : ℕ → Msg
    classify n = if isBatch n then BatchTick n else Tick

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

toggleText : Model → String
toggleText m = if running m then "Stop" else "Start"

tickText : Model → String
tickText m = show (tickCount m)

batchText : Model → String
batchText m = show (batchCount m)

lastBatchText : Model → String
lastBatchText m = if lastBatchAt m ≡ᵇ 0
  then "—"
  else "at tick #" ++ show (lastBatchAt m)

combinatorsTemplate : Node Model Msg
combinatorsTemplate =
  div [ class "combinators-demo" ]
    ( h1 [] [ text "Combinators" ]
    ∷ p [ class "description" ]
        [ text "foldE + mapE: stateful event pipeline" ]

    ∷ div [ class "controls" ]
        ( button (onClick Toggle ∷ class "btn" ∷ []) [ bindF toggleText ]
        ∷ button (onClick Reset ∷ class "btn reset-btn" ∷ []) [ text "Reset" ]
        ∷ [] )

    ∷ div [ class "stats" ]
        ( div [ class "stat" ]
            ( span [ class "stat-label" ] [ text "All ticks" ]
            ∷ span [ class "stat-value tick-value" ] [ bindF tickText ]
            ∷ [] )
        ∷ div [ class "stat batch-stat" ]
            ( span [ class "stat-label" ] [ text "Batches (every 5th)" ]
            ∷ span [ class "stat-value batch-value" ] [ bindF batchText ]
            ∷ [] )
        ∷ div [ class "stat" ]
            ( span [ class "stat-label" ] [ text "Last batch" ]
            ∷ span [ class "stat-value" ] [ bindF lastBatchText ]
            ∷ [] )
        ∷ [] )

    ∷ div [ class "explanation" ]
        ( p [] [ text "Pipeline: interval 300ms → foldE (count internally) → mapE (classify)" ]
        ∷ p [] [ text "foldE maintains a tick counter as internal state (not in the model)" ]
        ∷ p [] [ text "mapE: every 5th tick → BatchTick, others → Tick" ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel combinatorsTemplate (λ _ _ → ε) subs'
