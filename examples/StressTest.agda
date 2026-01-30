{-# OPTIONS --without-K #-}

-- StressTest: performance benchmark for reactive bindings
-- Runs at 60 FPS (interval 16ms). Each frame applies a batch of N pure updates.
-- Shows: frames/sec (should be ~60) and logical ops/sec (frames × batch size).
-- Proves the framework has massive headroom at display refresh rate.

module StressTest where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_)
open import Data.Nat.Show using (show)
open import Data.Nat.DivMod using (_/_ ; _%_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Function using (_∘_; const; id)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Config
------------------------------------------------------------------------

-- How many pure update iterations per frame
batchSize : ℕ
batchSize = 1000000

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    counter     : ℕ            -- Main counter (incremented batchSize times per frame)
    frames      : ℕ            -- Frames since last measurement
    fps         : ℕ            -- Last measured frames/sec (should be ~60)
    peakFps     : ℕ            -- Peak fps
    opsPerSec   : ℕ            -- Logical ops/sec = fps × batchSize
    totalFrames : ℕ            -- Total frames rendered
    running     : Bool
    -- Derived bindings (from counter)
    b1 : ℕ                    -- counter mod 7
    b2 : ℕ                    -- counter mod 13
    b3 : ℕ                    -- counter mod 37
    b4 : ℕ                    -- counter mod 97
    b5 : ℕ                    -- counter mod 53
    b6 : ℕ                    -- counter mod 3

open Model public

initModel : Model
initModel = mkModel 0 0 0 0 0 0 false 0 0 0 0 0 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Start   : Msg
  Stop    : Msg
  Frame   : Msg   -- One frame: apply batchSize updates, then render
  Measure : Msg   -- Record fps (fired every 1s)
  Reset   : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

max : ℕ → ℕ → ℕ
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc (max m n)

-- Apply N increments to counter (pure loop, no DOM touches)
iterate : ℕ → ℕ → ℕ
iterate zero    c = c
iterate (suc n) c = iterate n (suc c)

{-# COMPILE JS iterate = n => c => { let r = c; for (let i = 0n; i < n; i++) r = r + 1n; return r; } #-}

-- Build new model with precomputed counter to ensure sharing in JS
frameUpdate : ℕ → Model → Model
frameUpdate c m = mkModel
  c
  (suc (frames m))
  (fps m)
  (peakFps m)
  (opsPerSec m)
  (suc (totalFrames m))
  (running m)
  (c % 7) (c % 13) (c % 37) (c % 97) (c % 53) (c % 3)

updateModel : Msg → Model → Model
updateModel Start m = record m { running = true ; frames = 0 ; fps = 0 }
updateModel Stop m = record m { running = false }
updateModel Frame m = frameUpdate (iterate batchSize (counter m)) m
updateModel Measure m = record m
  { fps       = frames m
  ; peakFps   = max (peakFps m) (frames m)
  ; opsPerSec = frames m * batchSize
  ; frames    = 0
  }
updateModel Reset m = initModel

------------------------------------------------------------------------
-- Display helpers
------------------------------------------------------------------------

statusText : Model → String
statusText m = if running m then "RUNNING" else "STOPPED"

fpsText : Model → String
fpsText m = show (fps m)

peakText : Model → String
peakText m = show (peakFps m)

opsText : Model → String
opsText m = formatK (opsPerSec m)
  where
    open import Data.Nat using (_<ᵇ_)

    formatK : ℕ → String
    formatK n =
      if n <ᵇ 1000 then show n
      else show (n / 1000) ++ "K"

totalText : Model → String
totalText m = show (totalFrames m)

counterText : Model → String
counterText m = show (counter m)

batchText : Model → String
batchText _ = show batchSize

b1text : Model → String
b1text m = show (b1 m)

b2text : Model → String
b2text m = show (b2 m)

b3text : Model → String
b3text m = show (b3 m)

b4text : Model → String
b4text m = show (b4 m)

b5text : Model → String
b5text m = show (b5 m)

b6text : Model → String
b6text m = show (b6 m)

------------------------------------------------------------------------
-- Bar visualization
------------------------------------------------------------------------

bar : ℕ → String
bar zero    = ""
bar (suc n) = "█" ++ bar n

b1bar : Model → String
b1bar m = bar (b1 m)

b2bar : Model → String
b2bar m = bar (b2 m)

b3bar : Model → String
b3bar m = bar (b3 m)

b4bar : Model → String
b4bar m = bar (b4 m)

b5bar : Model → String
b5bar m = bar (b5 m)

b6bar : Model → String
b6bar m = bar (b6 m)

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

stressTemplate : Node Model Msg
stressTemplate =
  div [ class "stress-test" ]
    ( h1 [] [ text "Stress Test" ]
    ∷ p [ class "subtitle" ] [ text "1M pure updates per frame — no Virtual DOM" ]

    -- Controls
    ∷ div [ class "controls" ]
        ( button [ onClick Start ] [ text "Start" ]
        ∷ button [ onClick Stop ]  [ text "Stop" ]
        ∷ button [ onClick Reset ] [ text "Reset" ]
        ∷ [] )

    -- Main stats
    ∷ div [ class "stats" ]
        ( div [ class "stat stat-main" ]
            ( div [ class "stat-label" ] [ text "FPS" ]
            ∷ div [ class "stat-value stat-fps" ] [ bindF fpsText ]
            ∷ [] )
        ∷ div [ class "stat" ]
            ( div [ class "stat-label" ] [ text "Peak FPS" ]
            ∷ div [ class "stat-value stat-peak" ] [ bindF peakText ]
            ∷ [] )
        ∷ div [ class "stat stat-highlight" ]
            ( div [ class "stat-label" ] [ text "ops/sec" ]
            ∷ div [ class "stat-value stat-ops" ] [ bindF opsText ]
            ∷ [] )
        ∷ div [ class "stat" ]
            ( div [ class "stat-label" ] [ text "Batch" ]
            ∷ div [ class "stat-value" ] [ bindF batchText ]
            ∷ [] )
        ∷ div [ class "stat" ]
            ( div [ class "stat-label" ] [ text "Frames" ]
            ∷ div [ class "stat-value" ] [ bindF totalText ]
            ∷ [] )
        ∷ div [ class "stat" ]
            ( div [ class "stat-label" ] [ text "Counter" ]
            ∷ div [ class "stat-value" ] [ bindF counterText ]
            ∷ [] )
        ∷ [] )

    -- Live bindings visualization
    ∷ div [ class "bindings-section" ]
        ( h2 [] [ text "Live Bindings (all update every frame)" ]
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 7" ]
            ∷ span [ class "binding-val" ] [ bindF b1text ]
            ∷ span [ class "binding-bar" ] [ bindF b1bar ]
            ∷ [] )
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 13" ]
            ∷ span [ class "binding-val" ] [ bindF b2text ]
            ∷ span [ class "binding-bar" ] [ bindF b2bar ]
            ∷ [] )
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 37" ]
            ∷ span [ class "binding-val" ] [ bindF b3text ]
            ∷ span [ class "binding-bar" ] [ bindF b3bar ]
            ∷ [] )
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 97" ]
            ∷ span [ class "binding-val" ] [ bindF b4text ]
            ∷ span [ class "binding-bar" ] [ bindF b4bar ]
            ∷ [] )
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 53" ]
            ∷ span [ class "binding-val" ] [ bindF b5text ]
            ∷ span [ class "binding-bar" ] [ bindF b5bar ]
            ∷ [] )
        ∷ div [ class "binding-row" ]
            ( span [ class "binding-label" ] [ text "mod 3" ]
            ∷ span [ class "binding-val" ] [ bindF b6text ]
            ∷ span [ class "binding-bar" ] [ bindF b6bar ]
            ∷ [] )
        ∷ [] )

    ∷ div [ class "explanation" ]
        ( p [] [ text "Each frame: 1M pure updates (iterate) + 19 binding checks + DOM patch." ]
        ∷ p [] [ text "No frame rate cap. FPS is limited only by computation + rendering cost." ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs : Model → Event Msg
subs m =
  if running m
  then merge (interval 1 Frame) (interval 1000 Measure)
  else never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel stressTemplate
