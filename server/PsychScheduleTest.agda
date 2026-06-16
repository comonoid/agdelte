{-# OPTIONS --without-K --guardedness #-}

-- Pure unit tests for Psych.Schedule (the booking grid/availability math). No
-- store, no IO in the math — just assertions over the calendar arithmetic, the
-- working grid, overlap, availability-minus-busy, and slot validation. Prints
-- "PASS <name>" / "FAIL <name>" per check (run-ghc-tests.sh greps those).
module PsychScheduleTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (is-just; is-nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Psych.Schedule

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

cfg : Settings
cfg = defaultSettings

-- a Monday grid start at 10:00 (day 4 = 1970-01-05 = Monday)
monday : ℕ
monday = 4

s10 : ℕ
s10 = atMinute cfg monday 600

-- `_,_` and `_==_` are both at fixity level 4, so an inline tuple `(n , a == b)`
-- can't parse — use a prefix constructor where application binds tighter.
chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  -- calendar arithmetic
  chk "weekday-0-thursday" ((weekday 0) == 4) ∷
  chk "weekday-4-monday"   ((weekday 4) == 1) ∷
  chk "weekday-3-sunday"   ((weekday 3) == 7) ∷
  chk "workday-monday"     (isWorkday (weekday 4)) ∷
  chk "nonwork-sunday"     (not (isWorkday (weekday 3))) ∷
  -- working grid (10:00–19:00: 6 session slots / 18 intro slots per workday)
  chk "grid-session-6"     (length (gridSlots cfg Session monday) == 6) ∷
  chk "grid-intro-18"      (length (gridSlots cfg Intro   monday) == 18) ∷
  chk "grid-sunday-empty"  (length (gridSlots cfg Session 3) == 0) ∷
  -- on-grid validation
  chk "ongrid-yes"         (onGrid cfg Session s10) ∷
  chk "ongrid-off-by-60"   (not (onGrid cfg Session (s10 + 60))) ∷
  -- interval overlap (half-open)
  chk "overlap-yes"        (overlaps (0 , 10) (5 , 15)) ∷
  chk "overlap-touch-no"   (not (overlaps (0 , 10) (10 , 20))) ∷
  -- availability = grid − busy (book the 10:00 slot → 5 of 6 remain that day)
  chk "avail-minus-busy-5"
     (length (availabilityFrom cfg Session 0 (atMinute cfg monday 0) 1
              ((atMinute cfg monday 600 , atMinute cfg monday 690) ∷ [])) == 5) ∷
  -- validateSlot: ok / too-soon / beyond-horizon
  chk "validate-ok"        (is-nothing (validateSlot cfg Session 0 s10)) ∷
  chk "validate-too-soon"  (is-just    (validateSlot cfg Session s10 s10)) ∷
  chk "validate-horizon"   (is-just    (validateSlot cfg Session 0 (atMinute cfg 200 600))) ∷
  -- cancel policy (slice 3): ≥24h before start = free; <24h = late
  chk "cancel-free-100h"   (freeCancelWindow cfg 0 (100 * 3600)) ∷
  chk "cancel-late-10h"    (not (freeCancelWindow cfg 0 (10 * 3600))) ∷
  chk "cancel-boundary-24h" (freeCancelWindow cfg 0 (24 * 3600)) ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "psych-schedule done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
