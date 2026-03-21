{-# OPTIONS --without-K #-}

-- Course progress tracking component.
-- Shows per-lesson completion marks and overall course progress.
-- Client-side: periodic position sync, auto-complete at ≥90%.

module Agdelte.Html.Controls.Video.Progress where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agda.Builtin.String using (primShowNat)
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

record LessonProgress : Set where
  constructor mkLessonProgress
  field
    lpLessonId  : ℕ
    lpTitle     : String
    lpCompleted : Bool
    lpPosition  : ℕ       -- seconds watched
    lpDuration  : ℕ       -- total seconds

open LessonProgress public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Count completed lessons in a list.
countCompleted : List LessonProgress → ℕ
countCompleted [] = zero
countCompleted (l ∷ ls) = if lpCompleted l then suc (countCompleted ls) else countCompleted ls

-- | Safe division for percentages (avoids NonZero constraint).
postulate safeDiv : ℕ → ℕ → ℕ
{-# COMPILE JS safeDiv = function(n) { return function(d) { return d === 0 ? 0 : Math.floor(n / d); }; } #-}

-- | Percentage string: completed / total * 100
percentStr : ℕ → ℕ → String
percentStr n total = primShowNat (safeDiv (n * 100) total)

------------------------------------------------------------------------
-- Course progress bar
------------------------------------------------------------------------

-- | Overall course progress: "X / Y lessons completed (Z%)"
courseProgressBar : ∀ {M A}
                 → (M → List LessonProgress)
                 → Node M A
courseProgressBar getLessons =
  div (class "agdelte-course-progress" ∷ [])
    ( div (class "agdelte-course-progress__bar" ∷
           styleBind "width" (stringBinding (λ m →
             let ls = getLessons m
             in percentStr (countCompleted ls) (length ls) ++ "%")) ∷
           [])
        []
    ∷ span (class "agdelte-course-progress__text" ∷ [])
        ( bindF (λ m →
            let ls = getLessons m
                done = countCompleted ls
                total = length ls
            in primShowNat done ++ " / " ++ primShowNat total ++ " уроков")
        ∷ [])
    ∷ [])

------------------------------------------------------------------------
-- Lesson list with completion marks
------------------------------------------------------------------------

-- | Single lesson row with checkmark and title.
-- Takes a concrete lessonId for the onClick handler (since onClick
-- needs a static message, not a model-dependent one).
lessonRow : ∀ {M A}
          → (M → LessonProgress)
          → ℕ                    -- lessonId (for onClick)
          → (ℕ → A)             -- onSelect: lessonId → msg
          → Node M A
lessonRow getLesson lid onSelect =
  div (class "agdelte-lesson-row" ∷
       classBind (λ m → if lpCompleted (getLesson m)
                        then "agdelte-lesson-row--completed"
                        else "") ∷
       onClick (onSelect lid) ∷
       [])
    ( span (class "agdelte-lesson-row__check" ∷ [])
        ( bindF (λ m → if lpCompleted (getLesson m) then "✓" else "○") ∷ [])
    ∷ span (class "agdelte-lesson-row__title" ∷ [])
        ( bindF (λ m → lpTitle (getLesson m)) ∷ [])
    ∷ span (class "agdelte-lesson-row__time" ∷ [])
        ( bindF (λ m → let l = getLesson m
                          in primShowNat (lpPosition l) ++ " / " ++ primShowNat (lpDuration l) ++ "с") ∷ [])
    ∷ [])

------------------------------------------------------------------------
-- Progress sync configuration
------------------------------------------------------------------------

-- | Interval for sending progress updates to server (milliseconds).
syncIntervalMs : ℕ
syncIntervalMs = 30000    -- every 30 seconds

-- | Threshold for marking a lesson as completed (percentage 0–100).
completionThreshold : ℕ
completionThreshold = 90
