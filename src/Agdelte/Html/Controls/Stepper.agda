{-# OPTIONS --without-K #-}

-- Stepper: Step-by-step wizard navigation
-- CSS classes: .agdelte-stepper, .agdelte-stepper__step,
--              .agdelte-stepper__number, .agdelte-stepper__label,
--              .agdelte-stepper__line

module Agdelte.Html.Controls.Stepper where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

open import Agda.Builtin.String using (primShowNat)

------------------------------------------------------------------------
-- Step definition
------------------------------------------------------------------------

record Step : Set where
  constructor mkStep
  field
    stepLabel       : String
    stepDescription : String   -- optional description

open Step public

------------------------------------------------------------------------
-- Helper
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

------------------------------------------------------------------------
-- Horizontal stepper
------------------------------------------------------------------------

-- | Horizontal stepper showing numbered steps.
-- | currentStep: extract current step index (0-indexed)
-- | steps: list of step definitions
stepper : ∀ {M A}
        → (M → ℕ)        -- current step index
        → List Step
        → Node M A
stepper {M} {A} currentStep steps =
  div ( class "agdelte-stepper" ∷ attr "role" "navigation" ∷ [] )
    (renderSteps 0 (length steps) steps)
  where
    getStepClass : ℕ → ℕ → String
    getStepClass idx current =
      if idx <ᵇ current then "agdelte-stepper__step agdelte-stepper__step--completed"
      else if idx ≡ᵇ current then "agdelte-stepper__step agdelte-stepper__step--active"
      else "agdelte-stepper__step"

    renderStep : ℕ → ℕ → Step → Node M A
    renderStep idx total step =
      div ( attrBind "class" (mkBinding
              (λ m → getStepClass idx (currentStep m))
              eqStr)
          ∷ [] )
        ( div ( class "agdelte-stepper__indicator" ∷ [] )
            ( span ( class "agdelte-stepper__number" ∷ [] )
                ( text (primShowNat (suc idx)) ∷ [] )
            ∷ [] )
        ∷ div ( class "agdelte-stepper__content" ∷ [] )
            ( span ( class "agdelte-stepper__label" ∷ [] )
                ( text (stepLabel step) ∷ [] )
            ∷ span ( class "agdelte-stepper__description" ∷ [] )
                ( text (stepDescription step) ∷ [] )
            ∷ [] )
        ∷ (if suc idx <ᵇ total
           then div ( class "agdelte-stepper__line" ∷ [] ) [] ∷ []
           else []) )

    {-# TERMINATING #-}
    renderSteps : ℕ → ℕ → List Step → List (Node M A)
    renderSteps _ _ [] = []
    renderSteps idx total (s ∷ ss) =
      renderStep idx total s ∷ renderSteps (suc idx) total ss

------------------------------------------------------------------------
-- Clickable stepper
------------------------------------------------------------------------

-- | Stepper where steps can be clicked to navigate.
-- | currentStep: current step index
-- | goToStep: message to go to step (receives index)
-- | steps: list of step definitions
clickableStepper : ∀ {M A}
                 → (M → ℕ)        -- current step
                 → (ℕ → A)        -- go to step message
                 → List Step
                 → Node M A
clickableStepper {M} {A} currentStep goToStep steps =
  div ( class "agdelte-stepper agdelte-stepper--clickable"
      ∷ attr "role" "navigation"
      ∷ [] )
    (renderSteps 0 (length steps) steps)
  where
    getStepClass : ℕ → ℕ → String
    getStepClass idx current =
      if idx <ᵇ current then "agdelte-stepper__step agdelte-stepper__step--completed"
      else if idx ≡ᵇ current then "agdelte-stepper__step agdelte-stepper__step--active"
      else "agdelte-stepper__step"

    renderStep : ℕ → ℕ → Step → Node M A
    renderStep idx total step =
      button ( attrBind "class" (mkBinding
                 (λ m → getStepClass idx (currentStep m))
                 eqStr)
             ∷ onClick (goToStep idx)
             ∷ [] )
        ( div ( class "agdelte-stepper__indicator" ∷ [] )
            ( span ( class "agdelte-stepper__number" ∷ [] )
                ( text (primShowNat (suc idx)) ∷ [] )
            ∷ [] )
        ∷ div ( class "agdelte-stepper__content" ∷ [] )
            ( span ( class "agdelte-stepper__label" ∷ [] )
                ( text (stepLabel step) ∷ [] )
            ∷ [] )
        ∷ (if suc idx <ᵇ total
           then div ( class "agdelte-stepper__line" ∷ [] ) [] ∷ []
           else []) )

    {-# TERMINATING #-}
    renderSteps : ℕ → ℕ → List Step → List (Node M A)
    renderSteps _ _ [] = []
    renderSteps idx total (s ∷ ss) =
      renderStep idx total s ∷ renderSteps (suc idx) total ss

------------------------------------------------------------------------
-- Vertical stepper
------------------------------------------------------------------------

-- | Vertical stepper layout.
verticalStepper : ∀ {M A}
                → (M → ℕ)        -- current step
                → List Step
                → Node M A
verticalStepper {M} {A} currentStep steps =
  div ( class "agdelte-stepper agdelte-stepper--vertical"
      ∷ attr "role" "navigation"
      ∷ [] )
    (renderSteps 0 (length steps) steps)
  where
    getStepClass : ℕ → ℕ → String
    getStepClass idx current =
      if idx <ᵇ current then "agdelte-stepper__step agdelte-stepper__step--completed"
      else if idx ≡ᵇ current then "agdelte-stepper__step agdelte-stepper__step--active"
      else "agdelte-stepper__step"

    renderStep : ℕ → ℕ → Step → Node M A
    renderStep idx total step =
      div ( attrBind "class" (mkBinding
              (λ m → getStepClass idx (currentStep m))
              eqStr)
          ∷ [] )
        ( div ( class "agdelte-stepper__indicator" ∷ [] )
            ( span ( class "agdelte-stepper__number" ∷ [] )
                ( text (primShowNat (suc idx)) ∷ [] )
            ∷ (if suc idx <ᵇ total
               then div ( class "agdelte-stepper__line" ∷ [] ) [] ∷ []
               else []) )
        ∷ div ( class "agdelte-stepper__content" ∷ [] )
            ( span ( class "agdelte-stepper__label" ∷ [] )
                ( text (stepLabel step) ∷ [] )
            ∷ span ( class "agdelte-stepper__description" ∷ [] )
                ( text (stepDescription step) ∷ [] )
            ∷ [] )
        ∷ [] )

    {-# TERMINATING #-}
    renderSteps : ℕ → ℕ → List Step → List (Node M A)
    renderSteps _ _ [] = []
    renderSteps idx total (s ∷ ss) =
      renderStep idx total s ∷ renderSteps (suc idx) total ss

------------------------------------------------------------------------
-- Simple stepper from strings
------------------------------------------------------------------------

-- | Simple stepper from list of step labels.
simpleStepper : ∀ {M A}
              → (M → ℕ)          -- current step
              → List String      -- step labels
              → Node M A
simpleStepper {M} {A} currentStep labels =
  stepper currentStep (map (λ lbl → mkStep lbl "") labels)

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | Create step with label only
step : String → Step
step lbl = mkStep lbl ""

-- | Create step with label and description
stepWithDesc : String → String → Step
stepWithDesc = mkStep
