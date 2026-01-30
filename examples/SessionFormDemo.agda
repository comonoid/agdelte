{-# OPTIONS --without-K #-}

-- SessionFormDemo: Multi-step form with typed state transitions
--
-- Demonstrates SessionExec concepts as a ReactiveApp:
-- - Session protocol defines the form steps
-- - FormPhase tracks progress through the protocol
-- - Each step has typed state transitions
-- - The pipeline approach (nameAgent >>> emailAgent >>> summaryAgent)
--   shows how session steps compose via _>>>_

module SessionFormDemo where

open import Data.String using (String; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using ([]; _∷_; [_])
open import Function using (const)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Session protocol (conceptual):
--   recv Name → recv Email → recv Age → send Summary → done
--
-- This compiles to:
--   SessionI = String × (String × (String × ⊤))
--   SessionO = String × ⊤
--
-- We model this as a phased Agent (from SessionExec).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Model: phase-indexed form state
------------------------------------------------------------------------

data FormPhase : Set where
  enterName  : FormPhase
  enterEmail : FormPhase
  enterAge   : FormPhase
  confirm    : FormPhase
  submitted  : FormPhase

record Model : Set where
  constructor mkModel
  field
    phase   : FormPhase
    name    : String
    email   : String
    age     : String
    curInput : String      -- current input field value
    stepNum : ℕ

open Model public

initModel : Model
initModel = mkModel enterName "" "" "" "" 1


------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  UpdateInput : String → Msg
  Submit      : Msg
  Back        : Msg
  Reset       : Msg

------------------------------------------------------------------------
-- Update: typed state transitions per phase
------------------------------------------------------------------------

nextPhase : FormPhase → FormPhase
nextPhase enterName  = enterEmail
nextPhase enterEmail = enterAge
nextPhase enterAge   = confirm
nextPhase confirm    = submitted
nextPhase submitted  = submitted

prevPhase : FormPhase → FormPhase
prevPhase enterName  = enterName
prevPhase enterEmail = enterName
prevPhase enterAge   = enterEmail
prevPhase confirm    = enterAge
prevPhase submitted  = submitted

stepOf : FormPhase → ℕ
stepOf enterName  = 1
stepOf enterEmail = 2
stepOf enterAge   = 3
stepOf confirm    = 4
stepOf submitted  = 5

-- Submit: save current input to the appropriate field, advance phase
submitStep : Model → Model
submitStep m with phase m
... | enterName  = mkModel enterEmail (curInput m) (email m) (age m) "" 2
... | enterEmail = mkModel enterAge (name m) (curInput m) (age m) "" 3
... | enterAge   = mkModel confirm (name m) (email m) (curInput m) "" 4
... | confirm    = mkModel submitted (name m) (email m) (age m) "" 5
... | submitted  = m

-- Back: restore previous field to input
backStep : Model → Model
backStep m with phase m
... | enterName  = m
... | enterEmail = mkModel enterName (name m) (email m) (age m) (name m) 1
... | enterAge   = mkModel enterEmail (name m) (email m) (age m) (email m) 2
... | confirm    = mkModel enterAge (name m) (email m) (age m) (age m) 3
... | submitted  = m

updateModel : Msg → Model → Model
updateModel (UpdateInput s) m = record m { curInput = s }
updateModel Submit m = submitStep m
updateModel Back m = backStep m
updateModel Reset _ = initModel

------------------------------------------------------------------------
-- View helpers
------------------------------------------------------------------------

isInputPhase : Model → Bool
isInputPhase m with phase m
... | enterName  = true
... | enterEmail = true
... | enterAge   = true
... | _ = false

isConfirm : Model → Bool
isConfirm m with phase m
... | confirm = true
... | _ = false

isSubmitted : Model → Bool
isSubmitted m with phase m
... | submitted = true
... | _ = false

canGoBack : Model → Bool
canGoBack m with phase m
... | enterName  = false
... | submitted  = false
... | _ = true

promptText : Model → String
promptText m with phase m
... | enterName  = "Enter your name:"
... | enterEmail = "Enter your email:"
... | enterAge   = "Enter your age:"
... | confirm    = ""
... | submitted  = ""

stepLabel : Model → String
stepLabel m = "Step " ++ show (stepNum m) ++ "/4"

summaryText : Model → String
summaryText m = name m ++ " <" ++ email m ++ ">, age " ++ age m

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

formTemplate : Node Model Msg
formTemplate =
  div [ class "session-form" ]
    ( h1 [] [ text "Registration Form" ]
    ∷ div [ class "progress" ] [ bindF stepLabel ]

    -- Input phase: show prompt + input field
    ∷ when isInputPhase
        (div [ class "form-step" ]
          ( div [ class "prompt" ] [ bindF promptText ]
          ∷ input (placeholder "Type here..." ∷ onInput UpdateInput ∷ valueBind curInput ∷ [])
          ∷ div [ class "actions" ]
              ( button (onClick Submit ∷ class "btn primary" ∷ []) [ text "Next →" ]
              ∷ when canGoBack
                  (button (onClick Back ∷ class "btn" ∷ []) [ text "← Back" ])
              ∷ [] )
          ∷ [] ))

    -- Confirm phase: show summary + submit
    ∷ when isConfirm
        (div [ class "form-step confirm" ]
          ( h2 [] [ text "Confirm your details:" ]
          ∷ div [ class "summary" ]
              ( p [] [ bindF (λ m → "Name: " ++ name m) ]
              ∷ p [] [ bindF (λ m → "Email: " ++ email m) ]
              ∷ p [] [ bindF (λ m → "Age: " ++ age m) ]
              ∷ [] )
          ∷ div [ class "actions" ]
              ( button (onClick Submit ∷ class "btn primary" ∷ []) [ text "Submit ✓" ]
              ∷ button (onClick Back ∷ class "btn" ∷ []) [ text "← Back" ]
              ∷ [] )
          ∷ [] ))

    -- Submitted phase: success message
    ∷ when isSubmitted
        (div [ class "form-step done" ]
          ( h2 [] [ text "Registration Complete!" ]
          ∷ div [ class "summary" ] [ bindF summaryText ]
          ∷ button (onClick Reset ∷ class "btn" ∷ []) [ text "Start Over" ]
          ∷ [] ))

    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel formTemplate
