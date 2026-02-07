{-# OPTIONS --without-K --guardedness #-}

-- Demo: Multi-step form with typed state transitions
--
-- Models a 3-step registration form as a Session protocol:
--   Step 1: recv Name     (user enters name)
--   Step 2: recv Email    (user enters email)
--   Step 3: send Summary  (display confirmation)
--
-- Each step is an Agent, composed via _>>>_ into a pipeline.
-- The Session type guarantees the correct order of steps.

module Agdelte.Concurrent.SessionForm where

open import Agda.Builtin.String using (String; primStringAppend)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; const)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring using (_>>>_)
open import Agdelte.Concurrent.Session

------------------------------------------------------------------------
-- Form protocol: recv Name → recv Email → send Summary → done
------------------------------------------------------------------------

FormProtocol : Session
FormProtocol = recv String (recv String (send String done))

-- SessionI FormProtocol = String × (String × ⊤) ≈ String × String
-- SessionO FormProtocol = String × ⊤ ≈ String

------------------------------------------------------------------------
-- Form state: tracks progress through the protocol
------------------------------------------------------------------------

data FormPhase : Set where
  enterName  : FormPhase
  enterEmail : FormPhase
  confirm    : FormPhase
  submitted  : FormPhase

record FormState : Set where
  constructor mkForm
  field
    phase : FormPhase
    name  : String
    email : String

open FormState public

initForm : FormState
initForm = mkForm enterName "" ""

------------------------------------------------------------------------
-- Form Agent: phased state machine
------------------------------------------------------------------------

_++_ : String → String → String
_++_ = primStringAppend
infixr 5 _++_

showPhase : FormPhase → String
showPhase enterName  = "Enter your name"
showPhase enterEmail = "Enter your email"
showPhase confirm    = "Confirm"
showPhase submitted  = "Submitted"

formObserve : FormState → String
formObserve fs with phase fs
... | enterName  = "Step 1/3: " ++ showPhase enterName
... | enterEmail = "Step 2/3: " ++ showPhase enterEmail ++ " (name: " ++ name fs ++ ")"
... | confirm    = "Step 3/3: " ++ name fs ++ " <" ++ email fs ++ ">"
... | submitted  = "Done! Registered: " ++ name fs ++ " <" ++ email fs ++ ">"

formStep : FormState → String → FormState
formStep fs input with phase fs
... | enterName  = mkForm enterEmail input (email fs)
... | enterEmail = mkForm confirm (name fs) input
... | confirm    = mkForm submitted (name fs) (email fs)
... | submitted  = fs  -- no-op after submit

formAgent : Agent FormState String String
formAgent = mkAgent initForm formObserve formStep

------------------------------------------------------------------------
-- Pipeline approach: each step is a separate Agent
------------------------------------------------------------------------

-- Step 1: receive name, store it
nameAgent : Agent String String String
nameAgent = mkAgent "" (const "Enter name:") (λ _ input → input)

-- Step 2: receive email, store it
emailAgent : Agent String String String
emailAgent = mkAgent "" (const "Enter email:") (λ _ input → input)

-- Step 3: produce summary from the two inputs
summaryAgent : Agent (String × String) String String
summaryAgent = mkAgent ("" , "")
  (λ { (n , e) → "Summary: " ++ n ++ " <" ++ e ++ ">" })
  (λ { (_ , e) input → input , e })  -- receives name from pipeline

-- Pipeline: name >>> email >>> summary
formPipeline : Agent (String × (String × (String × String))) String String
formPipeline = nameAgent >>> (emailAgent >>> summaryAgent)

------------------------------------------------------------------------
-- Validation: form protocol as Session
------------------------------------------------------------------------

-- The form follows FormProtocol exactly.
-- We can type-check this by building a SessionAgent:

formSessionAgent : SessionAgent FormProtocol FormState
formSessionAgent = record
  { state   = initForm
  ; observe = λ fs → summaryStr fs , tt
  ; step    = λ fs (n , (e , tt)) → mkForm submitted n e
  }
  where
    summaryStr : FormState → String
    summaryStr fs = name fs ++ " <" ++ email fs ++ ">"

------------------------------------------------------------------------
-- Example: run form through steps
------------------------------------------------------------------------

-- Simulate: enter "Alice", then "alice@example.com", then confirm
step1 : FormState
step1 = formStep initForm "Alice"

step2 : FormState
step2 = formStep step1 "alice@example.com"

step3 : FormState
step3 = formStep step2 "confirm"

-- Verify via observe:
-- formObserve step1 = "Step 2/3: Enter your email (name: Alice)"
-- formObserve step2 = "Step 3/3: Alice <alice@example.com>"
-- formObserve step3 = "Done! Registered: Alice <alice@example.com>"

------------------------------------------------------------------------
-- Multi-form wizard: compose forms sequentially
------------------------------------------------------------------------

-- Two forms in sequence: registration >>> preferences
prefsProtocol : Session
prefsProtocol = recv String (send String done)

-- Full wizard: register then set preferences
wizardProtocol : Session
wizardProtocol = recv String (recv String (send String (recv String (send String done))))
