{-# OPTIONS --without-K --guardedness #-}

-- PolyApp: connection between App and Polynomial Functors
-- Demonstrates that App Model Msg ≅ Coalg (AppPoly Msg)

module Agdelte.Theory.PolyApp where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)

open import Agdelte.Theory.Poly as P
open import Agdelte.Core.Signal hiding (merge; delay)
open import Agdelte.Core.Event
open import Agdelte.Html.Types
open import Agdelte.App

------------------------------------------------------------------------
-- App as polynomial coalgebra
------------------------------------------------------------------------

-- Polynomial for UI component:
-- Pos = Html Msg (what we display)
-- Dir = λ _ → Msg (all positions accept the same messages)
--
-- Interpretation: ⟦AppPoly Msg⟧ X = Σ (Html Msg) (λ _ → Msg → X) ≅ Html Msg × (Msg → X)
-- This is exactly the interface "display UI and accept a message"
AppPoly : Set → Poly
AppPoly Msg = Mono (Html Msg) Msg

------------------------------------------------------------------------
-- Convert App to Coalg
------------------------------------------------------------------------

-- App Model Msg corresponds to coalgebra AppPoly Msg with State = Model
-- view   corresponds to observe
-- update corresponds to update (with flip)
appToCoalg : ∀ {Model Msg : Set} → App Model Msg → Coalg (AppPoly Msg)
appToCoalg {Model} app = mkCoalg
  Model                            -- State
  (view app)                       -- observe : Model → Html Msg
  (λ m msg → update app msg m)     -- update  : Model → Msg → Model

------------------------------------------------------------------------
-- Parallel composition via Poly
------------------------------------------------------------------------

-- App._∥_ corresponds to Poly.parallel
-- AppPoly A₁ ⊗ AppPoly A₂ ≅ AppPoly (A₁ ⊎ A₂) with Pos = Html A₁ × Html A₂
--
-- However there is a subtlety: in App._∥_ we use mapHtml to translate
-- message types, which does not directly correspond to ⊗.
-- This is a connection "in spirit", not an exact isomorphism.

-- Polynomial for parallel composition:
ParallelPoly : Set → Set → Poly
ParallelPoly Msg₁ Msg₂ = AppPoly Msg₁ ⊗ AppPoly Msg₂

-- Coalgebra of parallel composition
parallelCoalg : ∀ {Model₁ Model₂ Msg₁ Msg₂ : Set}
              → App Model₁ Msg₁ → App Model₂ Msg₂ → Coalg (ParallelPoly Msg₁ Msg₂)
parallelCoalg app₁ app₂ = P.parallel (appToCoalg app₁) (appToCoalg app₂)

------------------------------------------------------------------------
-- Alternative composition via Poly
------------------------------------------------------------------------

-- App._⊕ᵃ_ corresponds to Poly.choice
-- AppPoly A₁ ⊕ AppPoly A₂ = mkPoly (Html A₁ ⊎ Html A₂) ...

-- Polynomial for alternative composition:
ChoicePoly : Set → Set → Poly
ChoicePoly Msg₁ Msg₂ = AppPoly Msg₁ ⊕ AppPoly Msg₂

-- Coalgebra of alternative composition
choiceCoalg : ∀ {Model₁ Model₂ Msg₁ Msg₂ : Set}
            → App Model₁ Msg₁ → App Model₂ Msg₂ → Coalg (ChoicePoly Msg₁ Msg₂)
choiceCoalg app₁ app₂ = P.choice (appToCoalg app₁) (appToCoalg app₂)

------------------------------------------------------------------------
-- mapMsg via Lens
------------------------------------------------------------------------

-- mapMsg : (Msg₂ → Msg₁) → (Msg₁ → Msg₂) → App Model Msg₁ → App Model Msg₂
-- corresponds to applying a lens to the polynomial

-- Lens between AppPoly Msg₁ and AppPoly Msg₂
-- Message isomorphism induces polynomial isomorphism
msgLens : ∀ {Msg₁ Msg₂ : Set} → (Msg₁ → Msg₂) → (Msg₂ → Msg₁) → Lens (AppPoly Msg₁) (AppPoly Msg₂)
msgLens to from = mkLens
  (mapHtml to)      -- onPos : Html Msg₁ → Html Msg₂
  (λ _ → from)      -- onDir : Msg₂ → Msg₁

-- Applying lens to App coalgebra
transformApp : ∀ {Msg₁ Msg₂ : Set} → (Msg₁ → Msg₂) → (Msg₂ → Msg₁) → Coalg (AppPoly Msg₁) → Coalg (AppPoly Msg₂)
transformApp to from = transformCoalg (msgLens to from)

------------------------------------------------------------------------
-- Round-trip proofs: App ↔ Coalg correspondence
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- App has more fields than Coalg (subs, command, init).
-- The correspondence is structural: view ↔ observe, update ↔ update.

-- observe is preserved
app-coalg-observe : ∀ {Model Msg : Set} (app : App Model Msg) (m : Model)
                  → Coalg.observe (appToCoalg app) m ≡ view app m
app-coalg-observe _ _ = refl

-- update is preserved
app-coalg-update : ∀ {Model Msg : Set} (app : App Model Msg) (m : Model) (msg : Msg)
                 → Coalg.update (appToCoalg app) m msg ≡ update app msg m
app-coalg-update _ _ _ = refl

-- parallel composition corresponds
parallel-observe : ∀ {M₁ M₂ Msg₁ Msg₂ : Set}
                 → (a₁ : App M₁ Msg₁) (a₂ : App M₂ Msg₂)
                 → (m₁ : M₁) (m₂ : M₂)
                 → Coalg.observe (parallelCoalg a₁ a₂) (m₁ , m₂)
                   ≡ (view a₁ m₁ , view a₂ m₂)
parallel-observe _ _ _ _ = refl

parallel-update-left : ∀ {M₁ M₂ Msg₁ Msg₂ : Set}
                     → (a₁ : App M₁ Msg₁) (a₂ : App M₂ Msg₂)
                     → (m₁ : M₁) (m₂ : M₂) (msg : Msg₁)
                     → Coalg.update (parallelCoalg a₁ a₂) (m₁ , m₂) (inj₁ msg)
                       ≡ (update a₁ msg m₁ , m₂)
parallel-update-left _ _ _ _ _ = refl

parallel-update-right : ∀ {M₁ M₂ Msg₁ Msg₂ : Set}
                      → (a₁ : App M₁ Msg₁) (a₂ : App M₂ Msg₂)
                      → (m₁ : M₁) (m₂ : M₂) (msg : Msg₂)
                      → Coalg.update (parallelCoalg a₁ a₂) (m₁ , m₂) (inj₂ msg)
                        ≡ (m₁ , update a₂ msg m₂)
parallel-update-right _ _ _ _ _ = refl

-- choice composition corresponds
choice-observe-left : ∀ {M₁ M₂ Msg₁ Msg₂ : Set}
                    → (a₁ : App M₁ Msg₁) (a₂ : App M₂ Msg₂)
                    → (m₁ : M₁)
                    → Coalg.observe (choiceCoalg a₁ a₂) (inj₁ m₁)
                      ≡ inj₁ (view a₁ m₁)
choice-observe-left _ _ _ = refl

choice-observe-right : ∀ {M₁ M₂ Msg₁ Msg₂ : Set}
                     → (a₁ : App M₁ Msg₁) (a₂ : App M₂ Msg₂)
                     → (m₂ : M₂)
                     → Coalg.observe (choiceCoalg a₁ a₂) (inj₂ m₂)
                       ≡ inj₂ (view a₂ m₂)
choice-observe-right _ _ _ = refl

------------------------------------------------------------------------
-- Semantics of App via Signal
------------------------------------------------------------------------

-- Running the application produces Signal (Html Msg)
-- This corresponds to unfolding the coalgebra into an infinite stream

-- Simple case: no external events, fixed sequence of Msg
runWithMsgs : ∀ {Model Msg : Set} → App Model Msg → Signal Msg → Signal (Html Msg)
now  (runWithMsgs app msgs) = view app (init app)
next (runWithMsgs app msgs) = runWithMsgs (step (now msgs) app) (next msgs)

------------------------------------------------------------------------
-- Wiring: connecting App to the external world
------------------------------------------------------------------------

-- App can be viewed as a "wire" in Poly terms:
-- It accepts Msg as input and produces Html Msg as output
-- Wiring diagram shows how App connects to:
-- 1. DOM (event source → Msg)
-- 2. Renderer (Html Msg → side effects)
-- 3. Subscriptions (external events → Event Msg)

-- Full polynomial for App with subscriptions:
-- Pos = Html Msg × Event Msg (what we produce: UI + subscriptions)
-- Dir = λ _ → Msg (accept messages)
AppWithEventsPoly : Set → Poly
AppWithEventsPoly Msg = Mono (Html Msg × Event Msg) Msg

-- Coalgebra for the full App
appWithEventsToCoalg : ∀ {Model Msg : Set} → App Model Msg → Coalg (AppWithEventsPoly Msg)
appWithEventsToCoalg {Model} app = mkCoalg
  Model
  (λ m → view app m , events app m)
  (λ m msg → update app msg m)

-- Full app with events: observe is preserved
appE-coalg-observe : ∀ {Model Msg : Set} (app : App Model Msg) (m : Model)
                   → Coalg.observe (appWithEventsToCoalg app) m ≡ (view app m , events app m)
appE-coalg-observe _ _ = refl

------------------------------------------------------------------------
-- Connection to theory: App as a dynamical system
------------------------------------------------------------------------

-- In polynomial functors terminology:
-- - App is a Moore machine (finite automaton with output)
-- - State: Model
-- - Input: Msg
-- - Output: Html Msg (+ Event Msg for subscriptions)
-- - Transition: update : Msg → Model → Model
-- - Observation: view : Model → Html Msg
--
-- Moore machine = Coalg (Mono Output Input)
-- where Output = Html Msg, Input = Msg
--
-- This is the key correspondence making Elm/TEA architecture
-- an instance of polynomial functors theory.
