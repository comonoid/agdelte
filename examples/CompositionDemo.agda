{-# OPTIONS --without-K #-}

-- CompositionDemo: демонстрация композиции приложений
-- Два независимых Counter работают параллельно через _∥_

module CompositionDemo where

open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
import Agdelte.App as App
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events

------------------------------------------------------------------------
-- Counter App (переиспользуемый компонент)
------------------------------------------------------------------------

module CounterApp where
  -- Model
  record Model : Set where
    constructor mkModel
    field
      count     : ℕ
      counterName : String

  open Model public

  -- Messages
  data Msg : Set where
    Inc   : Msg
    Dec   : Msg
    Reset : Msg

  -- Update
  update : Msg → Model → Model
  update Inc m = record m { count = suc (count m) }
  update Dec m = record m { count = pred (count m) }
  update Reset m = record m { count = zero }

  -- View
  view : Model → Html Msg
  view m = div (class "counter-component" ∷ [])
    ( h3 [] (text (counterName m) ∷ [])
    ∷ div (class "counter-controls" ∷ [])
        ( button (onClick Dec ∷ class "btn" ∷ []) (text "-" ∷ [])
        ∷ span (class "count" ∷ []) (text (show (count m)) ∷ [])
        ∷ button (onClick Inc ∷ class "btn" ∷ []) (text "+" ∷ [])
        ∷ button (onClick Reset ∷ class "reset-btn" ∷ []) (text "Reset" ∷ [])
        ∷ [])
    ∷ [])

  -- App
  mkCounter : String → ℕ → App.App Model Msg
  mkCounter n initial = App.mkApp
    (mkModel initial n)
    update
    view
    (const never)

------------------------------------------------------------------------
-- Composed App: Two Counters
------------------------------------------------------------------------

open CounterApp using () renaming
  ( Model to CounterModel
  ; Msg to CounterMsg
  ; mkCounter to mkCounter
  )

-- Два независимых счётчика
counter1 : App.App CounterModel CounterMsg
counter1 = mkCounter "Left Counter" 0

counter2 : App.App CounterModel CounterMsg
counter2 = mkCounter "Right Counter" 10

-- Композиция через _∥_
-- Результат: App (Model × Model) (Msg ⊎ Msg)
twoCounters : App.App (CounterModel × CounterModel) (CounterMsg ⊎ CounterMsg)
twoCounters = counter1 App.∥ counter2

------------------------------------------------------------------------
-- Wrapper App (добавляет заголовок и статистику)
------------------------------------------------------------------------

-- Используем composed app напрямую, но добавим обёртку для лучшего UI

Model : Set
Model = CounterModel × CounterModel

Msg : Set
Msg = CounterMsg ⊎ CounterMsg

totalCount : Model → ℕ
totalCount (m₁ , m₂) = CounterApp.count m₁ Data.Nat.+ CounterApp.count m₂
  where open import Data.Nat using (_+_)

-- Кастомный view с заголовком
customView : Model → Html Msg
customView m@(m₁ , m₂) = div (class "composition-demo" ∷ [])
  ( h1 [] (text "Composition Demo" ∷ [])
  ∷ p (class "description" ∷ [])
      (text "Two independent counters composed with _∥_" ∷ [])
  ∷ p (class "total" ∷ [])
      (text ("Total: " ++ show (totalCount m)) ∷ [])
  ∷ div (class "counters-container" ∷ [])
      ( mapHtml inj₁ (CounterApp.view m₁)
      ∷ mapHtml inj₂ (CounterApp.view m₂)
      ∷ [])
  ∷ [])

-- Финальное приложение: twoCounters с кастомным view
app : App.App Model Msg
app = App.withView customView twoCounters
