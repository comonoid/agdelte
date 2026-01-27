{-# OPTIONS --without-K --guardedness #-}

-- PolyApp: связь между App и Polynomial Functors
-- Демонстрирует, что App Model Msg ≅ Coalg (AppPoly Msg)

module Agdelte.Core.PolyApp where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)

open import Agdelte.Core.Poly
open import Agdelte.Core.Signal hiding (merge; delay)
open import Agdelte.Core.Event
open import Agdelte.Html.Types
open import Agdelte.App

------------------------------------------------------------------------
-- App как коалгебра полинома
------------------------------------------------------------------------

-- Полином для UI-компонента:
-- Pos = Html Msg (что отображаем)
-- Dir = λ _ → Msg (все позиции принимают одинаковые сообщения)
--
-- Интерпретация: ⟦AppPoly Msg⟧ X = Σ (Html Msg) (λ _ → Msg → X) ≅ Html Msg × (Msg → X)
-- Это в точности интерфейс "показать UI и принять сообщение"
AppPoly : Set → Poly
AppPoly Msg = Mono (Html Msg) Msg

------------------------------------------------------------------------
-- Преобразование App в Coalg
------------------------------------------------------------------------

-- App Model Msg соответствует коалгебре AppPoly Msg с State = Model
-- view   соответствует observe
-- update соответствует update (с flip)
appToCoalg : ∀ {Model Msg : Set} → App Model Msg → Coalg (AppPoly Msg)
appToCoalg {Model} app = mkCoalg
  Model                            -- State
  (view app)                       -- observe : Model → Html Msg
  (λ m msg → update app msg m)     -- update  : Model → Msg → Model

------------------------------------------------------------------------
-- Параллельная композиция через Poly
------------------------------------------------------------------------

-- App._∥_ соответствует Poly.parallel
-- AppPoly A₁ ⊗ AppPoly A₂ ≅ AppPoly (A₁ ⊎ A₂) с Pos = Html A₁ × Html A₂
--
-- Однако есть тонкость: в App._∥_ мы используем mapHtml для перевода
-- типов сообщений, что не напрямую соответствует ⊗.
-- Это связь "по духу", а не точный изоморфизм.

-- Полином для параллельной композиции:
ParallelPoly : Set → Set → Poly
ParallelPoly Msg₁ Msg₂ = AppPoly Msg₁ ⊗ AppPoly Msg₂

-- Коалгебра параллельной композиции
parallelCoalg : ∀ {Model₁ Model₂ Msg₁ Msg₂ : Set}
              → App Model₁ Msg₁ → App Model₂ Msg₂ → Coalg (ParallelPoly Msg₁ Msg₂)
parallelCoalg app₁ app₂ = parallel (appToCoalg app₁) (appToCoalg app₂)

------------------------------------------------------------------------
-- Альтернативная композиция через Poly
------------------------------------------------------------------------

-- App._⊕ᵃ_ соответствует Poly.choice
-- AppPoly A₁ ⊕ AppPoly A₂ = mkPoly (Html A₁ ⊎ Html A₂) ...

-- Полином для альтернативной композиции:
ChoicePoly : Set → Set → Poly
ChoicePoly Msg₁ Msg₂ = AppPoly Msg₁ ⊕ AppPoly Msg₂

-- Коалгебра альтернативной композиции
choiceCoalg : ∀ {Model₁ Model₂ Msg₁ Msg₂ : Set}
            → App Model₁ Msg₁ → App Model₂ Msg₂ → Coalg (ChoicePoly Msg₁ Msg₂)
choiceCoalg app₁ app₂ = choice (appToCoalg app₁) (appToCoalg app₂)

------------------------------------------------------------------------
-- mapMsg через Lens
------------------------------------------------------------------------

-- mapMsg : (Msg₂ → Msg₁) → (Msg₁ → Msg₂) → App Model Msg₁ → App Model Msg₂
-- соответствует применению линзы к полиному

-- Линза между AppPoly Msg₁ и AppPoly Msg₂
-- Изоморфизм сообщений индуцирует изоморфизм полиномов
msgLens : ∀ {Msg₁ Msg₂ : Set} → (Msg₁ → Msg₂) → (Msg₂ → Msg₁) → Lens (AppPoly Msg₁) (AppPoly Msg₂)
msgLens to from = mkLens
  (mapHtml to)      -- onPos : Html Msg₁ → Html Msg₂
  (λ _ → from)      -- onDir : Msg₂ → Msg₁

-- Применение линзы к коалгебре App
transformApp : ∀ {Msg₁ Msg₂ : Set} → (Msg₁ → Msg₂) → (Msg₂ → Msg₁) → Coalg (AppPoly Msg₁) → Coalg (AppPoly Msg₂)
transformApp to from = transformCoalg (msgLens to from)

------------------------------------------------------------------------
-- Семантика App через Signal
------------------------------------------------------------------------

-- Запуск приложения производит Signal (Html Msg)
-- Это соответствует разворачиванию коалгебры в бесконечный поток

-- Простой случай: без внешних событий, фиксированная последовательность Msg
runWithMsgs : ∀ {Model Msg : Set} → App Model Msg → Signal Msg → Signal (Html Msg)
now  (runWithMsgs app msgs) = view app (init app)
next (runWithMsgs app msgs) = runWithMsgs (step (now msgs) app) (next msgs)

------------------------------------------------------------------------
-- Wiring: соединение App с внешним миром
------------------------------------------------------------------------

-- App можно рассматривать как "провод" (wire) в терминах Poly:
-- Он принимает Msg на входе и выдаёт Html Msg на выходе
-- Wiring diagram показывает, как App соединяется с:
-- 1. DOM (источник событий → Msg)
-- 2. Renderer (Html Msg → побочные эффекты)
-- 3. Subscriptions (внешние события → Event Msg)

-- Полный полином для App с подписками:
-- Pos = Html Msg × Event Msg (что выдаём: UI + подписки)
-- Dir = λ _ → Msg (принимаем сообщения)
AppWithEventsPoly : Set → Poly
AppWithEventsPoly Msg = Mono (Html Msg × Event Msg) Msg

-- Коалгебра для полного App
appWithEventsToCoalg : ∀ {Model Msg : Set} → App Model Msg → Coalg (AppWithEventsPoly Msg)
appWithEventsToCoalg {Model} app = mkCoalg
  Model
  (λ m → view app m , events app m)
  (λ m msg → update app msg m)

------------------------------------------------------------------------
-- Связь с теорией: App как динамическая система
------------------------------------------------------------------------

-- В терминологии polynomial functors:
-- - App — это Moore machine (конечный автомат с выходом)
-- - Состояние: Model
-- - Вход: Msg
-- - Выход: Html Msg (+ Event Msg для подписок)
-- - Переход: update : Msg → Model → Model
-- - Наблюдение: view : Model → Html Msg
--
-- Moore machine = Coalg (Mono Output Input)
-- где Output = Html Msg, Input = Msg
--
-- Это ключевое соответствие, делающее Elm/TEA архитектуру
-- экземпляром теории polynomial functors.
