{-# OPTIONS --without-K --guardedness #-}

-- App: Elm-подобная архитектура с Event-driven подписками
-- App = { init, update, view, events }

module Agdelte.App where

open import Level using (Level)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)

open import Agdelte.Core.Signal hiding (merge; delay)
open import Agdelte.Core.Event
open import Agdelte.Html.Types

------------------------------------------------------------------------
-- App Record: основная структура приложения
------------------------------------------------------------------------

record App (Model Msg : Set) : Set where
  constructor mkApp
  field
    -- Начальное состояние
    init : Model

    -- Обновление состояния по сообщению
    update : Msg → Model → Model

    -- Отображение состояния в HTML
    view : Model → Html Msg

    -- Динамические подписки на события (зависят от модели)
    events : Model → Event Msg

open App public

------------------------------------------------------------------------
-- Простое приложение без внешних событий
------------------------------------------------------------------------

-- Создать приложение только с view-событиями (клики и т.п.)
simpleApp : ∀ {Model Msg : Set}
          → Model
          → (Msg → Model → Model)
          → (Model → Html Msg)
          → App Model Msg
simpleApp i u v = mkApp i u v (const never)

------------------------------------------------------------------------
-- Композиция приложений
------------------------------------------------------------------------

-- Параллельная композиция: оба приложения работают одновременно
-- Модель — пара, сообщение — сумма
_∥_ : ∀ {M₁ M₂ A₁ A₂ : Set}
    → App M₁ A₁ → App M₂ A₂
    → App (M₁ × M₂) (A₁ ⊎ A₂)
app₁ ∥ app₂ = mkApp
  -- init
  (init app₁ , init app₂)
  -- update
  (λ { (inj₁ msg) (m₁ , m₂) → update app₁ msg m₁ , m₂
     ; (inj₂ msg) (m₁ , m₂) → m₁ , update app₂ msg m₂ })
  -- view (показываем оба)
  (λ { (m₁ , m₂) → node "div" []
       ( mapHtml inj₁ (view app₁ m₁)
       ∷ mapHtml inj₂ (view app₂ m₂)
       ∷ [] ) })
  -- events (объединяем)
  (λ { (m₁ , m₂) → merge
       (mapE inj₁ (events app₁ m₁))
       (mapE inj₂ (events app₂ m₂)) })

infixr 5 _∥_

-- Альтернативная композиция: только одно приложение активно
_⊕ᵃ_ : ∀ {M₁ M₂ A₁ A₂ : Set}
     → App M₁ A₁ → App M₂ A₂
     → App (M₁ ⊎ M₂) (A₁ ⊎ A₂)
app₁ ⊕ᵃ app₂ = mkApp
  -- init (начинаем с первого)
  (inj₁ (init app₁))
  -- update
  (λ { (inj₁ msg) (inj₁ m₁) → inj₁ (update app₁ msg m₁)
     ; (inj₂ msg) (inj₂ m₂) → inj₂ (update app₂ msg m₂)
     ; _ m → m })  -- Игнорируем несовпадающие сообщения
  -- view
  (λ { (inj₁ m₁) → mapHtml inj₁ (view app₁ m₁)
     ; (inj₂ m₂) → mapHtml inj₂ (view app₂ m₂) })
  -- events
  (λ { (inj₁ m₁) → mapE inj₁ (events app₁ m₁)
     ; (inj₂ m₂) → mapE inj₂ (events app₂ m₂) })

infixr 4 _⊕ᵃ_

------------------------------------------------------------------------
-- Трансформации приложения
------------------------------------------------------------------------

-- Изменить тип сообщения
mapMsg : ∀ {Model Msg₁ Msg₂ : Set}
       → (Msg₂ → Msg₁)  -- Преобразование входящих
       → (Msg₁ → Msg₂)  -- Преобразование исходящих (для events)
       → App Model Msg₁
       → App Model Msg₂
mapMsg from to app = mkApp
  (init app)
  (λ msg → update app (from msg))
  (λ m → mapHtml to (view app m))
  (λ m → mapE to (events app m))

-- Изменить модель (линза)
mapModel : ∀ {Model₁ Model₂ Msg : Set}
         → (Model₂ → Model₁)        -- get
         → (Model₁ → Model₂ → Model₂)  -- set
         → Model₂                    -- initial outer
         → App Model₁ Msg
         → App Model₂ Msg
mapModel get set initial app = mkApp
  initial
  (λ msg m₂ → set (update app msg (get m₂)) m₂)
  (λ m₂ → view app (get m₂))
  (λ m₂ → events app (get m₂))

------------------------------------------------------------------------
-- Добавление функциональности
------------------------------------------------------------------------

-- Добавить внешние события к приложению
withEvents : ∀ {Model Msg : Set}
           → (Model → Event Msg)
           → App Model Msg
           → App Model Msg
withEvents extraEvents app = mkApp
  (init app)
  (update app)
  (view app)
  (λ m → merge (events app m) (extraEvents m))

-- Добавить middleware (перехват сообщений)
withMiddleware : ∀ {Model Msg : Set}
               → (Msg → Model → Maybe Msg)
               → App Model Msg
               → App Model Msg
withMiddleware middleware app = mkApp
  (init app)
  (λ msg m → maybe (λ msg' → update app msg' m) m (middleware msg m))
  (view app)
  (events app)
  where open import Data.Maybe using (maybe)

-- Добавить логирование (для отладки)
withLogging : ∀ {Model Msg : Set}
            → (Msg → Model → Model → Model)  -- before → after → logged
            → App Model Msg
            → App Model Msg
withLogging logger app = mkApp
  (init app)
  (λ msg m →
    let m' = update app msg m
    in logger msg m m')
  (view app)
  (events app)

------------------------------------------------------------------------
-- Batch updates
------------------------------------------------------------------------

-- Применить список сообщений
batchUpdate : ∀ {Model Msg : Set}
            → App Model Msg
            → List Msg
            → Model
            → Model
batchUpdate app [] m = m
batchUpdate app (msg ∷ msgs) m = batchUpdate app msgs (update app msg m)

------------------------------------------------------------------------
-- Связь с полиномами
------------------------------------------------------------------------

-- App как коалгебра полинома Html × Event
-- Позиция = Html Msg (что показываем)
-- Направление = Msg (что принимаем)

-- appToPoly : App Model Msg → Poly
-- appToPoly app = mkPoly (Html Msg) (const Msg)

-- appToCoalg : App Model Msg → Coalg (appToPoly app)
-- appToCoalg app = mkCoalg Model (view app) (flip (update app))

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Получить текущий view
currentView : ∀ {Model Msg : Set} → App Model Msg → Html Msg
currentView app = view app (init app)

-- Симуляция одного шага
step : ∀ {Model Msg : Set} → Msg → App Model Msg → App Model Msg
step msg app = mkApp
  (update app msg (init app))
  (update app)
  (view app)
  (events app)

-- Симуляция нескольких шагов
steps : ∀ {Model Msg : Set} → List Msg → App Model Msg → App Model Msg
steps [] app = app
steps (msg ∷ msgs) app = steps msgs (step msg app)
