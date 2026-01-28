{-# OPTIONS --without-K #-}

-- App: Elm-подобная архитектура с Event-driven подписками и командами
-- App = { init, update, view, subs, command }

module Agdelte.App where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Html.Types

------------------------------------------------------------------------
-- App Record: основная структура приложения
------------------------------------------------------------------------

record App (Model Msg : Set) : Set where
  field
    -- Начальное состояние
    init : Model

    -- Обновление состояния по сообщению
    update : Msg → Model → Model

    -- Отображение состояния в HTML
    view : Model → Html Msg

    -- Динамические подписки на события (зависят от модели)
    subs : Model → Event Msg

    -- Команды (побочные эффекты) — вызываются после update
    command : Msg → Model → Cmd Msg

open App public

------------------------------------------------------------------------
-- Конструкторы App
------------------------------------------------------------------------

-- Простое приложение (без команд) — для Counter, Timer, etc.
mkApp : ∀ {Model Msg : Set}
      → Model
      → (Msg → Model → Model)
      → (Model → Html Msg)
      → (Model → Event Msg)
      → App Model Msg
mkApp i u v s = record
  { init = i
  ; update = u
  ; view = v
  ; subs = s
  ; command = λ _ _ → ε  -- нет команд
  }

-- Приложение с командами — для HTTP и других эффектов
mkCmdApp : ∀ {Model Msg : Set}
         → Model
         → (Msg → Model → Model)
         → (Model → Html Msg)
         → (Model → Event Msg)
         → (Msg → Model → Cmd Msg)
         → App Model Msg
mkCmdApp i u v s c = record
  { init = i
  ; update = u
  ; view = v
  ; subs = s
  ; command = c
  }

-- Для обратной совместимости: events = subs
events : ∀ {Model Msg : Set} → App Model Msg → Model → Event Msg
events = subs

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
app₁ ∥ app₂ = mkCmdApp
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
  -- subs (объединяем)
  (λ { (m₁ , m₂) → merge
       (mapE inj₁ (subs app₁ m₁))
       (mapE inj₂ (subs app₂ m₂)) })
  -- command
  (λ { (inj₁ msg) (m₁ , _) → mapCmd inj₁ (command app₁ msg m₁)
     ; (inj₂ msg) (_ , m₂) → mapCmd inj₂ (command app₂ msg m₂) })

infixr 5 _∥_

-- Альтернативная композиция: только одно приложение активно
_⊕ᵃ_ : ∀ {M₁ M₂ A₁ A₂ : Set}
     → App M₁ A₁ → App M₂ A₂
     → App (M₁ ⊎ M₂) (A₁ ⊎ A₂)
app₁ ⊕ᵃ app₂ = mkCmdApp
  -- init (начинаем с первого)
  (inj₁ (init app₁))
  -- update
  (λ { (inj₁ msg) (inj₁ m₁) → inj₁ (update app₁ msg m₁)
     ; (inj₂ msg) (inj₂ m₂) → inj₂ (update app₂ msg m₂)
     ; _ m → m })  -- Игнорируем несовпадающие сообщения
  -- view
  (λ { (inj₁ m₁) → mapHtml inj₁ (view app₁ m₁)
     ; (inj₂ m₂) → mapHtml inj₂ (view app₂ m₂) })
  -- subs
  (λ { (inj₁ m₁) → mapE inj₁ (subs app₁ m₁)
     ; (inj₂ m₂) → mapE inj₂ (subs app₂ m₂) })
  -- command
  (λ { (inj₁ msg) (inj₁ m₁) → mapCmd inj₁ (command app₁ msg m₁)
     ; (inj₂ msg) (inj₂ m₂) → mapCmd inj₂ (command app₂ msg m₂)
     ; _ _ → ε })

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
mapMsg from to app = mkCmdApp
  (init app)
  (λ msg → update app (from msg))
  (λ m → mapHtml to (view app m))
  (λ m → mapE to (subs app m))
  (λ msg m → mapCmd to (command app (from msg) m))

-- Изменить модель (линза)
mapModel : ∀ {Model₁ Model₂ Msg : Set}
         → (Model₂ → Model₁)        -- get
         → (Model₁ → Model₂ → Model₂)  -- set
         → Model₂                    -- initial outer
         → App Model₁ Msg
         → App Model₂ Msg
mapModel get set initial app = mkCmdApp
  initial
  (λ msg m₂ → set (update app msg (get m₂)) m₂)
  (λ m₂ → view app (get m₂))
  (λ m₂ → subs app (get m₂))
  (λ msg m₂ → command app msg (get m₂))

------------------------------------------------------------------------
-- Добавление функциональности
------------------------------------------------------------------------

-- Заменить view (для кастомизации отображения)
withView : ∀ {Model Msg : Set}
         → (Model → Html Msg)
         → App Model Msg
         → App Model Msg
withView v app = mkCmdApp
  (init app)
  (update app)
  v
  (subs app)
  (command app)

-- Заменить update
withUpdate : ∀ {Model Msg : Set}
           → (Msg → Model → Model)
           → App Model Msg
           → App Model Msg
withUpdate u app = mkCmdApp
  (init app)
  u
  (view app)
  (subs app)
  (command app)

-- Заменить subs
withSubs : ∀ {Model Msg : Set}
         → (Model → Event Msg)
         → App Model Msg
         → App Model Msg
withSubs s app = mkCmdApp
  (init app)
  (update app)
  (view app)
  s
  (command app)

-- Добавить внешние события к приложению (merge)
withEvents : ∀ {Model Msg : Set}
           → (Model → Event Msg)
           → App Model Msg
           → App Model Msg
withEvents extraEvents app = mkCmdApp
  (init app)
  (update app)
  (view app)
  (λ m → merge (subs app m) (extraEvents m))
  (command app)

-- Добавить команды к приложению (merge)
withCommand : ∀ {Model Msg : Set}
            → (Msg → Model → Cmd Msg)
            → App Model Msg
            → App Model Msg
withCommand cmd app = mkCmdApp
  (init app)
  (update app)
  (view app)
  (subs app)
  (λ msg m → command app msg m <> cmd msg m)

-- Добавить middleware (перехват сообщений)
withMiddleware : ∀ {Model Msg : Set}
               → (Msg → Model → Maybe Msg)
               → App Model Msg
               → App Model Msg
withMiddleware middleware app = mkCmdApp
  (init app)
  (λ msg m → maybe (λ msg' → update app msg' m) m (middleware msg m))
  (view app)
  (subs app)
  (λ msg m → maybe (λ msg' → command app msg' m) ε (middleware msg m))
  where open import Data.Maybe using (maybe)

-- Добавить логирование (для отладки)
withLogging : ∀ {Model Msg : Set}
            → (Msg → Model → Model → Model)  -- before → after → logged
            → App Model Msg
            → App Model Msg
withLogging logger app = mkCmdApp
  (init app)
  (λ msg m →
    let m' = update app msg m
    in logger msg m m')
  (view app)
  (subs app)
  (command app)

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
-- Связь с полиномами (см. Agdelte.Theory.PolyApp для деталей)
------------------------------------------------------------------------

-- App Model Msg — это коалгебра полинома AppPoly Msg = Mono (Html Msg) Msg
--
-- Ключевое соответствие:
--   App.init   → начальное состояние коалгебры
--   App.view   → Coalg.observe : State → Pos
--   App.update → Coalg.update  : State → Dir → State
--
-- Операции на App соответствуют wiring diagrams на коалгебрах:
--   _∥_  ↔ Poly.parallel : Coalg P → Coalg Q → Coalg (P ⊗ Q)
--   _⊕ᵃ_ ↔ Poly.choice   : Coalg P → Coalg Q → Coalg (P ⊕ Q)
--   mapMsg ↔ Poly.transformCoalg : Lens P Q → Coalg P → Coalg Q
--
-- Это делает App экземпляром Moore machine в терминах polynomial functors:
--   Moore machine = ν X. Output × (Input → X) = Coalg (Mono Output Input)

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Получить текущий view
currentView : ∀ {Model Msg : Set} → App Model Msg → Html Msg
currentView app = view app (init app)

-- Симуляция одного шага
step : ∀ {Model Msg : Set} → Msg → App Model Msg → App Model Msg
step msg app = mkCmdApp
  (update app msg (init app))
  (update app)
  (view app)
  (subs app)
  (command app)

-- Симуляция нескольких шагов
steps : ∀ {Model Msg : Set} → List Msg → App Model Msg → App Model Msg
steps [] app = app
steps (msg ∷ msgs) app = steps msgs (step msg app)

------------------------------------------------------------------------
-- Wiring diagram aliases (для совместимости с Poly терминологией)
------------------------------------------------------------------------

-- Параллельное соединение (tensor product)
tensor : ∀ {M₁ M₂ A₁ A₂ : Set} → App M₁ A₁ → App M₂ A₂ → App (M₁ × M₂) (A₁ ⊎ A₂)
tensor = _∥_

-- Выбор (coproduct)
coproduct : ∀ {M₁ M₂ A₁ A₂ : Set} → App M₁ A₁ → App M₂ A₂ → App (M₁ ⊎ M₂) (A₁ ⊎ A₂)
coproduct = _⊕ᵃ_
