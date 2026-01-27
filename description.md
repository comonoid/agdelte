# Agdelte

## Идея

Svelte 5 ввёл Runes — явную реактивность вместо магии компилятора. Правильный шаг, но TypeScript не знает о Runes, это надстройка.

Agdelte — те же идеи в языке с настоящей системой типов. Реактивность через стандартные абстракции. Эффекты явны в типах. Невозможные состояния непредставимы.

---

## Философия: Простота + Гарантии

```
┌───────────────────────────────────────────────────────┐
│  ПОЛЬЗОВАТЕЛЬ: Простые record-определения             │
│  App { init, update, view, events }                   │
│  Понятные сообщения об ошибках                        │
├───────────────────────────────────────────────────────┤
│  БИБЛИОТЕКА: Типизированные комбинаторы              │
│  mapE, merge, _∥_, mapMsg                            │
├───────────────────────────────────────────────────────┤
│  ТЕОРИЯ (Theory/): Poly, Coalg, Lens                 │
│  Изолирована, для доказательств и продвинутых фич    │
└───────────────────────────────────────────────────────┘
```

**Принцип:** Простые определения для эргономики и понятных ошибок. Теория (Polynomial Functors) в отдельном модуле — для формальных гарантий, доказательств, и продвинутых возможностей (wiring diagrams в будущем).

---

## Что видит пользователь

### App — главная абстракция

```agda
record App (Msg : Set) (Model : Set) : Set where
  init   : Model                    -- начальное состояние
  update : Msg → Model → Model      -- чистая функция
  view   : Model → Html Msg         -- чистая функция
  events : Model → Event Msg        -- декларативные подписки
```

### Signal и Event — дискретные потоки

```agda
Signal : Set → Set              -- дискретный поток (одно значение на такт)
Event  : Set → Set              -- дискретные события (список за такт)
Event A = Signal (List A)
```

**Важно:** в Agdelte нет непрерывного времени. Signal — это дискретный поток значений, не функция `Time → A`.

### IO — всё это Event

```agda
interval       : ℕ → Event ⊤              -- тики таймера
animationFrame : Event FrameInfo          -- кадры браузера
keyboard       : Event Key                -- нажатия клавиш
request        : Request → Event Response -- HTTP ответы
websocket      : Url → WebSocket          -- WebSocket канал
```

---

## Примеры

### Счётчик

```agda
data Msg = Inc | Dec

counter : App Msg ℕ
counter = record
  { init   = 0
  ; update = λ { Inc n → suc n ; Dec n → pred n }
  ; view   = λ n → div []
      [ button [ onClick Dec ] [ text "-" ]
      , span [] [ text (show n) ]
      , button [ onClick Inc ] [ text "+" ]
      ]
  ; events = λ _ → never
  }
```

### HTTP запрос

```agda
data Msg = Fetch | GotData Response
data Status = Idle | Loading | Ready Data

app : App Msg Model
app = record
  { init   = { status = Idle }
  ; update = λ where
      Fetch m → record m { status = Loading }
      (GotData r) m → record m { status = Ready (parse r) }
  ; view   = λ m → button [ onClick Fetch ] [ text "Load" ]
  ; events = λ m → case m.status of λ where
      Loading → mapE GotData (request (get "/api"))
      _ → never
  }
```

**Ключевой инсайт:** `events` зависит от `Model`. Когда `status = Loading` — runtime подписывается на HTTP. Ответ пришёл → status изменился → автоматическая отписка. Нет ручного cleanup.

---

## Комбинаторы

```agda
-- Базовые
never     : Event A                           -- пустой поток
merge     : Event A → Event A → Event A       -- объединить
mapE      : (A → B) → Event A → Event B       -- преобразовать
filterE   : (A → Bool) → Event A → Event A    -- отфильтровать

-- Sampling
snapshot  : (A → B → C) → Event A → Signal B → Event C
gate      : Event A → Signal Bool → Event A
changes   : Signal A → Event A

-- Временные
debounce  : ℕ → Event A → Event A
throttle  : ℕ → Event A → Event A

-- Композиция приложений
_∥_       : App Msg₁ Model₁ → App Msg₂ Model₂ → App (Msg₁ ⊎ Msg₂) (Model₁ × Model₂)
```

---

## Теоретическое обоснование (Theory/)

Модуль `Theory/` содержит формализацию на основе **Polynomial Functors** (Spivak, Niu):

```agda
-- Poly: интерфейс взаимодействия
record Poly : Set₁ where
  Pos : Set              -- что система выдаёт
  Dir : Pos → Set        -- что принимает

-- Coalg: система с состоянием
record Coalg (p : Poly) : Set₁ where
  State : Set
  observe : State → p.Pos
  update  : (s : State) → p.Dir (observe s) → State

-- Доказывается соответствие:
-- Signal A ≅ Coalg (Mono A ⊤)
-- App M Msg ≅ Coalg (AppPoly Msg) + init + events
```

**Текущий статус:**
- Core определения (Signal, Event, App) — простые records для эргономики
- Theory/ — формализация соответствия с Poly
- Phase 2+: комбинаторы будут использовать Poly внутри (гарантии "by construction")
- Phase 3+: Wiring diagrams для сложных композиций

Пользователю это знать не нужно — но теория даёт путь к формальной верификации.

---

## Runtime

```
1. model := init
2. html := view(model)
3. Рендер, установить DOM обработчики
4. Подписаться на events(model)
5. Ждать событие
6. model := update(msg, model)
7. Обновить подписки (diff events)
8. goto 2
```

Event появился в `events(model)` → подписка. Исчез → отписка. Автоматически.

---

## Ключевые свойства

| Свойство | Описание |
|----------|----------|
| **Унификация** | Таймеры, HTTP, WebSocket — всё Event |
| **Чистота** | update и view — чистые функции |
| **Декларативность** | events описывает *что*, не *как* |
| **Автоматический cleanup** | Нет утечек ресурсов |
| **Композиция** | Приложения комбинируются как значения |

---

## Что получаем бесплатно

| Возможность | Почему просто |
|-------------|---------------|
| Time-travel debugging | Model — это данные |
| Undo/Redo | Список предыдущих Model |
| Сериализация | JSON.stringify(model) |
| Тестирование | update msg model ≡ expected |
| Отмена запросов | Автоматически при отписке |
| Race conditions | Невозможны по построению |

---

## Сравнение

| | Svelte 5 | Elm | Agdelte |
|--|----------|-----|---------|
| Реактивность | Магия компилятора | Архитектура | Elm-like + Poly теория |
| Типы | TypeScript | ML | Зависимые типы |
| Эффекты | Скрыты в $effect | Cmd (непрозрачен) | Event (явно) |
| Композиция | Компоненты | Boilerplate | `_∥_`, `mapMsg` (Poly внутри) |
| Сообщения об ошибках | Хорошие | Хорошие | Хорошие (простые типы) |
| Доказательства | Нет | Нет | Возможны (через Theory/) |

---

## Roadmap

**Phase 1: MVP** ✅ — простота и работающие примеры

- Signal, Event — простые coinductive records
- App — Elm-like record { init, update, view, events }
- Html — типизированные элементы и атрибуты
- Примитивы: interval, animationFrame
- Runtime: event loop, VDOM patching
- Примеры: Counter, Timer, Todo

**Phase 2: Расширения + Poly внутри**

IO примитивы:
- request (HTTP), websocket, keyboard, mouse
- localStorage, routing

Комбинаторы:
- filterE, merge, snapshot, debounce, throttle
- Линзы для вложенных моделей

Интеграция Poly:
- `_∥_` реализован через `Poly.parallel` (гарантии by construction)
- `mapMsg` реализован через `Poly.transformCoalg`
- API остаётся простым, Poly работает внутри

**Phase 3: Wiring Diagrams**

- Сети компонентов с явными связями
- Декларативное описание потоков данных
- Для сложных enterprise-приложений

**Phase 4: Продвинутое**

- Конкурентность (worker, parallel, race)
- Формальная верификация
- Session types, Linear types

> Подробнее: [architecture/](architecture/)

---

## Заключение

```
Пользователь пишет:     app = mkApp init update view events
Пользователь видит:     Простые типы, понятные ошибки
Внутри работает:        Poly гарантирует корректность (Phase 2+)
Для продвинутых:        Theory/, wiring diagrams (Phase 3+)
```

**Простота использования. Гарантии по построению. Путь к формальной верификации.**
