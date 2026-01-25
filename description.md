# Agdelte

## Идея

Svelte 5 ввёл Runes — явную реактивность вместо магии компилятора. Правильный шаг, но TypeScript не знает о Runes, это надстройка.

Agdelte — те же идеи в языке с настоящей системой типов. Реактивность через стандартные абстракции: Functor, Applicative, потоки.

---

## Два типа

### Signal — значения во времени

```agda
record Signal (A : Set) : Set where
  coinductive              -- бесконечная структура
  field
    now  : A               -- текущее значение
    next : Signal A        -- продолжение (следующий такт)
```

Signal — бесконечный поток значений. Не "переменная", а последовательность: значение сейчас (`now`) и значение потом (`next`).

**Такт** — одна итерация: событие пришло → update → render. Между тактами система ждёт.

### Event — события извне

```agda
Event A = Signal (List A)
```

Event — поток списков. За один такт: 0, 1 или несколько событий.

```agda
never : Event A           -- событие, которое никогда не происходит
never = pure []           -- каждый такт — пустой список
```

---

## Всё IO — это Event

Любое взаимодействие с внешним миром — события, которые приходят в систему:

```agda
interval  : ℕ → Event ⊤              -- тики таймера
keyboard  : Event Key                -- нажатия клавиш
request   : Request → Event Response -- HTTP ответы
websocket : Url → WebSocket          -- WebSocket канал (recv + send)
```

WebSocket — двунаправленный канал:
```agda
record WebSocket : Set where
  recv : Event WsEvent       -- входящие события
  send : String → Event ⊤    -- отправить сообщение
```

HTTP запрос — не команда, а источник событий. Запрос выполняется когда runtime подписывается на Event.

---

## App

```agda
record App (Msg : Set) (Model : Set) : Set where
  init   : Model
  update : Msg → Model → Model
  view   : Model → Html Msg
  events : Model → Event Msg
```

- `init` — начальное состояние
- `update` — чистая функция, без эффектов
- `view` — чистая функция
- `events` — какие внешние события слушать (зависит от Model)

DOM events из `view` добавляются автоматически.

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

### Часы

```agda
data Msg = Tick

clock : App Msg ℕ
clock = record
  { init   = 0
  ; update = λ { Tick n → suc n }
  ; view   = λ n → text (show n)
  ; events = λ _ → map (const Tick) (interval 1000)  -- const Tick _ = Tick
  }
```

### Fetch по клику

```agda
data Msg = FetchData | GotData Response

fetch : App Msg Model
fetch = record
  { init   = { loading = false; data = Nothing }
  ; update = λ where
      FetchData m → record m { loading = true }
      (GotData d) m → record m { loading = false; data = Just d }
  ; view   = λ m → button [ onClick FetchData ] [ text "Load" ]
  ; events = λ m →
      if m.loading
      then map GotData (request (get "/api"))
      else never
  }
```

Когда `loading = true`, runtime подписывается на `request` → HTTP запрос уходит → ответ приходит как `GotData`.

---

## Push-FRP

**Push** означает: события "проталкиваются" извне в приложение. Приложение не опрашивает источники — оно реагирует на входящие события.

```
Внешний мир
    │
    ├── interval ────► тики
    ├── keyboard ────► клавиши
    ├── request ─────► HTTP ответы
    ├── websocket ───► сообщения
    │
    ▼
  Event Msg
    │
    ▼
  update (чистая)
    │
    ▼
  Model
    │
    ▼
  view (чистая)
    │
    ▼
  Html ──► DOM events ──┐
                        │
    events(Model) ◄─────┘
```

Всё взаимодействие с миром — входящие события. Внутри — чистые функции.

---

## Runtime

```
1. model := init
2. html := view(model)
3. Рендер, установить DOM обработчики
4. Подписаться на events(model)
5. Ждать событие (DOM, interval, request, ...)
6. model := update(msg, model)
7. Обновить подписки (diff events)
8. goto 2
```

Runtime управляет подписками декларативно: Event появился в `events(model)` → подписка, исчез → отписка.

---

## Ключевые свойства

**Унификация.** Таймеры, HTTP, WebSocket — всё Event. Один механизм.

**Чистота.** `update` и `view` — чистые функции. Эффекты только через Event.

**Декларативность.** `events` описывает *что* слушать, не *как* управлять подписками.

**Ацикличность.** Signal — чистые потоки. Циклические зависимости невозможны по построению.

**Композиция.** Event комбинируются стандартными операциями:

```agda
never  : Event A                        -- ничего
merge  : Event A → Event A → Event A    -- объединить два потока
map    : (A → B) → Event A → Event B    -- преобразовать события
filter : (A → Bool) → Event A → Event A -- отфильтровать
```

---

## Roadmap

**Phase 1: MVP**
- Signal, Event, foldp
- Примитивы: interval, keyboard, request, websocket
- App (init, update, view, events)
- Html, Runtime

**Phase 2: Расширения**
- mouse, storage, routing
- Конкурентность: `worker : WorkerFn A B → A → Event B` (тот же паттерн Event)
- Focus management, keyed elements
- Higher-order: `join : Signal (Signal A) → Signal A`

**Phase 3: Типизация состояний**
- Индексированные типы для состояний UI
- Session types для протоколов
- Time-travel debugging

> Подробнее: `architecture.md` (базовая архитектура), `arch-concurrency.md` (конкурентность)

---

## Сравнение

| Svelte Runes | Agdelte |
|--------------|---------|
| Магия компилятора | Стандартные абстракции |
| `$state`, `$effect` | Signal, Event |
| Мутация | Fold по событиям |
| Эффекты скрыты | Эффекты = Event |

---

## Заключение

- **Signal** — значения во времени
- **Event** — события извне (всё IO)
- **update** — чистая функция
- **events** — декларативные подписки

Реактивность без магии, IO без императивности, эффекты явны в типах.
