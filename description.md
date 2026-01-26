# Agdelte

## Идея

Svelte 5 ввёл Runes — явную реактивность вместо магии компилятора. Правильный шаг, но TypeScript не знает о Runes, это надстройка.

Agdelte — те же идеи в языке с настоящей системой типов. Реактивность через стандартные абстракции. Эффекты явны в типах. Невозможные состояния непредставимы.

---

## Философия: Три слоя

```
┌───────────────────────────────────────────────────────┐
│  ПОЛЬЗОВАТЕЛЬ: Elm-подобный DSL                       │
│  app { init, update, view, events }                   │
├───────────────────────────────────────────────────────┤
│  БИБЛИОТЕКА: Типизированные комбинаторы              │
│  mapE, filterE, merge, snapshot                       │
├───────────────────────────────────────────────────────┤
│  ТЕОРИЯ: Poly, Coalg, Lens (скрыта)                  │
└───────────────────────────────────────────────────────┘
```

**Принцип:** Elm-модель имеет *фундаментальные* ограничения (нет теории композиции, Cmd непрозрачен). Poly-модель имеет *поверхностную* сложность (можно скрыть за хорошим API). Берём лучшее из обоих.

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

## Что под капотом (для любопытных)

Теория основана на **Polynomial Functors** (Spivak, Niu):

```agda
-- Poly: интерфейс взаимодействия
record Poly : Set₁ where
  Pos : Set              -- что система выдаёт
  Dir : Pos → Set        -- что принимает

-- Coalg: система с состоянием
record Coalg (p : Poly) : Set₁ where
  State : Set
  pos   : State → p.Pos
  step  : (s : State) → p.Dir (pos s) → State

-- Signal, Event, App — экземпляры Coalg
Signal A = Coalg (A, λ _ → ⊤)
Event A  = Signal (List A)
App      = Coalg (Html Msg, λ _ → Msg) + events
```

Комбинаторы — это **Lens** (морфизмы полиномов). Композиция — моноидальные структуры (⊗, ◁, ⊕).

Пользователю это знать не нужно. Но теория гарантирует корректность.

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
| Реактивность | Магия компилятора | Архитектура | Poly + DSL |
| Типы | TypeScript | ML | Зависимые типы |
| Эффекты | Скрыты в $effect | Cmd (непрозрачен) | Event (явно) |
| Композиция | Компоненты | Boilerplate | ⊗, ◁, Lens |
| Доказательства | Нет | Нет | Возможны |

---

## Roadmap

**Phase 1: MVP** — всё интуитивно понятное

Core:
- Signal, Event
- Базовые: never, merge, mapE, filterE, occur
- Signal ↔ Event: foldp, stepper, changes
- Sampling: snapshot, attach, tag, gate
- Аккумуляторы: accumE, accumB
- Временные: debounce, throttle
- Прочее: mergeWith, pre, catchE

Примитивы:
- interval, animationFrame, keyboard, mouse, request

App, Html (с keyed), Runtime

**Phase 2: Расширения** — отдельные концепции

- websocket (сложное состояние)
- localStorage (persistence)
- routing (URL, history)
- switchE, alignWith (динамические потоки)
- touch, focus management

**Phase 3: Конкурентность** — отдельный модуль

- worker, parallel, race, channel

**Phase 4: Продвинутое** — для экспертов

- Incremental (патчи коллекций)
- Session types, Linear types
- Формальная верификация

> Подробнее: [architecture/](architecture/)

---

## Заключение

```
Пользователь пишет:     app { init, update, view, events }
Библиотека реализует:   Coalg, Lens, ⊗
Теория гарантирует:     Корректность, композируемость
```

**Реактивность без магии. IO без императивности. Эффекты явны в типах.**
