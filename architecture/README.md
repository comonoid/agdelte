# Архитектура Agdelte

## Философия: Три слоя

Agdelte построена на **трёхслойной архитектуре**:

```
┌─────────────────────────────────────────────────────────────┐
│  ПОЛЬЗОВАТЕЛЬ                                               │
│  Elm-подобный синтаксис, простые концепции                  │
│  app { init, update, view, events }                         │
│  combine [ app1, app2 ]                                     │
├─────────────────────────────────────────────────────────────┤
│  БИБЛИОТЕКА                                                 │
│  Типизированные комбинаторы                                 │
│  mapE, filterE, merge, snapshot, ⊗, ◁, Lens                │
├─────────────────────────────────────────────────────────────┤
│  ТЕОРИЯ                                                     │
│  Poly, Coalg, Behavior, unfold                              │
│  (скрыта от пользователей)                                  │
└─────────────────────────────────────────────────────────────┘
```

**Ключевой принцип:** Elm-модель имеет *фундаментальные* ограничения (нет теории композиции, hardcoded Html, boilerplate). Poly-модель имеет *поверхностную* сложность (можно скрыть за хорошим API). Мы берём лучшее из обоих: Elm-подобный интерфейс на фундаменте Poly.

---

## 1. Слой пользователя: Elm-подобный DSL

### App — главная абстракция

```agda
record App (Msg : Set) (Model : Set) : Set where
  field
    init   : Model                    -- начальное состояние
    update : Msg → Model → Model      -- чистая функция
    view   : Model → Html Msg         -- чистая функция
    events : Model → Event Msg        -- декларативные подписки
```

### Signal и Event — дискретные потоки

```agda
-- Signal: дискретный поток значений (одно значение на такт)
Signal : Set → Set

-- Event: дискретные события (список событий за такт)
Event : Set → Set
Event A = Signal (List A)

-- Примитивы IO — всё это Event
interval       : ℕ → Event ⊤
keyboard       : Event Key
animationFrame : Event FrameInfo
request        : Request → Event Response
websocket      : Url → WebSocket
```

### Пример: счётчик с таймером

```agda
data Msg = Inc | Dec | Tick

counter : App Msg ℕ
counter = record
  { init   = 0
  ; update = λ { Inc n → suc n ; Dec n → pred n ; Tick n → suc n }
  ; view   = λ n → div []
      [ button [ onClick Dec ] [ text "-" ]
      , span [] [ text (show n) ]
      , button [ onClick Inc ] [ text "+" ]
      ]
  ; events = λ _ → mapE (const Tick) (interval 1000)
  }
```

### Пример: HTTP запрос

```agda
data Msg = Fetch | GotData Response

data Status = Idle | Loading | Ready Data

record Model : Set where
  status : Status

app : App Msg Model
app = record
  { init = { status = Idle }
  ; update = λ where
      Fetch m → record m { status = Loading }
      (GotData r) m → record m { status = Ready (parse r) }
  ; view = λ m → button [ onClick Fetch ] [ text "Load" ]
  ; events = λ m → case m.status of λ where
      Loading → mapE GotData (request (get "/api"))
      _ → never
  }
```

**Ключевой инсайт:** `events` зависит от `Model`. Когда `status = Loading` — runtime подписывается на HTTP. Ответ пришёл, status изменился — автоматическая отписка. Нет ручного cleanup, нет утечек.

---

## 2. Слой библиотеки: Комбинаторы

### Базовые операции

```agda
-- Пустой поток
never : Event A

-- Объединение
merge : Event A → Event A → Event A

-- Трансформация
mapE : (A → B) → Event A → Event B

-- Фильтрация
filterE : (A → Bool) → Event A → Event A
```

### Sampling (взаимодействие Event и Signal)

```agda
-- Семплировать Signal при событии
snapshot : (A → B → C) → Event A → Signal B → Event C

-- Фильтр по Signal
gate : Event A → Signal Bool → Event A

-- События изменения Signal
changes : Signal A → Event A
```

### Временные

```agda
debounce : ℕ → Event A → Event A    -- после паузы N мс
throttle : ℕ → Event A → Event A    -- максимум раз в N мс
```

### Композиция приложений

```agda
-- Параллельно (независимо)
_∥_ : App Msg₁ Model₁ → App Msg₂ Model₂ → App (Msg₁ ⊎ Msg₂) (Model₁ × Model₂)

-- Выбор (переключение)
_⊕ᵃ_ : App Msg Model → App Msg Model → App Msg (Model ⊎ Model)

-- Вложенный компонент
embed : (Msg₁ → Msg₂) → (Model₂ → Model₁) → (Model₁ → Model₂ → Model₂)
      → App Msg₁ Model₁ → App Msg₂ Model₂ → App Msg₂ Model₂
```

### Пример: два независимых счётчика

```agda
data Msg = Left CounterMsg | Right CounterMsg

twoCounters : App Msg (ℕ × ℕ)
twoCounters = mapMsg Left counter ∥ mapMsg Right counter
```

---

## 3. Слой теории: Poly (для разработчиков библиотеки)

### Poly (полиномиальный функтор)

```agda
record Poly : Set₁ where
  field
    Pos : Set              -- позиции (что система выдаёт)
    Dir : Pos → Set        -- направления (что принимает)
```

Полином `p(y) = Σ_{i : Pos} y^{Dir i}` описывает **контракт взаимодействия**.

### Coalg (коалгебра = система с состоянием)

```agda
record Coalg (p : Poly) : Set₁ where
  field
    State : Set
    init  : State
    pos   : State → p.Pos
    step  : (s : State) → p.Dir (pos s) → State
```

### Behavior (финальная коалгебра = поведение без состояния)

```agda
Behavior : Poly → Set
Behavior p = ν X. Σ (o : p.Pos) (p.Dir o → X)
```

### unfold/fold — мост между представлениями

```agda
unfold : Coalg p → Behavior p    -- "забыть" внутреннее состояние
fold   : Behavior p → Coalg p    -- "восстановить" состояние (не уникально)
```

### Signal, Event, App — экземпляры Coalg

```agda
-- Stream полином
StreamP : Set → Poly
StreamP A = record { Pos = A ; Dir = λ _ → ⊤ }

Signal A = Coalg (StreamP A)    -- или Behavior (StreamP A)
Event A  = Signal (List A)

-- Interactive полином
InteractiveP : Set → Poly
InteractiveP Msg = record { Pos = Html Msg ; Dir = λ _ → Msg }

-- App ≈ Coalg (InteractiveP Msg) + events
```

### Lens (морфизм полиномов)

```agda
record Lens (p q : Poly) : Set where
  field
    fwd : p.Pos → q.Pos
    bwd : (i : p.Pos) → q.Dir (fwd i) → p.Dir i
```

Все комбинаторы (mapE, filterE, ...) — это Lens под капотом.

### Моноидальные структуры

```agda
-- Параллельная композиция
_⊗_ : Poly → Poly → Poly
(p ⊗ q).Pos = p.Pos × q.Pos
(p ⊗ q).Dir (i, j) = p.Dir i × q.Dir j

-- Последовательная композиция
_◁_ : Poly → Poly → Poly

-- Выбор
_⊕_ : Poly → Poly → Poly
(p ⊕ q).Pos = p.Pos ⊎ q.Pos
(p ⊕ q).Dir = [ p.Dir , q.Dir ]
```

---

## 4. Как слои связаны

### Пользователь видит

```agda
app : App Msg Model
app = record { init = ...; update = ...; view = ...; events = ... }
```

### Библиотека реализует как

```agda
-- App — это обёртка над Coalg
toCoalg : App Msg Model → Coalg (InteractiveP Msg)
toCoalg app = record
  { State = Model
  ; init  = app.init
  ; pos   = app.view
  ; step  = λ m msg → app.update msg m
  }
```

### Теория гарантирует

- Композиция `∥` — это `⊗` на уровне Poly
- Комбинаторы — это Lens
- Все операции корректны по построению

---

## 5. Primitive как полиномы

| Примитив | Poly | Pos | Dir |
|----------|------|-----|-----|
| `interval ms` | Stream ⊤ | тик | ⊤ |
| `keyboard` | Stream Key | клавиша | ⊤ |
| `request req` | Response → ⊤ | ответ | Request |
| `websocket` | WsEvent → Maybe String | событие | отправить? |

**Dir может быть нетривиальным:**
- `interval`: `Dir = ⊤` — просто продолжай
- `request`: `Dir = Request` — нужен запрос для ответа
- `websocket`: `Dir = Maybe String` — можно отправить сообщение

Это отражает **реальные протоколы** взаимодействия.

---

## 6. Runtime

### Алгоритм

```
1. model := app.init
2. html := app.view(model)
3. Рендер DOM, установить обработчики
4. Подписаться на app.events(model)
5. Ждать событие (DOM, interval, request, ...)
6. model := app.update(msg, model)
7. Обновить подписки: diff(events(old), events(new))
8. goto 2
```

### JavaScript реализация

```javascript
function runApp(app) {
  let model = app.init;
  let currentEvents = app.events(model);

  function dispatch(msg) {
    model = app.update(msg, model);

    const newEvents = app.events(model);
    diffSubscriptions(currentEvents, newEvents, dispatch);
    currentEvents = newEvents;

    render(app.view(model));
  }

  render(app.view(model));
  subscribe(currentEvents, dispatch);
}
```

---

## 7. Что даёт эта архитектура

### Для пользователя

| Свойство | Описание |
|----------|----------|
| Простота | Elm-подобный API, 4 поля |
| Чистота | update и view — чистые функции |
| Декларативность | events описывает *что*, не *как* |
| Автоматический cleanup | Event исчез → отписка |
| Тестируемость | `update msg model ≡ expected` |

### Для библиотеки

| Свойство | Описание |
|----------|----------|
| Унификация | Signal, Event, App — экземпляры Coalg |
| Композиция | ⊗, ◁, ⊕ — принципиальные способы |
| Трансформации | Lens для любых преобразований |
| Расширяемость | Новые примитивы = новые Poly |

### От теории

| Свойство | Описание |
|----------|----------|
| Time-travel | Тривиально (список Model) |
| Сериализация | `JSON.stringify(model)` |
| Race conditions | Невозможны по построению |
| Формальные доказательства | Poly хорошо изучена |

---

## 8. Сравнение подходов

### Почему не чистый Elm?

| Проблема | Описание |
|----------|----------|
| Нет теории композиции | Вложение компонентов — boilerplate |
| Hardcoded Html | Msg привязан к DOM |
| Cmd — чёрный ящик | Эффекты непрозрачны |
| Нет доказательств | Нельзя формально верифицировать |

### Почему не чистый Poly?

| Проблема | Описание |
|----------|----------|
| Крутая кривая обучения | Coalg, Lens, ⊗ — абстрактно |
| Много boilerplate | Wiring diagrams вручную |
| Нет привычного API | Пользователи ожидают Elm-like |

### Решение: лучшее из обоих

- **Интерфейс:** Elm-подобный (простой, знакомый)
- **Реализация:** Poly (корректная, расширяемая)
- **Теория:** Скрыта, но доступна

---

## 9. Источники

| Тема | Ресурс |
|------|--------|
| Polynomial Functors | Spivak, Niu "Polynomial Functors: A Mathematical Theory of Interaction" |
| Coalgebras | Rutten "Universal Coalgebra" |
| Elm Architecture | Evan Czaplicki |
| Reflex FRP | Ryan Trinkle |
| Categories of Containers | Abbott, Altenkirch, Ghani |

---

## 10. Итог

```
┌─────────────────────────────────────────────────────────────┐
│  Пользователь пишет:                                        │
│    app { init, update, view, events }                       │
│    mapE, filterE, merge, snapshot                           │
├─────────────────────────────────────────────────────────────┤
│  Библиотека реализует через:                                │
│    Coalg, Lens, ⊗, ◁, ⊕                                    │
├─────────────────────────────────────────────────────────────┤
│  Теория гарантирует:                                        │
│    Корректность, композируемость, расширяемость             │
└─────────────────────────────────────────────────────────────┘
```

**Принцип:** Реактивность без магии, IO без императивности, эффекты явны в типах. Простота использования, мощность под капотом.
