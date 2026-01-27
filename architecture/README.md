# Архитектура Agdelte

> **Примечание:** Этот документ описывает архитектуру и теоретическое обоснование.
> См. [../README.md](../README.md) для актуального статуса реализации.

## Философия: Простота + Гарантии

Agdelte построена на принципе **простые определения + изолированная теория**:

```
┌─────────────────────────────────────────────────────────────┐
│  ПОЛЬЗОВАТЕЛЬ                                               │
│  Простые record-определения                                 │
│  App { init, update, view, subs, command }                  │
│  Event — подписки (постоянные)                              │
│  Cmd — команды (одноразовые)                                │
│  Понятные сообщения об ошибках                              │
├─────────────────────────────────────────────────────────────┤
│  БИБЛИОТЕКА                                                 │
│  Типизированные комбинаторы                                 │
│  mapE, filterE, merge, _∥_, mapMsg, mapCmd                  │
├─────────────────────────────────────────────────────────────┤
│  ТЕОРИЯ (Theory/)                                           │
│  Poly, Coalg, Lens — теоретическое обоснование             │
│  Доказательства: Signal ≅ Coalg, App ≅ Coalg               │
│  (изолирована, импортируется по желанию)                   │
└─────────────────────────────────────────────────────────────┘
```

**Ключевой принцип:** Прямые определения для эргономики и понятных ошибок.
Теория (Poly) — в отдельном модуле для формальных гарантий и доказательств.

---

## 1. Слой пользователя: Elm-подобный DSL

### App — главная абстракция

```agda
record App (Model Msg : Set) : Set where
  field
    init    : Model                    -- начальное состояние
    update  : Msg → Model → Model      -- чистая функция (простой!)
    view    : Model → Html Msg         -- чистая функция
    subs    : Model → Event Msg        -- подписки (постоянные события)
    command : Msg → Model → Cmd Msg    -- команды (одноразовые эффекты)
```

### Cmd — одноразовые эффекты

```agda
data Cmd (A : Set) : Set where
  ε        : Cmd A                    -- пустая команда
  _<>_     : Cmd A → Cmd A → Cmd A    -- композиция
  httpGet  : String → (String → A) → (String → A) → Cmd A
  httpPost : String → String → (String → A) → (String → A) → Cmd A
```

**Ключевое разделение:**
- `Event` (subs) — подписки: interval, onKeyDown, onKeyUp (постоянно слушаем)
- `Cmd` (command) — команды: httpGet, httpPost (выполняются один раз)

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

counter : App ℕ Msg
counter = mkApp
  0                                                    -- init
  (λ { Inc n → suc n ; Dec n → pred n ; Tick n → suc n })  -- update
  (λ n → div []                                         -- view
      [ button [ onClick Dec ] [ text "-" ]
      , span [] [ text (show n) ]
      , button [ onClick Inc ] [ text "+" ]
      ])
  (λ _ → interval 1000 Tick)                           -- subs
-- Никаких команд! mkApp автоматически подставляет ε
```

### Пример: HTTP запрос

```agda
data Msg = Fetch | GotData String | GotError String

data Status = Idle | Loading | Ready String

record Model : Set where
  field status : Status

-- update остаётся простым!
update : Msg → Model → Model
update Fetch m = record m { status = Loading }
update (GotData d) m = record m { status = Ready d }
update (GotError _) m = record m { status = Idle }

-- command: когда делать HTTP запрос
command : Msg → Model → Cmd Msg
command Fetch _ = httpGet "/api/data" GotData GotError
command _ _ = ε  -- остальные сообщения — без команд

app : App Model Msg
app = mkCmdApp
  (record { status = Idle })   -- init
  update                        -- update (простой!)
  (λ m → button [ onClick Fetch ] [ text "Load" ])  -- view
  (λ _ → never)                 -- subs (нет подписок)
  command                       -- команды
```

**Ключевой инсайт:**
- `update` остаётся **простым**: `Msg → Model → Model`
- HTTP запрос — в `command`, выполняется **один раз** при Fetch
- `subs` — только для **постоянных** подписок (таймеры, клавиатура)

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

## 3. Слой теории: Theory/ (изолирован)

> **Статус:** Теория находится в `src/Agdelte/Theory/`. Используется для:
> - Формального обоснования корректности
> - Доказательств свойств (будущее)
> - Phase 2+: внутренняя реализация комбинаторов
> - Phase 3+: Wiring diagrams

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

### Текущее состояние (MVP)

```agda
-- Пользователь пишет простые определения
app : App Msg Model
app = record { init = ...; update = ...; view = ...; events = ... }

-- Библиотека реализует через простые функции
-- Композиторы работают напрямую, без Poly
```

### Phase 2+: Poly внутри

```agda
-- Соответствие доказано в Theory/PolyApp.agda
-- App Model Msg ≅ Coalg (AppPoly Msg)
toCoalg : App Msg Model → Coalg (InteractiveP Msg)
toCoalg app = record
  { State = Model
  ; init  = app.init
  ; pos   = app.view
  ; step  = λ m msg → app.update msg m
  }

-- В Phase 2 комбинаторы используют Poly внутри:
-- _∥_ реализован через Poly.parallel
-- mapMsg реализован через Poly.transformCoalg
-- API остаётся простым, гарантии by construction
```

### Теория гарантирует (через Theory/)

- Соответствие: `Signal A ≅ Coalg (Mono A ⊤)`
- Соответствие: `App ≅ Coalg (AppPoly) + init + events`
- Композиция `∥` — это `⊗` на уровне Poly
- Комбинаторы — это Lens

---

## 5. Primitive как полиномы

| Примитив | Poly | Pos | Dir | Статус |
|----------|------|-----|-----|--------|
| `interval ms` | Stream ⊤ | тик | ⊤ | ✅ MVP |
| `animationFrame` | Stream FrameInfo | dt, fps | ⊤ | ✅ MVP |
| `keyboard` | Stream Key | клавиша | ⊤ | 📋 Phase 2 |
| `request req` | Response → ⊤ | ответ | Request | 📋 Phase 2 |
| `websocket` | WsEvent → Maybe String | событие | отправить? | 📋 Phase 2 |

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
4. Подписаться на app.subs(model)
5. Ждать событие (DOM, interval, keyboard, ...)
6. cmd := app.command(msg, model)     -- получить команду
7. model := app.update(msg, model)    -- обновить модель
8. Выполнить cmd (httpGet → fetch)    -- выполнить команды
9. Обновить подписки: diff(subs(old), subs(new))
10. goto 2
```

### JavaScript реализация

```javascript
function runApp(app) {
  let model = app.init;
  let currentSubs = app.subs(model);

  function dispatch(msg) {
    // 1. Получить команды
    const cmd = app.command(msg)(model);

    // 2. Обновить модель
    model = app.update(msg)(model);

    // 3. Выполнить команды
    executeCmd(cmd, dispatch);  // httpGet → fetch → dispatch result

    // 4. Обновить подписки
    const newSubs = app.subs(model);
    updateSubscriptions(currentSubs, newSubs, dispatch);
    currentSubs = newSubs;

    // 5. Перерисовать
    render(app.view(model));
  }

  render(app.view(model));
  subscribe(currentSubs, dispatch);
}

function executeCmd(cmd, dispatch) {
  cmd({
    'ε': () => {},  // пустая команда
    '_<>_': (c1, c2) => { executeCmd(c1, dispatch); executeCmd(c2, dispatch); },
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(r => r.text())
        .then(t => dispatch(onOk(t)))
        .catch(e => dispatch(onErr(e.message)));
    },
    'httpPost': (url, body, onOk, onErr) => { ... }
  });
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

| Свойство | MVP | Phase 2+ |
|----------|-----|----------|
| Унификация | Простые определения | Signal, Event, App ≅ Coalg (доказано) |
| Композиция | Напрямую | ⊗, ◁, ⊕ внутри (гарантии by construction) |
| Трансформации | Простые функции | Lens под капотом |
| Расширяемость | Новые примитивы | Новые примитивы = новые Poly |

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

### Решение: поэтапный подход

| Фаза | Интерфейс | Реализация | Теория |
|------|-----------|------------|--------|
| **MVP** | Elm-подобный | Простые определения | Изолирована в Theory/ |
| **Phase 2** | Elm-подобный (без изменений) | Poly внутри комбинаторов | Используется для гарантий |
| **Phase 3** | + Wiring diagrams | Poly полностью | Для продвинутых пользователей |

- **Пользователь:** Всегда видит простой API
- **Библиотека:** Постепенно внедряет Poly под капотом
- **Теория:** Доступна тем, кому нужны доказательства

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
│  ПОЛЬЗОВАТЕЛЬ (все фазы)                                    │
│    mkApp { init, update, view, subs }      -- простые      │
│    mkCmdApp { ..., command }               -- с HTTP       │
│    Event — подписки (interval, keyboard)                    │
│    Cmd — команды (httpGet, httpPost)                        │
│    Понятные типы, понятные ошибки                           │
├─────────────────────────────────────────────────────────────┤
│  БИБЛИОТЕКА                                                 │
│    MVP: простые определения                                 │
│    Phase 2+: Coalg, Lens, ⊗, ◁, ⊕ под капотом              │
├─────────────────────────────────────────────────────────────┤
│  ТЕОРИЯ (Theory/)                                           │
│    Формальное соответствие Signal ≅ Coalg, App ≅ Coalg     │
│    Доказательства корректности композиции                   │
│    Phase 3+: Wiring diagrams для сложных систем             │
└─────────────────────────────────────────────────────────────┘
```

**Принцип:** Реактивность без магии, IO без императивности, эффекты явны в типах.

**Подход:** Простота для пользователя. Гарантии по построению внутри. Путь к формальной верификации.

**Ключевое разделение:**
- `Event` (subs) — **подписки** на постоянные источники событий
- `Cmd` (command) — **команды** для одноразовых эффектов
- `update` — **остаётся простым**: `Msg → Model → Model`
