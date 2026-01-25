# Архитектура Agdelte

## 0. Ключевые концепции

### Такт (Tick)

**Такт** — атомарная единица дискретного времени в системе. Один такт = одна итерация event loop.

```
Такт 0 → Такт 1 → Такт 2 → ...
   │        │        │
   ▼        ▼        ▼
 events   events   events
```

Границы такта определяются **событиями**:
- Каждое внешнее событие (клик, таймер, HTTP ответ) начинает новый такт
- За один такт: получить события → update → обновить подписки → render
- Между тактами система в состоянии покоя (idle)

В терминах браузера: такт ≈ обработка одного события из event queue.

### Push-семантика

События "проталкиваются" (push) извне в систему:
- **Внешний мир** → генерирует события (клики, таймеры, HTTP ответы)
- **Runtime** → получает и направляет события в `update`
- **Приложение** → реактивно обновляется

Приложение не опрашивает источники (pull), а получает уведомления (push).

### Одновременные события

Если несколько внешних событий происходят "одновременно" (например, два клика подряд быстрее чем один такт):

- **Браузер** сериализует их в очередь событий
- **Каждое событие** обрабатывается отдельным тактом
- **Порядок** сохраняется (FIFO)

Исключение: события внутри одного DOM event (например, `input` с несколькими символами при paste) — приходят как один такт со списком.

## Обзор

```
┌─────────────────────────────────────────────────────────────┐
│                        Agdelte                              │
├─────────────────────────────────────────────────────────────┤
│  Core          │  Signal, Event, комбинаторы               │
├─────────────────────────────────────────────────────────────┤
│  Primitives    │  interval, keyboard, request, ...         │
├─────────────────────────────────────────────────────────────┤
│  App           │  init, update, view, events               │
├─────────────────────────────────────────────────────────────┤
│  Html          │  Типизированные элементы и атрибуты       │
├─────────────────────────────────────────────────────────────┤
│  Runtime       │  Event loop, подписки, рендеринг          │
└─────────────────────────────────────────────────────────────┘
```

---

## 1. Signal

### Определение

```agda
record Signal (A : Set) : Set where
  coinductive
  field
    now  : A
    next : Signal A
```

Signal — коиндуктивный (бесконечный) поток значений. `now` — текущее значение, `next` — продолжение потока.

### Functor

```agda
map : (A → B) → Signal A → Signal B
map f s .now  = f (s .now)
map f s .next = map f (s .next)

-- Инфиксный синоним
_<$>_ = flip map
```

Пример:
```agda
doubled : Signal ℕ
doubled = (2 *_) <$> counter
-- Если counter = [0, 1, 2, 3, ...]
-- То doubled = [0, 2, 4, 6, ...]
```

### Applicative

```agda
pure : A → Signal A
pure a .now  = a
pure a .next = pure a

_<*>_ : Signal (A → B) → Signal A → Signal B
(sf <*> sa) .now  = sf .now (sa .now)
(sf <*> sa) .next = sf .next <*> sa .next
```

Пример:
```agda
-- Сложить два сигнала
sum : Signal ℕ
sum = pure _+_ <*> a <*> b

-- Или с idiom brackets
sum = ⦇ a + b ⦈
```

### Семантика

Signal можно понимать как функцию от времени:

```
Signal A  ≈  ℕ → A

s : Signal A
s 0 = s .now
s 1 = s .next .now
s 2 = s .next .next .now
...
```

---

## 2. Event

### Определение

```agda
Event : Set → Set
Event A = Signal (List A)
```

Event — поток списков событий. Каждый такт: пустой список (нет событий), один элемент, или несколько.

### Базовые значения

```agda
-- Никогда не происходит
never : Event A
never .now  = []
never .next = never

-- Одно событие сейчас
occur : A → Event A
occur a .now  = [ a ]
occur a .next = never
```

### Комбинаторы

```agda
-- Объединить два потока
merge : Event A → Event A → Event A
merge e1 e2 .now  = e1 .now ++ e2 .now
merge e1 e2 .next = merge (e1 .next) (e2 .next)

-- Преобразовать события
mapE : (A → B) → Event A → Event B
mapE f e .now  = List.map f (e .now)
mapE f e .next = mapE f (e .next)

-- Отфильтровать
filterE : (A → Bool) → Event A → Event A
filterE p e .now  = List.filter p (e .now)
filterE p e .next = filterE p (e .next)

-- Разделить по предикату
partitionE : (A → Bool) → Event A → Event A × Event A
partitionE p e = (filterE p e , filterE (not ∘ p) e)
```

**Примечание:** `mapE` для Event отличается от `map` для Signal:
- `map : (A → B) → Signal A → Signal B` — применяет к `now`
- `mapE : (A → B) → Event A → Event B` — применяет к каждому элементу списка

Можно было бы унифицировать через Functor instance, но явные имена понятнее для обучения.

### Event → Signal

```agda
-- Свёртка событий в состояние
foldp : (A → B → B) → B → Event A → Signal B
foldp f init e .now  = init
foldp f init e .next = foldp f (foldr f init (e .now)) (e .next)

-- Запомнить последнее событие
hold : A → Event A → Signal A
hold init e .now  = init
hold init e .next = hold (fromMaybe init (lastMaybe (e .now))) (e .next)
  where
    lastMaybe : List A → Maybe A
    lastMaybe [] = Nothing
    lastMaybe (x ∷ []) = Just x
    lastMaybe (_ ∷ xs) = lastMaybe xs

    fromMaybe : A → Maybe A → A
    fromMaybe def Nothing  = def
    fromMaybe _   (Just x) = x
```

### Пример foldp

```agda
-- Счётчик кликов
clicks : Event ⊤
counter : Signal ℕ
counter = foldp (λ _ n → suc n) 0 clicks

-- clicks  = [[], [tt], [], [tt, tt], [], ...]
-- counter = [0,  0,    1,  1,       3,  ...]
--                 ↑         ↑↑
--              +1 тут    +2 тут (два клика за такт)
```

---

## 3. Примитивы Event

Примитивы — источники событий из внешнего мира. Реализуются через FFI.

### Базовые типы

```agda
-- URL как строка (для MVP)
Url = String

-- Тело запроса/ответа
Body = String  -- JSON строка

-- HTTP статус
Status = ℕ     -- 200, 404, 500, ...

-- WebSocket сообщение
Message = String

-- Направление стрелок
data Direction : Set where
  Up Down Left Right : Direction

-- Клавиша
data Key : Set where
  Char   : Char → Key
  Enter Escape Tab Backspace Delete : Key
  Arrow  : Direction → Key
  Ctrl Alt Shift Meta : Key → Key  -- модификаторы
  F : ℕ → Key                       -- F1-F12
  Other : String → Key              -- остальные
```

### interval

```agda
interval : ℕ → Event ⊤
```

Событие каждые `n` миллисекунд.

```
interval 1000:
  такт 0ms:    []
  такт 100ms:  []
  ...
  такт 1000ms: [tt]  ← событие
  такт 1100ms: []
  ...
  такт 2000ms: [tt]  ← событие
  ...
```

### keyboard

```agda
keyboard : Event Key
```

События нажатия клавиш.

```agda
data Key : Set where
  Char   : Char → Key
  Enter  : Key
  Escape : Key
  Arrow  : Direction → Key
  ...
```

### request

```agda
request : Request → Event Response
```

HTTP запрос как источник события.

```agda
data Request : Set where
  get  : Url → Request
  post : Url → Body → Request
  ...

data Response : Set where
  ok    : Status → Body → Response
  error : Status → String → Response
```

Семантика:
- Подписка на `request r` → отправить HTTP запрос
- Ответ пришёл → событие `Response`
- Отписка → отменить запрос (если ещё не завершён)

```
request (get "/api"):
  такт 0:   [] (запрос отправлен)
  такт 1:   [] (ждём)
  ...
  такт N:   [Response] (ответ пришёл)
  такт N+1: [] (больше событий нет)
```

### websocket

```agda
data WsEvent : Set where
  Connected : WsEvent                    -- соединение установлено
  Message   : String → WsEvent           -- сообщение от сервера
  Closed    : WsEvent                    -- соединение закрыто
  Error     : String → WsEvent           -- ошибка

record WebSocket : Set where
  field
    recv : Event WsEvent                 -- входящие события
    send : String → Event ⊤              -- отправить сообщение

websocket : Url → WebSocket
```

WebSocket как двунаправленный канал связи.

**Семантика:**
- `websocket url` — создаёт WebSocket record (ленивый, соединение ещё не открыто)
- Подписка на `recv` — открывает соединение
- `send msg` — возвращает Event ⊤, при подписке отправляет сообщение
- Отписка от `recv` — закрывает соединение

```
ws = websocket "ws://server"

ws.recv:
  подписка → открыть соединение
  соединение открыто → событие Connected
  сообщение пришло → событие (Message data)
  ошибка → событие (Error msg)
  отписка → закрыть соединение

ws.send "hello":
  подписка → отправить "hello"
  отправлено → событие ⊤
  отписка → ничего (уже отправлено)
```

**Пример использования:**

```agda
data Msg = WsMsg WsEvent | Sent | SendMessage String

record Model : Set where
  field
    connected : Bool
    messages  : List String
    toSend    : Maybe String

ws : WebSocket
ws = websocket "ws://chat.example.com"

app : App Msg Model
app = record
  { init = { connected = false; messages = []; toSend = Nothing }

  ; update = λ where
      (WsMsg Connected) m → record m { connected = true }
      (WsMsg (Message s)) m → record m { messages = s ∷ m.messages }
      (WsMsg Closed) m → record m { connected = false }
      (WsMsg (Error _)) m → m
      Sent m → record m { toSend = Nothing }
      (SendMessage s) m → record m { toSend = Just s }

  ; view = ...

  ; events = λ m → merge
      (mapE WsMsg (ws .recv))                              -- всегда слушаем
      (maybe never (λ s → mapE (const Sent) (ws .send s)) (m .toSend))  -- отправляем если есть
  }
```

### Одноразовые vs повторяющиеся Event

| Примитив | Тип | Характер |
|----------|-----|----------|
| `interval n` | `Event ⊤` | Повторяющийся — события каждые n мс |
| `keyboard` | `Event Key` | Повторяющийся — событие на каждое нажатие |
| `request r` | `Event Response` | Одноразовый — одно событие, потом `never` |
| `websocket url` | `Event Message` | Повторяющийся — события пока соединение открыто |

**Одноразовые Event (request):**
- После получения ответа Event становится эквивалентен `never`
- Если приложение продолжает включать его в `events`, ничего не происходит
- Для повторного запроса нужно убрать Event из `events` и добавить снова

```agda
-- Типичный паттерн для одноразового запроса
events m = if m.loading then mapE GotData (request ...) else never
-- loading=true → запрос → ответ → update ставит loading=false → Event убран
```

### Сводка примитивов (MVP)

| Примитив | Тип | Подписка | Отписка |
|----------|-----|----------|---------|
| `interval n` | `Event ⊤` | Запустить таймер | Остановить таймер |
| `keyboard` | `Event Key` | addEventListener | removeEventListener |
| `request r` | `Event Response` | Отправить запрос | Отменить запрос |
| `websocket url` | `WebSocket` | — | — |
| `ws.recv` | `Event WsEvent` | Открыть соединение | Закрыть соединение |
| `ws.send msg` | `Event ⊤` | Отправить сообщение | — (уже отправлено) |

### Примитивы Phase 2

```agda
-- Мышь
data MouseEvent : Set where
  Click Move : ℕ × ℕ → MouseEvent        -- координаты (x, y)
  Down Up    : ℕ × ℕ → MouseButton → MouseEvent

mouse : Event MouseEvent

-- LocalStorage
storage : String → Event (Maybe String)  -- следить за ключом
setStorage : String → String → Event ⊤   -- записать (одноразовый)
getStorage : String → Event (Maybe String)  -- прочитать (одноразовый)

-- Routing (History API)
data Route : Set where
  -- определяется приложением

location : Event Url                      -- изменения URL
navigate : Url → Event ⊤                  -- программная навигация (pushState)
```

**Routing паттерн:**

```agda
-- URL как часть Model
record Model : Set where
  field
    route : Route
    ...

-- Парсинг URL
parseRoute : Url → Route

-- Обработка навигации
data Msg = UrlChanged Url | ...

app = record
  { ...
  ; update = λ where
      (UrlChanged url) m → record m { route = parseRoute url }
      ...
  ; events = λ m → merge
      (mapE UrlChanged location)  -- слушаем изменения URL
      ...
  }
```

---

## 4. App

### Определение

```agda
record App (Msg : Set) (Model : Set) : Set where
  field
    init   : Model
    update : Msg → Model → Model
    view   : Model → Html Msg
    events : Model → Event Msg
```

### Поля

**init** — начальное состояние приложения.

**update** — чистая функция. Получает сообщение и текущее состояние, возвращает новое состояние. Без побочных эффектов.

**view** — чистая функция. Получает состояние, возвращает Html. Html параметризован типом Msg — события из DOM будут этого типа.

**events** — декларация внешних событий. Зависит от Model, что позволяет динамически включать/выключать источники событий.

### Разворачивание App в Signal

Концептуально App можно развернуть в Signal Html:

```agda
runApp : App Msg Model → Event Msg → Signal (Html Msg)
runApp app domEvents = view <$> model
  where
    -- Все события: DOM + внешние
    allEvents : Signal (Event Msg)
    allEvents = λ m → merge domEvents (app .events m)

    -- Состояние как свёртка событий
    model : Signal Model
    model = foldpWithDynamic app.update app.init allEvents

    view = app .view
```

(Реальная реализация сложнее из-за динамических events)

---

## 5. Html

### Структура

```agda
data Html (Msg : Set) : Set where
  text   : String → Html Msg
  node   : Tag → List (Attr Msg) → List (Html Msg) → Html Msg

-- Удобные функции
div : List (Attr Msg) → List (Html Msg) → Html Msg
div = node "div"

button : List (Attr Msg) → List (Html Msg) → Html Msg
button = node "button"

span : List (Attr Msg) → List (Html Msg) → Html Msg
span = node "span"
-- и т.д.
```

### Атрибуты

```agda
data Attr (Msg : Set) : Set where
  -- События
  onClick   : Msg → Attr Msg
  onInput   : (String → Msg) → Attr Msg
  onSubmit  : Msg → Attr Msg
  onKeyDown : (Key → Msg) → Attr Msg

  -- Свойства
  className : String → Attr Msg
  id        : String → Attr Msg
  disabled  : Bool → Attr Msg
  value     : String → Attr Msg
  href      : String → Attr Msg
  src       : String → Attr Msg
  type'     : String → Attr Msg    -- type зарезервирован в Agda
  checked   : Bool → Attr Msg
  placeholder : String → Attr Msg
  style     : List (String × String) → Attr Msg  -- CSS свойства

  -- Модификаторы событий
  preventDefault  : Attr Msg       -- предотвратить действие по умолчанию
  stopPropagation : Attr Msg       -- остановить всплытие

  -- Focus (Phase 2)
  autofocus : Attr Msg             -- фокус при монтировании
  tabIndex  : ℕ → Attr Msg         -- порядок табуляции
```

### Focus management (Phase 2)

Программное управление фокусом через команды:

```agda
-- Фокус как Event (одноразовый)
focus : ElementId → Event ⊤        -- установить фокус
blur  : ElementId → Event ⊤        -- снять фокус

-- Пример: фокус на input после добавления todo
events m = merge
  (if m.justAdded then focus "new-todo" else never)
  ...
```

### Получение значений из DOM событий

`onInput` получает значение из `event.target.value`:

```javascript
// Runtime автоматически извлекает значение
element.addEventListener('input', (e) => {
  const msg = handler(e.target.value)  // handler : String → Msg
  tick([msg])
})
```

Аналогично для других событий:
- `onInput` → `event.target.value : String`
- `onCheck` → `event.target.checked : Bool`
- `onKeyDown` → `event.key : Key` (после преобразования)
- `onClick` → без значения (просто `Msg`)

### Полный набор элементов

```agda
-- Структурные
div, span, section, article, header, footer, nav, main : List (Attr Msg) → List (Html Msg) → Html Msg

-- Заголовки
h1, h2, h3, h4, h5, h6 : List (Attr Msg) → List (Html Msg) → Html Msg

-- Списки
ul, ol, li : List (Attr Msg) → List (Html Msg) → Html Msg

-- Формы
form, input, textarea, select, option, label : List (Attr Msg) → List (Html Msg) → Html Msg
button : List (Attr Msg) → List (Html Msg) → Html Msg

-- Таблицы
table, thead, tbody, tr, th, td : List (Attr Msg) → List (Html Msg) → Html Msg

-- Медиа
img, audio, video : List (Attr Msg) → List (Html Msg) → Html Msg

-- Ссылки
a : List (Attr Msg) → List (Html Msg) → Html Msg

-- Семантические
p, blockquote, pre, code, em, strong : List (Attr Msg) → List (Html Msg) → Html Msg

-- Специальные
empty : Html Msg                                    -- пустой элемент (не рендерится)
fragment : List (Html Msg) → Html Msg               -- группа без обёртки
```

**empty** — для условного рендеринга:
```agda
view m = div []
  [ if m.showHeader then header [] [...] else empty
  , content m
  ]
```

**fragment** — для возврата нескольких элементов:
```agda
viewItems : List Item → Html Msg
viewItems items = fragment (map viewItem items)
```

### Трансформация Msg

```agda
mapHtml : (A → B) → Html A → Html B
```

**Реализация mapHtml:**

```agda
mapHtml f (text s) = text s
mapHtml f (node tag attrs children) = node tag (map (mapAttr f) attrs) (map (mapHtml f) children)

mapAttr : (A → B) → Attr A → Attr B
mapAttr f (onClick msg) = onClick (f msg)
mapAttr f (onInput handler) = onInput (f ∘ handler)
mapAttr f (onKeyDown handler) = onKeyDown (f ∘ handler)
mapAttr f (className s) = className s  -- не содержит Msg
mapAttr f (disabled b) = disabled b    -- не содержит Msg
-- ... остальные атрибуты без Msg остаются без изменений
```

**Представление Html в JS:**

```javascript
// text "hello"
{ type: 'text', value: 'hello' }

// div [ className "foo" ] [ text "bar" ]
{
  type: 'node',
  tag: 'div',
  attrs: [{ type: 'className', value: 'foo' }],
  children: [{ type: 'text', value: 'bar' }]
}

// button [ onClick Inc ] [ text "+" ]
{
  type: 'node',
  tag: 'button',
  attrs: [{ type: 'onClick', msg: { tag: 'Inc' } }],
  children: [{ type: 'text', value: '+' }]
}

// input [ onInput SetName, value "test" ] []
{
  type: 'node',
  tag: 'input',
  attrs: [
    { type: 'onInput', handler: (s) => ({ tag: 'SetName', value: s }) },
    { type: 'value', value: 'test' }
  ],
  children: []
}

// empty — не рендерится
{ type: 'empty' }

// fragment [a, b, c] — группа без обёртки
{ type: 'fragment', children: [a, b, c] }
```

Позволяет встраивать компоненты с разными типами Msg:

```agda
-- Дочерний компонент
module Counter where
  data Msg = Inc | Dec
  view : ℕ → Html Msg

-- Родительский компонент
module Parent where
  data Msg = Counter1 Counter.Msg | Counter2 Counter.Msg

  view : Model → Html Msg
  view m = div []
    [ mapHtml Counter1 (Counter.view m.counter1)
    , mapHtml Counter2 (Counter.view m.counter2)
    ]
```

### Композиция приложений

Для вложенных App с собственными events:

```agda
-- Дочернее приложение
module Child where
  childApp : App ChildMsg ChildModel

-- Родительское приложение
module Parent where
  data Msg = ChildMsg ChildMsg | ParentMsg ParentMsg

  record Model : Set where
    field
      child  : ChildModel
      parent : ParentData

  parentApp : App Msg Model
  parentApp = record
    { init = { child = Child.childApp.init; parent = ... }

    ; update = λ where
        (ChildMsg cm) m → record m { child = Child.childApp.update cm (m .child) }
        (ParentMsg pm) m → ...

    ; view = λ m → div []
        [ mapHtml ChildMsg (Child.childApp.view (m .child))
        , parentView m
        ]

    ; events = λ m → merge
        (mapE ChildMsg (Child.childApp.events (m .child)))  -- события ребёнка
        (mapE ParentMsg (parentEvents m))                    -- события родителя
    }
```

### DOM events

События из Html (onClick, onInput, ...) обрабатываются runtime автоматически:

```agda
-- onClick генерирует Msg при клике
button [ onClick Inc ] [ text "+" ]
```

Runtime при рендеринге:
1. Находит атрибуты-события (onClick, onInput, ...)
2. Устанавливает DOM обработчики
3. При срабатывании → вызывает `update(msg, model)`

Концептуально DOM events — это ещё один Event, который merge'ится с `events(model)`:

```agda
allEvents : Model → Event Msg
allEvents m = merge (domEvents m) (app.events m)
```

Но `domEvents` создаётся runtime неявно из `view(model)`.

### Html Diff

Runtime сравнивает старый и новый Html для минимальных DOM операций:

```javascript
function diff(oldHtml, newHtml) {
  const patches = []

  // Разные типы узлов — заменить полностью
  if (oldHtml.type !== newHtml.type) {
    return [{ type: 'replace', node: newHtml }]
  }

  // Оба — text
  if (oldHtml.type === 'text') {
    if (oldHtml.value !== newHtml.value) {
      patches.push({ type: 'text', value: newHtml.value })
    }
    return patches
  }

  // Оба — node: сравнить tag, attrs, children
  if (oldHtml.tag !== newHtml.tag) {
    return [{ type: 'replace', node: newHtml }]
  }

  // Diff атрибутов
  patches.push(...diffAttrs(oldHtml.attrs, newHtml.attrs))

  // Diff детей (по индексу, без ключей для MVP)
  patches.push(...diffChildren(oldHtml.children, newHtml.children))

  return patches
}
```

**Для MVP:** сравнение детей по индексу. Если список изменился — перерендерить хвост.

### diffAttrs и diffChildren

```javascript
function diffAttrs(oldAttrs, newAttrs) {
  const patches = []

  // Удалённые/изменённые атрибуты
  for (const oldAttr of oldAttrs) {
    const newAttr = newAttrs.find(a => a.type === oldAttr.type)
    if (!newAttr) {
      patches.push({ type: 'removeAttr', attr: oldAttr })
    } else if (!attrEqual(oldAttr, newAttr)) {
      patches.push({ type: 'setAttr', attr: newAttr })
    }
  }

  // Новые атрибуты
  for (const newAttr of newAttrs) {
    const oldAttr = oldAttrs.find(a => a.type === newAttr.type)
    if (!oldAttr) {
      patches.push({ type: 'setAttr', attr: newAttr })
    }
  }

  return patches.length > 0 ? [{ type: 'attrs', patches }] : []
}

function attrEqual(a, b) {
  if (a.type !== b.type) return false
  // События: функции не сравниваем (считаем разными)
  if (a.type.startsWith('on')) return false
  // Значения
  return a.value === b.value || JSON.stringify(a.value) === JSON.stringify(b.value)
}

function diffChildren(oldChildren, newChildren) {
  const patches = []

  const maxLen = Math.max(oldChildren.length, newChildren.length)

  for (let i = 0; i < maxLen; i++) {
    const oldChild = oldChildren[i]
    const newChild = newChildren[i]

    if (!oldChild) {
      // Новый ребёнок — добавить
      patches.push({ type: 'appendChild', index: i, node: newChild })
    } else if (!newChild) {
      // Удалённый ребёнок
      patches.push({ type: 'removeChild', index: i })
    } else {
      // Оба есть — рекурсивный diff
      const childPatches = diff(oldChild, newChild)
      if (childPatches.length > 0) {
        patches.push({ type: 'patchChild', index: i, patches: childPatches })
      }
    }
  }

  return patches.length > 0 ? [{ type: 'children', patches }] : []
}

function applyChildPatches(element, patches, tick) {
  // Применяем в обратном порядке для корректных индексов при удалении
  const sortedPatches = [...patches].sort((a, b) => b.index - a.index)

  for (const patch of sortedPatches) {
    switch (patch.type) {
      case 'appendChild':
        const newChild = createElement(patch.node, tick)
        if (patch.index >= element.children.length) {
          element.appendChild(newChild)
        } else {
          element.insertBefore(newChild, element.children[patch.index])
        }
        break

      case 'removeChild':
        if (element.children[patch.index]) {
          element.removeChild(element.children[patch.index])
        }
        break

      case 'patchChild':
        const child = element.children[patch.index]
        if (child) {
          applyPatches(patch.patches, child, tick)
        }
        break
    }
  }
}
```

**Оптимизация (post-MVP):** keyed элементы для эффективного обновления списков:
```agda
keyedLi : String → List (Attr Msg) → List (Html Msg) → Html Msg
keyedLi key attrs children = node "li" (keyAttr key ∷ attrs) children
```

---

## 6. Runtime

### Event Loop

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   ┌─────────┐      ┌────────┐      ┌──────┐      ┌─────┐   │
│   │  init   │ ───► │ model  │ ───► │ view │ ───► │ DOM │   │
│   └─────────┘      └────────┘      └──────┘      └─────┘   │
│                         ▲                            │      │
│                         │                            │      │
│                    ┌────────┐                        │      │
│                    │ update │ ◄──────────────────────┘      │
│                    └────────┘         DOM events            │
│                         ▲                                   │
│                         │                                   │
│                    ┌────────────┐                           │
│                    │   events   │ ◄─── interval, request    │
│                    └────────────┘                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Псевдокод

```javascript
function runApp(app) {
  let model = app.init
  let currentEvents = null
  let subscriptions = new Map()

  function tick(msgs) {
    // msgs — список сообщений за этот такт (обычно одно)

    // 1. Обновить модель (применить все сообщения последовательно)
    for (const msg of msgs) {
      model = app.update(msg, model)
    }

    // 2. Обновить подписки
    const newEvents = app.events(model)
    updateSubscriptions(currentEvents, newEvents)
    currentEvents = newEvents

    // 3. Перерендерить
    render()
  }

  // Примитивы вызывают tick со списком
  // interval: tick([null])
  // keyboard: tick([key])
  // request: tick([response])

  function render() {
    const newHtml = app.view(model)
    const patches = diff(previousHtml, newHtml)
    applyPatches(patches, rootElement, tick)  // tick для DOM events
    previousHtml = newHtml
  }

  function applyPatches(patches, element, tick) {
    for (const patch of patches) {
      switch (patch.type) {
        case 'replace':
          const newEl = createElement(patch.node, tick)
          element.parentNode.replaceChild(newEl, element)
          break

        case 'text':
          element.textContent = patch.value
          break

        case 'attrs':
          applyAttrs(element, patch.oldAttrs, patch.newAttrs, tick)
          break

        case 'children':
          applyChildPatches(element, patch.childPatches, tick)
          break
      }
    }
  }

  // Создание DOM элемента из Html
  function createElement(html, tick) {
    // text
    if (html.type === 'text') {
      return document.createTextNode(html.value)
    }

    // empty — не рендерить (возвращаем пустой комментарий как placeholder)
    if (html.type === 'empty') {
      return document.createComment('empty')
    }

    // fragment — создать DocumentFragment с детьми
    if (html.type === 'fragment') {
      const frag = document.createDocumentFragment()
      for (const child of html.children) {
        frag.appendChild(createElement(child, tick))
      }
      return frag
    }

    // node
    const el = document.createElement(html.tag)

    // Установить атрибуты и обработчики
    for (const attr of html.attrs) {
      applyAttr(el, attr, tick)
    }

    // Рекурсивно создать детей
    for (const child of html.children) {
      el.appendChild(createElement(child, tick))
    }

    return el
  }

  // Применение одного атрибута
  function applyAttr(element, attr, tick) {
    switch (attr.type) {
      // DOM события → вызывают tick
      case 'onClick':
        element.addEventListener('click', () => tick([attr.msg]))
        break

      case 'onInput':
        element.addEventListener('input', (e) => {
          const msg = attr.handler(e.target.value)  // handler : String → Msg
          tick([msg])
        })
        break

      case 'onKeyDown':
        element.addEventListener('keydown', (e) => {
          const key = parseKey(e)  // JS KeyboardEvent → Agda Key
          const msg = attr.handler(key)
          tick([msg])
        })
        break

      case 'onSubmit':
        element.addEventListener('submit', (e) => {
          e.preventDefault()
          tick([attr.msg])
        })
        break

      // Обычные атрибуты
      case 'className':
        element.className = attr.value
        break

      case 'id':
        element.id = attr.value
        break

      case 'disabled':
        element.disabled = attr.value
        break

      case 'value':
        element.value = attr.value
        break

      case 'checked':
        element.checked = attr.value
        break

      case 'style':
        for (const [prop, val] of attr.styles) {
          element.style[prop] = val
        }
        break

      // ... другие атрибуты
    }
  }

  // Конвертация JS Key в Agda Key
  function parseKey(event) {
    if (event.key.length === 1) {
      return { tag: 'Char', value: event.key }
    }
    switch (event.key) {
      case 'Enter': return { tag: 'Enter' }
      case 'Escape': return { tag: 'Escape' }
      case 'Tab': return { tag: 'Tab' }
      case 'Backspace': return { tag: 'Backspace' }
      case 'ArrowUp': return { tag: 'Arrow', value: { tag: 'Up' } }
      case 'ArrowDown': return { tag: 'Arrow', value: { tag: 'Down' } }
      case 'ArrowLeft': return { tag: 'Arrow', value: { tag: 'Left' } }
      case 'ArrowRight': return { tag: 'Arrow', value: { tag: 'Right' } }
      default: return { tag: 'Other', value: event.key }
    }
  }

  function updateSubscriptions(oldEvents, newEvents) {
    // Используем diffEvents из секции ниже
    diffEvents(
      oldEvents || { type: 'never' },
      newEvents,
      subscriptions,
      tick
    )
  }

  // === ИНИЦИАЛИЗАЦИЯ ===
  let previousHtml = null
  let rootElement = null

  function mount(selector) {
    rootElement = document.querySelector(selector)
    if (!rootElement) {
      throw new Error(`Element not found: ${selector}`)
    }

    // 1. Начальное состояние уже установлено: model = app.init

    // 2. Подписаться на начальные events
    currentEvents = app.events(model)
    subscribe(currentEvents, subscriptions, tick)

    // 3. Начальный рендер
    const html = app.view(model)
    rootElement.innerHTML = ''  // очистить
    rootElement.appendChild(createElement(html, tick))
    previousHtml = html
  }

  return { mount }
}

// Использование:
// const app = runApp(myApp)
// app.mount('#root')
```

### Точка входа

```agda
-- Main модуль
main : IO ⊤
main = runApp counterApp

-- Или с указанием DOM элемента
main = runAppIn "#app" counterApp
```

```javascript
// Скомпилированный JS
import { runApp } from './runtime'
import { counterApp } from './Counter.js'

runApp(counterApp, document.getElementById('app'))
```

### Управление подписками

Runtime сравнивает `events(oldModel)` и `events(newModel)`:

```
oldEvents = merge (interval 1000) never
newEvents = merge (interval 1000) (request (get "/api"))
                                   ^^^^^^^^^^^^^^^^^^^^
                                   новый Event → подписаться
```

```
oldEvents = merge (interval 1000) (request (get "/api"))
newEvents = merge (interval 1000) never
                                   ^^^^
                                   Event исчез → отписаться
```

### diffEvents псевдокод

```javascript
function diffEvents(oldEvent, newEvent, subscriptions, emit) {
  // Оба never — ничего не делать
  if (oldEvent.type === 'never' && newEvent.type === 'never') {
    return
  }

  // Был never, стал что-то — подписаться
  if (oldEvent.type === 'never' && newEvent.type !== 'never') {
    subscribe(newEvent, subscriptions, emit)
    return
  }

  // Был что-то, стал never — отписаться
  if (oldEvent.type !== 'never' && newEvent.type === 'never') {
    unsubscribe(oldEvent, subscriptions)
    return
  }

  // Оба merge — рекурсивно сравнить left и right
  if (oldEvent.type === 'merge' && newEvent.type === 'merge') {
    diffEvents(oldEvent.left, newEvent.left, subscriptions, emit)
    diffEvents(oldEvent.right, newEvent.right, subscriptions, emit)
    return
  }

  // Оба map/filter — сравнить source
  if ((oldEvent.type === 'map' && newEvent.type === 'map') ||
      (oldEvent.type === 'filter' && newEvent.type === 'filter')) {
    // Функции не сравниваем (считаем одинаковыми если структура та же)
    diffEvents(oldEvent.source, newEvent.source, subscriptions, emit)
    return
  }

  // Вспомогательная функция для сравнения аргументов
  function deepEqual(a, b) {
    if (a === b) return true
    if (typeof a !== typeof b) return false
    if (typeof a !== 'object' || a === null) return false
    if (Array.isArray(a) !== Array.isArray(b)) return false

    if (Array.isArray(a)) {
      if (a.length !== b.length) return false
      return a.every((item, i) => deepEqual(item, b[i]))
    }

    const keysA = Object.keys(a)
    const keysB = Object.keys(b)
    if (keysA.length !== keysB.length) return false
    return keysA.every(key => deepEqual(a[key], b[key]))
  }

  // Оба primitive — сравнить тип и аргументы
  if (oldEvent.type === 'primitive' && newEvent.type === 'primitive') {
    const same = oldEvent.primitive._type === newEvent.primitive._type &&
                 deepEqual(oldEvent.primitive._args, newEvent.primitive._args)
    if (same) {
      // Тот же примитив — ничего не делать
      return
    }
    // Разные — отписаться от старого, подписаться на новый
    unsubscribe(oldEvent, subscriptions)
    subscribe(newEvent, subscriptions, emit)
    return
  }

  // Структура изменилась — полная переподписка
  unsubscribe(oldEvent, subscriptions)
  subscribe(newEvent, subscriptions, emit)
}

function subscribe(event, subscriptions, emit) {
  if (event.type === 'never') return

  if (event.type === 'primitive') {
    const handle = event.primitive.subscribe((msgs) => {
      // Применить map/filter если есть обёртки
      emit(msgs)
    })
    subscriptions.set(event, handle)
    return
  }

  if (event.type === 'merge') {
    subscribe(event.left, subscriptions, emit)
    subscribe(event.right, subscriptions, emit)
    return
  }

  if (event.type === 'map') {
    subscribe(event.source, subscriptions, (msgs) => {
      emit(msgs.map(event.f))
    })
    return
  }

  if (event.type === 'filter') {
    subscribe(event.source, subscriptions, (msgs) => {
      emit(msgs.filter(event.p))
    })
    return
  }
}

function unsubscribe(event, subscriptions) {
  if (event.type === 'never') return

  if (event.type === 'primitive') {
    const handle = subscriptions.get(event)
    if (handle) {
      event.primitive.unsubscribe(handle)
      subscriptions.delete(event)
    }
    return
  }

  if (event.type === 'merge') {
    unsubscribe(event.left, subscriptions)
    unsubscribe(event.right, subscriptions)
    return
  }

  if (event.type === 'map' || event.type === 'filter') {
    unsubscribe(event.source, subscriptions)
    return
  }
}
```

### Идентификация Event

Для diff нужно идентифицировать Event. Варианты:

1. **Структурное сравнение** — сравнивать конструктор и аргументы
2. **Явные ключи** — `interval "timer1" 1000`

Для MVP — структурное сравнение:
- `interval 1000` == `interval 1000` → тот же Event
- `interval 1000` != `interval 500` → разные Event

### Представление Event в runtime

Event в runtime — это дерево:

```javascript
// Примитив (лист)
{ type: 'primitive', primitive: interval(1000) }

// merge (узел)
{ type: 'merge', left: Event, right: Event }

// mapE (узел)
{ type: 'map', f: Function, source: Event }

// filterE (узел)
{ type: 'filter', p: Function, source: Event }

// never (специальный лист)
{ type: 'never' }
```

Runtime обходит дерево для:
1. **Подписки** — находит все примитивы и подписывается
2. **Diff** — сравнивает деревья структурно
3. **Доставки событий** — применяет `map`/`filter` при получении

```javascript
// Пример: mapE GotData (request (get "/api"))
{
  type: 'map',
  f: GotData,
  source: {
    type: 'primitive',
    primitive: request({ method: 'get', url: '/api' })
  }
}
```

### Семантика выполнения

**Signal и Event ленивые** — вычисляются только когда runtime запрашивает значение.

Runtime не хранит бесконечные структуры в памяти. Вместо этого:
1. Хранит текущее состояние каждой активной подписки
2. При событии вызывает `now` для получения значения
3. `next` не вызывается явно — это концептуальная модель

```javascript
// Runtime не делает так:
const signal = foldp(f, init, events)
const val = signal.next.next.next.now  // ❌

// Runtime делает так:
let state = init
onEvent(msg => {
  state = f(msg, state)  // ✓ — обновляет состояние напрямую
})
```

Коиндуктивные определения в Agda — для **спецификации семантики**, не для прямого исполнения. Runtime реализует эквивалентное поведение императивно.

---

## 7. FFI

### Структура примитива

Каждый примитив Event реализуется через FFI:

```agda
-- Agda: объявление
postulate interval : ℕ → Event ⊤
```

```javascript
// JavaScript: реализация
const interval = (ms) => ({
  // Уникальный идентификатор для diff
  _type: 'interval',
  _args: [ms],

  // Вызывается при подписке
  subscribe: (emit) => {
    const id = setInterval(() => emit([null]), ms)
    return id  // возвращаем handle для отписки
  },

  // Вызывается при отписке
  unsubscribe: (id) => {
    clearInterval(id)
  }
})
```

### keyboard

```javascript
const keyboard = {
  _type: 'keyboard',
  _args: [],

  subscribe: (emit) => {
    const handler = (e) => {
      const key = parseKeyEvent(e)
      emit([key])
    }
    document.addEventListener('keydown', handler)
    return handler  // handle для отписки
  },

  unsubscribe: (handler) => {
    document.removeEventListener('keydown', handler)
  }
}

// Преобразование JS KeyboardEvent в Agda Key
function parseKeyEvent(e) {
  // Модификаторы
  let key = parseBaseKey(e.key)
  if (e.ctrlKey) key = { tag: 'Ctrl', value: key }
  if (e.altKey) key = { tag: 'Alt', value: key }
  if (e.shiftKey && e.key.length > 1) key = { tag: 'Shift', value: key }
  if (e.metaKey) key = { tag: 'Meta', value: key }
  return key
}

function parseBaseKey(keyStr) {
  if (keyStr.length === 1) {
    return { tag: 'Char', value: keyStr }
  }
  switch (keyStr) {
    case 'Enter': return { tag: 'Enter' }
    case 'Escape': return { tag: 'Escape' }
    case 'Tab': return { tag: 'Tab' }
    case 'Backspace': return { tag: 'Backspace' }
    case 'Delete': return { tag: 'Delete' }
    case 'ArrowUp': return { tag: 'Arrow', value: { tag: 'Up' } }
    case 'ArrowDown': return { tag: 'Arrow', value: { tag: 'Down' } }
    case 'ArrowLeft': return { tag: 'Arrow', value: { tag: 'Left' } }
    case 'ArrowRight': return { tag: 'Arrow', value: { tag: 'Right' } }
    case 'F1': case 'F2': case 'F3': case 'F4': case 'F5': case 'F6':
    case 'F7': case 'F8': case 'F9': case 'F10': case 'F11': case 'F12':
      return { tag: 'F', value: parseInt(keyStr.slice(1)) }
    default: return { tag: 'Other', value: keyStr }
  }
}
```

### request

```javascript
const request = (req) => ({
  _type: 'request',
  _args: [req.method, req.url, req.body],

  subscribe: (emit) => {
    const controller = new AbortController()
    let completed = false

    fetch(req.url, {
      method: req.method,
      body: req.body,
      signal: controller.signal
    })
    .then(resp => resp.json())
    .then(data => {
      if (!completed) {
        completed = true
        emit([{ tag: 'ok', status: 200, body: JSON.stringify(data) }])
      }
    })
    .catch(err => {
      if (!completed && err.name !== 'AbortError') {
        completed = true
        emit([{ tag: 'error', status: 0, msg: err.message }])
      }
    })

    return { controller, isCompleted: () => completed }
  },

  unsubscribe: (handle) => {
    if (!handle.isCompleted()) {
      handle.controller.abort()
    }
  }
})
```

**Одноразовость request:**

Request — одноразовый Event: после получения ответа он больше не генерирует событий.

Как это работает:
1. `subscribe` выполняет fetch и вызывает `emit` ровно один раз (с ответом или ошибкой)
2. После `emit` примитив молчит — больше не вызывает `emit`
3. Если приложение продолжает включать `request` в `events`, подписка остаётся активной, но событий больше нет
4. Когда приложение убирает `request` из `events` (например, `loading = false`), runtime вызывает `unsubscribe`

**Паттерн для повторного запроса:**
```agda
-- Чтобы сделать новый запрос, нужно убрать Event и добавить снова:
-- 1. loading = true → подписка на request
-- 2. ответ пришёл → update ставит loading = false
-- 3. loading = false → events = never → отписка
-- 4. Пользователь снова кликает → loading = true → новая подписка
```

Альтернатива — использовать уникальный идентификатор запроса:
```agda
-- Каждый запрос уникален
events m = if m.loading
  then mapE GotData (request (get ("/api?id=" ++ show m.requestId)))
  else never

-- При повторном запросе: requestId увеличивается
-- Runtime видит новый URL → новая подписка
```

### websocket

```javascript
// Хранилище активных соединений (по URL)
const wsConnections = new Map()

const websocket = (url) => {
  // Ленивое создание — соединение открывается при подписке на recv
  return {
    recv: {
      _type: 'websocket_recv',
      _args: [url],

      subscribe: (emit) => {
        // Создать или переиспользовать соединение
        let conn = wsConnections.get(url)
        if (!conn) {
          const ws = new WebSocket(url)
          conn = { ws, refCount: 0, emitters: new Set() }
          wsConnections.set(url, conn)

          ws.onopen = () => {
            conn.emitters.forEach(e => e([{ tag: 'Connected' }]))
          }
          ws.onmessage = (e) => {
            conn.emitters.forEach(e => e([{ tag: 'Message', value: e.data }]))
          }
          ws.onerror = (e) => {
            conn.emitters.forEach(e => e([{ tag: 'Error', value: e.message || 'Unknown error' }]))
          }
          ws.onclose = () => {
            conn.emitters.forEach(e => e([{ tag: 'Closed' }]))
            wsConnections.delete(url)
          }
        }

        conn.refCount++
        conn.emitters.add(emit)
        return { url, emit }
      },

      unsubscribe: (handle) => {
        const conn = wsConnections.get(handle.url)
        if (conn) {
          conn.emitters.delete(handle.emit)
          conn.refCount--
          if (conn.refCount <= 0) {
            conn.ws.close()
            wsConnections.delete(handle.url)
          }
        }
      }
    },

    send: (msg) => ({
      _type: 'websocket_send',
      _args: [url, msg],

      subscribe: (emit) => {
        const conn = wsConnections.get(url)
        if (conn && conn.ws.readyState === WebSocket.OPEN) {
          conn.ws.send(msg)
          emit([null])  // ⊤ = успех
        } else {
          // Соединение не открыто — подождать или ошибка
          // Для MVP: ждём открытия
          const checkAndSend = () => {
            const c = wsConnections.get(url)
            if (c && c.ws.readyState === WebSocket.OPEN) {
              c.ws.send(msg)
              emit([null])
            } else {
              setTimeout(checkAndSend, 10)
            }
          }
          checkAndSend()
        }
        return null  // нет handle для отписки
      },

      unsubscribe: () => {
        // Сообщение уже отправлено, ничего не делать
      }
    })
  }
}
```

**Ключевые моменты:**
- `websocket(url)` возвращает record с `recv` и `send`
- Соединение создаётся при первой подписке на `recv`
- Несколько подписчиков на один URL переиспользуют соединение (refCount)
- `send` ждёт открытия соединения если оно ещё не готово
- Соединение закрывается когда последний подписчик отписывается от `recv`

### Компиляция Event в JS-дерево

Agda определения компилируются в JS-структуры:

```agda
-- Agda: комбинаторы Event
never : Event A
merge : Event A → Event A → Event A
mapE  : (A → B) → Event A → Event B
```

```javascript
// JS: представление после компиляции
const never = { type: 'never' }

const merge = (e1) => (e2) => ({
  type: 'merge',
  left: e1,
  right: e2
})

const mapE = (f) => (e) => ({
  type: 'map',
  f: f,
  source: e
})

// Примитивы уже возвращают правильную структуру
const interval = (ms) => ({
  type: 'primitive',
  primitive: {
    _type: 'interval',
    _args: [ms],
    subscribe: ...,
    unsubscribe: ...
  }
})
```

**Пример компиляции:**

```agda
-- Agda
events m = if m.loading
  then mapE GotData (request (get "/api"))
  else never
```

```javascript
// JS после компиляции
const events = (m) =>
  m.loading
    ? mapE(GotData)(request(get("/api")))
    : never

// Что вычисляется в:
// m.loading = true →
// {
//   type: 'map',
//   f: GotData,
//   source: {
//     type: 'primitive',
//     primitive: { _type: 'request', _args: ['GET', '/api', null], ... }
//   }
// }
//
// m.loading = false →
// { type: 'never' }
```

Runtime вызывает `events(model)` каждый такт и получает дерево для diff.

### COMPILE прагмы

Связь между Agda postulate и JS реализацией:

```agda
-- В Primitive.agda
postulate
  interval : ℕ → Event ⊤

{-# COMPILE JS interval =
  function(ms) {
    return {
      _type: 'interval',
      _args: [ms],
      subscribe: function(emit) {
        return setInterval(function() { emit([null]); }, ms);
      },
      unsubscribe: function(id) {
        clearInterval(id);
      }
    };
  }
#-}
```

Для типов данных:

```agda
data Response : Set where
  ok    : Status → Body → Response
  error : Status → String → Response

{-# COMPILE JS Response = data
  | ok    = function(status, body) { return { tag: 'ok', status: status, body: body }; }
  | error = function(status, msg)  { return { tag: 'error', status: status, msg: msg }; }
#-}
```

---

## 8. Компиляция

### Схема

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   .agda     │ ──► │    Agda     │ ──► │     .js     │
│   код       │     │  --compile  │     │   модули    │
└─────────────┘     │    --js     │     └─────────────┘
                    └─────────────┘            │
                                               ▼
                                        ┌─────────────┐
                                        │   Runtime   │
                                        │   (JS)      │
                                        └─────────────┘
                                               │
                                               ▼
                                        ┌─────────────┐
                                        │   Bundle    │
                                        └─────────────┘
```

### Стандартные функции

Используемые функции из стандартной библиотеки Agda:

```agda
-- Data.List
_++_    : List A → List A → List A       -- конкатенация
map     : (A → B) → List A → List B      -- преобразование
filter  : (A → Bool) → List A → List A   -- фильтрация
foldr   : (A → B → B) → B → List A → B   -- правая свёртка
foldl   : (B → A → B) → B → List A → B   -- левая свёртка
length  : List A → ℕ                      -- длина
null    : List A → Bool                   -- пустой ли список

-- Data.Maybe
data Maybe A = Nothing | Just A
maybe   : B → (A → B) → Maybe A → B      -- деструктор

-- Data.Bool
not     : Bool → Bool
_&&_    : Bool → Bool → Bool
_||_    : Bool → Bool → Bool

-- Function
const   : A → B → A                       -- const x y = x
flip    : (A → B → C) → B → A → C
_∘_     : (B → C) → (A → B) → A → C      -- композиция
id      : A → A

-- Data.Nat
_+_     : ℕ → ℕ → ℕ
_*_     : ℕ → ℕ → ℕ
suc     : ℕ → ℕ
pred    : ℕ → ℕ                           -- pred 0 = 0

-- Data.String
_++_    : String → String → String
show    : {A : Set} → ⦃ Show A ⦄ → A → String
```

### Структура проекта

```
src/
  Agdelte/
    ├── Core/                    -- Ядро (обязательно)
    │   ├── Signal.agda          -- Signal, Functor, Applicative
    │   └── Event.agda           -- Event, комбинаторы, foldp
    │
    ├── Primitive/               -- IO-примитивы (по необходимости)
    │   ├── Interval.agda        -- interval : ℕ → Event ⊤
    │   ├── Keyboard.agda        -- keyboard : Event Key
    │   ├── Request.agda         -- request : Request → Event Response
    │   └── WebSocket.agda       -- websocket : Url → Event Message
    │
    ├── Concurrent/              -- Конкурентность (опционально)
    │   ├── Worker.agda          -- worker : WorkerFn A B → A → Event B
    │   ├── Pool.agda            -- WorkerPool, poolWorker
    │   ├── Parallel.agda        -- parallel, race, sequence
    │   └── Channel.agda         -- двунаправленная связь
    │
    ├── App.agda                 -- App record
    └── Html.agda                -- Html, Attr

runtime/
  index.js           -- runApp, event loop
  primitives.js      -- interval, request, websocket
  workers.js         -- worker runtime (опционально)
  dom.js             -- рендеринг Html в DOM
  diff.js            -- сравнение Event для подписок

examples/
  Counter.agda       -- только DOM events
  Clock.agda         -- interval
  Fetch.agda         -- request
  TodoMVC.agda       -- только DOM events
  ImageProcess.agda  -- worker (конкурентность)
```

**Модульность:** импортируйте только то, что нужно. Большинство UI-приложений не требуют `Concurrent/`.

---

## 9. Примеры

### TodoMVC

```agda
module TodoMVC where

-- Типы
record Todo : Set where
  field
    id        : ℕ
    text      : String
    completed : Bool

data Filter = All | Active | Completed

record Model : Set where
  field
    todos     : List Todo
    input     : String
    filter    : Filter
    nextId    : ℕ

data Msg : Set where
  NoOp          : Msg                     -- ничего не делать
  UpdateInput   : String → Msg
  AddTodo       : Msg
  ToggleTodo    : ℕ → Msg
  DeleteTodo    : ℕ → Msg
  SetFilter     : Filter → Msg
  ClearCompleted : Msg

-- App
todoApp : App Msg Model
todoApp = record
  { init   = { todos = []; input = ""; filter = All; nextId = 0 }

  ; update = λ where
      NoOp m → m                          -- игнорировать
      (UpdateInput s) m → record m { input = s }
      AddTodo m →
        if null (m .input) then m
        else record m
          { todos = m .todos ++ [ record { id = m .nextId; text = m .input; completed = false } ]
          ; input = ""
          ; nextId = suc (m .nextId)
          }
      (ToggleTodo id) m → record m { todos = map (toggle id) (m .todos) }
      (DeleteTodo id) m → record m { todos = filter (λ t → t .id /= id) (m .todos) }
      (SetFilter f) m → record m { filter = f }
      ClearCompleted m → record m { todos = filter (not ∘ completed) (m .todos) }

  ; view = viewTodoApp

  ; events = λ _ → never  -- только DOM events
  }
  where
    toggle : ℕ → Todo → Todo
    toggle id t = if t .id == id
                  then record t { completed = not (t .completed) }
                  else t

    -- Вспомогательные функции
    filterTodos : Filter → List Todo → List Todo
    filterTodos All ts = ts
    filterTodos Active ts = filter (not ∘ completed) ts
    filterTodos Completed ts = filter completed ts

    viewFilter : Filter → Filter → Html Msg
    viewFilter f current = li []
      [ a [ className (if f == current then "selected" else "")
          , onClick (SetFilter f)
          ] [ text (show f) ]
      ]

    viewTodo : Todo → Html Msg
    viewTodo t = li [ className (if t .completed then "completed" else "") ]
      [ div [ className "view" ]
          [ input [ className "toggle", type' "checkbox"
                  , checked (t .completed)
                  , onClick (ToggleTodo (t .id))
                  ] []
          , label [] [ text (t .text) ]
          , button [ className "destroy", onClick (DeleteTodo (t .id)) ] []
          ]
      ]

-- View (упрощённо)
viewTodoApp : Model → Html Msg
viewTodoApp m = div [ className "todoapp" ]
  [ header [ className "header" ]
      [ h1 [] [ text "todos" ]
      , input
          [ className "new-todo"
          , value (m .input)
          , onInput UpdateInput
          , onKeyDown (λ k → if k == Enter then AddTodo else NoOp)
          ] []
      ]
  , section [ className "main" ]
      [ ul [ className "todo-list" ]
          (map viewTodo (filterTodos (m .filter) (m .todos)))
      ]
  , footer [ className "footer" ]
      [ span [ className "todo-count" ]
          [ text (show (length (filter (not ∘ completed) (m .todos))) ++ " items left") ]
      , ul [ className "filters" ]
          [ viewFilter All m.filter
          , viewFilter Active m.filter
          , viewFilter Completed m.filter
          ]
      ]
  ]
```

### Fetch с обработкой ошибок

```agda
module FetchExample where

data Status = Idle | Loading | Success Data | Failure String

record Model : Set where
  field
    status : Status

data Msg : Set where
  FetchData  : Msg
  GotData    : Response → Msg

fetchApp : App Msg Model
fetchApp = record
  { init   = { status = Idle }

  ; update = λ where
      FetchData m → record m { status = Loading }
      (GotData (ok _ body)) m → record m { status = Success (parseData body) }
      (GotData (error _ msg)) m → record m { status = Failure msg }

  ; view = λ m → div []
      [ case m .status of λ where
          Idle → button [ onClick FetchData ] [ text "Load Data" ]
          Loading → div [ className "spinner" ] [ text "Loading..." ]
          (Success data) → viewData data
          (Failure msg) → div [ className "error" ]
              [ text ("Error: " ++ msg)
              , button [ onClick FetchData ] [ text "Retry" ]
              ]
      ]

  ; events = λ m → case m .status of λ where
      Loading → mapE GotData (request (get "/api/data"))
      _ → never
  }
```

### Polling (периодические запросы)

```agda
module Polling where

record Model : Set where
  field
    data       : Maybe Data
    polling    : Bool
    fetching   : Bool          -- идёт ли сейчас запрос

data Msg : Set where
  TogglePolling : Msg
  Tick          : Msg          -- пора делать запрос
  GotData       : Response → Msg

pollingApp : App Msg Model
pollingApp = record
  { init = { data = Nothing; polling = false; fetching = false }

  ; update = λ where
      TogglePolling m → record m { polling = not (m .polling) }
      Tick m → record m { fetching = true }   -- начать загрузку
      (GotData (ok _ body)) m → record m
        { data = Just (parse body)
        ; fetching = false                    -- загрузка завершена
        }
      (GotData _) m → record m { fetching = false }

  ; view = λ m → div []
      [ button [ onClick TogglePolling ]
          [ text (if m .polling then "Stop" else "Start") ]
      , maybe (text "No data") viewData (m .data)
      ]

  ; events = λ m → merge
      -- Таймер: тикает пока polling=true
      (if m .polling then mapE (const Tick) (interval 5000) else never)
      -- Запрос: выполняется пока fetching=true
      (if m .fetching then mapE GotData (request (get "/api")) else never)
  }
```

**Логика:**
1. `polling=true` → подписка на `interval` → каждые 5 сек приходит `Tick`
2. `Tick` → `fetching := true`
3. `fetching=true` → подписка на `request` → запрос уходит
4. Ответ приходит → `GotData` → `fetching := false` → отписка от `request`
5. Через 5 сек снова `Tick` → цикл повторяется

---

## 10. Тестирование

### Тестирование update

`update` — чистая функция, тестируется напрямую:

```agda
test_increment : update Inc 0 ≡ 1
test_increment = refl

test_decrement : update Dec 5 ≡ 4
test_decrement = refl
```

### Тестирование с событиями

Можно создать "фейковые" Event и проверить поведение:

```agda
-- Симулировать последовательность событий
simulate : App Msg Model → List Msg → Model
simulate app msgs = foldl (flip app.update) app.init msgs

test_counter : simulate counterApp [Inc, Inc, Dec] ≡ 1
test_counter = refl
```

### Property-based тестирование

```agda
-- Счётчик всегда ≥ 0 (если не уходим в минус)
prop_non_negative : ∀ msgs →
  all (λ m → m ≡ Inc) msgs →
  simulate counterApp msgs ≥ 0
```

---

## 11. Отладка

### Логирование событий

Runtime может логировать все события и состояния:

```javascript
function runApp(app, options = {}) {
  const debug = options.debug || false

  function tick(msgs) {
    if (debug) {
      console.group('Tick')
      console.log('Messages:', msgs)
      console.log('Model before:', model)
    }

    for (const msg of msgs) {
      model = app.update(msg, model)
    }

    if (debug) {
      console.log('Model after:', model)
      console.groupEnd()
    }
    // ...
  }
}
```

### Time-travel debugging (Phase 2+)

Сохранение истории для отката:

```javascript
const history = []
let historyIndex = -1

function tick(msgs) {
  // Сохранить состояние перед изменением
  history.push({ model, msgs })
  historyIndex = history.length - 1
  // ...
}

// Откат
function timeTravel(index) {
  historyIndex = index
  model = history[index].model
  render()
}
```

Возможно благодаря чистоте `update` — состояние полностью определяется историей событий.

### Инспектор состояния

Визуализация Model в DevTools:

```javascript
// Экспорт для браузерных DevTools
window.__AGDELTE_DEVTOOLS__ = {
  getModel: () => model,
  getHistory: () => history,
  dispatch: (msg) => tick([msg])
}
```

---

## 12. Обоснования решений (Rationale)

### Почему Signal — coinductive record?

**Альтернатива:** индуктивный тип (конечный список) или функция `ℕ → A`.

**Решение:** coinductive record.

**Причины:**
- Signal концептуально бесконечен (значение существует в любой момент времени)
- Coinduction позволяет определять бесконечные структуры без явной рекурсии
- Record с полями `now`/`next` даёт удобный доступ к текущему значению и продолжению
- Agda хорошо поддерживает coinductive records с copattern matching

```agda
-- Copattern matching — естественный способ определения
map f s .now  = f (s .now)
map f s .next = map f (s .next)
```

### Почему Event = Signal (List A), а не Signal (Maybe A)?

**Альтернатива:** `Event A = Signal (Maybe A)` — либо есть событие, либо нет.

**Решение:** `Event A = Signal (List A)` — список событий за такт.

**Причины:**
- За один такт может произойти несколько событий (два клика, несколько сообщений WebSocket)
- `List` естественно обрабатывает 0, 1 или много событий
- `merge` становится простым `++`
- `foldp` корректно обрабатывает несколько событий за такт через `foldr`

```agda
-- С Maybe: потеря событий при merge
merge (Just a) (Just b) = ???  -- что выбрать?

-- С List: всё сохраняется
merge [a] [b] = [a, b]
```

### Почему всё IO через Event?

**Альтернатива:** отдельный тип `Cmd` для команд (как в Elm).

**Решение:** всё IO — это `Event`. HTTP запрос — источник событий.

**Причины:**
- **Унификация:** один механизм для таймеров, HTTP, WebSocket, keyboard
- **Простота:** меньше типов, меньше концепций
- **Декларативность:** "пока `loading = true`, слушай этот источник" вместо "отправь запрос"
- **Автоматическая отмена:** Event исчез из `events` → отписка → отмена запроса
- **Связь с линейностью:** ресурс (подписка) существует ровно пока нужен

```agda
-- Elm: императивно
update FetchData m = (m, Http.get ...)

-- Agdelte: декларативно
events m = if m.loading then request (get ...) else never
```

### Почему events зависит от Model?

**Альтернатива:** статические события `events : Event Msg`.

**Решение:** `events : Model → Event Msg`.

**Причины:**
- Динамическое включение/выключение источников событий
- HTTP запрос по условию (`if loading then request ... else never`)
- WebSocket только когда нужен
- Polling можно включать/выключать
- Runtime автоматически управляет подписками при изменении Model

```agda
-- Статические: всегда слушаем всё
events = merge (interval 1000) (request ...)

-- Динамические: слушаем по необходимости
events m = if m.polling then interval 1000 else never
```

### Почему update чистый (без Cmd)?

**Альтернатива:** `update : Msg → Model → Model × Cmd Msg` (как в Elm).

**Решение:** `update : Msg → Model → Model` — чистая функция без побочных эффектов.

**Причины:**
- **Простота:** update только обновляет состояние
- **Тестируемость:** чистая функция легко тестируется
- **Разделение ответственности:** состояние в `update`, эффекты в `events`
- **Cmd не нужен:** эффекты выражаются через `events(model)`

```agda
-- Elm: эффект в update
update FetchData m = ({ m | loading = true }, Http.get ...)

-- Agdelte: эффект следует из состояния
update FetchData m = { m | loading = true }
events m = if m.loading then request ... else never
```

### Почему декларативные подписки?

**Альтернатива:** императивное управление — `subscribe`, `unsubscribe`.

**Решение:** декларативное — `events` описывает *что* слушать, runtime управляет *как*.

**Причины:**
- **Нет утечек:** невозможно забыть отписаться
- **Идемпотентность:** одинаковый `events(model)` = одинаковые подписки
- **Простота:** не нужно отслеживать состояние подписок вручную
- **Связь с линейностью:** ресурсы автоматически освобождаются

```agda
-- Императивно: легко забыть отписаться
onMount = subscribe(interval 1000)
onUnmount = unsubscribe(???)  -- где взять handle?

-- Декларативно: автоматически
events m = if m.active then interval 1000 else never
-- Runtime сам управляет подписками
```

### Почему нет отдельного типа Sub?

**Альтернатива:** `Sub Msg` для подписок (как в Elm), отдельно от `Cmd Msg`.

**Решение:** всё унифицировано через `Event`.

**Причины:**
- **Меньше типов:** Event покрывает и "подписки" и "команды"
- **Единообразие:** interval и request — оба Event
- **Композиция:** один `merge` для всего, не `Sub.batch` + `Cmd.batch`
- **Концептуальная ясность:** всё — входящие события

```agda
-- Elm: два типа
subscriptions m = Time.every 1000 Tick
update Fetch m = (m, Http.get ...)

-- Agdelte: один тип
events m = merge
  (map (const Tick) (interval 1000))
  (if m.fetching then map GotData (request ...) else never)
```

### Почему примитивы — postulate?

**Альтернатива:** реализовать примитивы в Agda.

**Решение:** `postulate` с FFI реализацией.

**Причины:**
- Примитивы требуют взаимодействия с внешним миром (таймеры, HTTP)
- Agda компилируется в JS — FFI естественен
- `postulate` чётко отмечает границу чистого/нечистого кода
- Runtime на JS эффективен и имеет доступ к браузерным API

```agda
-- Объявление в Agda
postulate interval : ℕ → Event ⊤

-- Реализация в JS
{-# COMPILE JS interval = ... #-}
```

---

## 13. Расширения

Базовая архитектура покрывает большинство UI-задач:
- Интерактивные формы, списки, навигация — только DOM events
- Периодические обновления — `interval`
- Загрузка данных — `request`
- Real-time — `websocket`

### Когда нужны расширения?

| Задача | Решение |
|--------|---------|
| Тяжёлые вычисления (> 16мс) | `Concurrent/Worker` |
| Параллельная обработка | `Concurrent/Parallel` |
| Обработка больших данных | `Concurrent/Worker` + SharedArrayBuffer |

### Доступные расширения

**Конкурентность** (`arch-concurrency.md`):
- `worker` — вычисления в Web Worker как Event
- `parallel`, `race` — комбинаторы параллелизма
- `WorkerPool` — переиспользование worker'ов
- `Channel` — двунаправленная связь

Принцип расширений: **тот же паттерн Event**.

```agda
-- Базовый примитив
request   : Request → Event Response

-- Расширение (та же модель)
worker    : WorkerFn A B → A → Event B
```

Worker — это "ещё один примитив Event". Декларативная модель, управление подписками, композиция через `merge` — всё работает одинаково.

---

## Итого

| Компонент | Роль |
|-----------|------|
| **Signal** | Значения во времени (Functor, Applicative) |
| **Event** | События (Signal (List A)) |
| **Примитивы** | Источники Event из внешнего мира |
| **App** | Структура приложения |
| **Html** | Типизированный DOM |
| **Runtime** | Event loop, подписки, рендеринг |
| **FFI** | Реализация примитивов на JS |
| **Расширения** | Конкурентность и др. (опционально) |

Ключевой принцип: **всё IO — это Event**. Приложение — чистые функции, эффекты только через подписки на Event.

### Философия дизайна

1. **Унификация** — один механизм вместо нескольких (Event вместо Cmd + Sub)
2. **Декларативность** — описываем *что*, не *как*
3. **Чистота** — эффекты на границе, внутри только чистые функции
4. **Простота** — минимум концепций, максимум выразительности
