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

### Модель времени

Agdelte использует **дискретное время** по образцу игровых движков, а не непрерывное время классического FRP (Conal Elliott).

#### Почему не непрерывное время?

Классический FRP определяет:

```haskell
type Behavior a = Time → a  -- Time ∈ ℝ (непрерывное)
```

**Проблемы непрерывного времени:**

| Проблема | Описание |
|----------|----------|
| Невычислимость | Компьютер дискретен — непрерывное время это иллюзия |
| Time leaks | `Behavior` может требовать всю историю значений |
| Неопределённость | Когда именно вычислять? При каждом событии? 60 FPS? |
| Накопление thunks | Ленивость приводит к утечкам памяти |

**Решение Agdelte:** время дискретно, такт — атомарная единица.

```
Непрерывное (Conal Elliott):     Дискретное (Agdelte):

  Behavior a = Time → a            Signal a = now + next
  "значение в КАЖДЫЙ момент"       "значение в КАЖДЫЙ ТАКТ"

  Реальность: сэмплируем           Реальность: именно так
  в дискретные моменты             и вычисляем
```

#### Уровни времени

```
┌─────────────────────────────────────────────────────────────┐
│                  Agdelte Time Architecture                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Level 1: Logical Time (такты)                              │
│  ─────────────────────────────                              │
│  • Событие = один такт                                      │
│  • UI: клики, input, HTTP, WebSocket                        │
│  • Между событиями — idle (эффективно!)                     │
│  • Примитивы: interval, keyboard, request                   │
│                                                              │
│  Level 2: Frame Time (кадры)                                │
│  ─────────────────────────────                              │
│  • requestAnimationFrame                                     │
│  • dt = миллисекунды с прошлого кадра                       │
│  • Для: CSS-анимации, transitions, плавные эффекты          │
│  • Примитив: animationFrame                                  │
│                                                              │
│  Level 3: Physics Time (фиксированный шаг)                  │
│  ─────────────────────────────────────────                  │
│  • Фиксированный dt (например, 16ms = 60Hz)                 │
│  • Детерминизм: одинаковый input → одинаковый результат     │
│  • Для: игры, симуляции, физика                             │
│  • Модуль: Agdelte.Physics                                   │
│                                                              │
│  Level 4: Continuous Time — НЕТ                             │
│  ──────────────────────────────                             │
│  • Аппроксимируется через Level 2/3                         │
│  • "Интеграл" = сумма по dt                                 │
│  • Это честно, и это работает                               │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### Примитив animationFrame

```agda
-- Событие на каждый кадр браузера (~60 FPS)
animationFrame : Event FrameInfo

record FrameInfo : Set where
  field
    dt  : ℕ    -- миллисекунды с прошлого кадра (обычно 16-17)
    fps : ℕ    -- текущий FPS (вычисляется runtime)
```

**Использование:**

```agda
data Msg = Tick FrameInfo | StartAnimation | StopAnimation

record Model : Set where
  field
    position  : ℕ      -- пиксели
    velocity  : ℕ      -- пиксели/секунду
    animating : Bool

app : App Msg Model
app = record
  { init = { position = 0; velocity = 200; animating = false }

  ; update = λ where
      (Tick frame) m → record m
        { position = m.position + m.velocity * frame.dt / 1000 }
      StartAnimation m → record m { animating = true }
      StopAnimation m → record m { animating = false }

  ; view = λ m → div []
      [ div [ style [("transform", "translateX(" ++ show m.position ++ "px)")] ]
          [ text "●" ]
      , text ("FPS: " ++ show frame.fps)
      , button [ onClick (if m.animating then StopAnimation else StartAnimation) ]
          [ text (if m.animating then "Stop" else "Start") ]
      ]

  ; events = λ m →
      if m.animating
      then mapE Tick animationFrame
      else never  -- не крутим цикл без необходимости
  }
```

**Ключевое:** когда `animating = false`, события не генерируются — браузер idle, батарея не тратится.

#### Fixed Timestep (для игр и физики)

Проблема variable timestep:

```
Frame 1: dt = 16ms  → position += velocity * 0.016
Frame 2: dt = 100ms → position += velocity * 0.100  // лаг!
         ↑
    Объект "пролетает" сквозь стену
```

Решение — fixed timestep (как в игровых движках):

```agda
module Agdelte.Physics where

-- Фиксированная частота физики
PHYSICS_HZ : ℕ
PHYSICS_HZ = 60

FIXED_DT : ℕ
FIXED_DT = 1000 / PHYSICS_HZ  -- 16ms

-- Состояние физической симуляции
record PhysicsModel (A : Set) : Set where
  field
    current     : A      -- текущее состояние (после последнего шага)
    previous    : A      -- предыдущее (для интерполяции рендеринга)
    accumulator : ℕ      -- накопленное время

-- Шаг физики (ВСЕГДА вызывается с одинаковым dt!)
PhysicsStep : Set → Set
PhysicsStep A = A → A

-- Обновление: может выполнить 0, 1 или несколько шагов физики
updatePhysics : PhysicsStep A → ℕ → PhysicsModel A → PhysicsModel A
updatePhysics step dt model = go (record model { accumulator = model.accumulator + dt })
  where
    go : PhysicsModel A → PhysicsModel A
    go m = if m.accumulator >= FIXED_DT
           then go (record m
             { current = step (m.current)
             ; previous = m.current
             ; accumulator = m.accumulator - FIXED_DT
             })
           else m

-- Интерполяция для плавного рендеринга между шагами физики
interpolate : Lerp A → PhysicsModel A → A
interpolate lerp m =
  let alpha = m.accumulator * 1000 / FIXED_DT  -- 0..1000
  in lerp (m.previous) (m.current) alpha

-- Typeclass для интерполяции
Lerp : Set → Set
Lerp A = A → A → ℕ → A  -- from → to → alpha(0-1000) → result
```

**Пример: прыгающий мяч**

```agda
record Ball : Set where
  field
    y  : ℤ    -- позиция (миллиметры для точности)
    vy : ℤ    -- скорость (мм/с)

GRAVITY : ℤ
GRAVITY = -9800  -- мм/с² (ускорение свободного падения)

-- Один шаг физики (dt = FIXED_DT = 16ms)
ballStep : PhysicsStep Ball
ballStep b =
  let newVy = b.vy + GRAVITY * FIXED_DT / 1000
      newY  = b.y + newVy * FIXED_DT / 1000
      -- Отскок от земли (y = 0)
      (y', vy') = if newY < 0
                  then (0, negate newVy * 80 / 100)  -- 80% энергии сохраняется
                  else (newY, newVy)
  in record { y = y'; vy = vy' }

-- Линейная интерполяция для рендеринга
lerpBall : Lerp Ball
lerpBall a b alpha = record
  { y  = a.y + (b.y - a.y) * alpha / 1000
  ; vy = b.vy  -- скорость не интерполируем
  }

-- Приложение
data Msg = Frame FrameInfo | Drop

record Model : Set where
  field
    physics : PhysicsModel Ball
    running : Bool

ballApp : App Msg Model
ballApp = record
  { init =
      { physics = { current = { y = 5000; vy = 0 }
                  ; previous = { y = 5000; vy = 0 }
                  ; accumulator = 0 }
      ; running = false
      }

  ; update = λ where
      (Frame f) m → record m { physics = updatePhysics ballStep f.dt m.physics }
      Drop m → record m
        { physics = resetPhysics { y = 5000; vy = 0 }
        ; running = true
        }

  ; view = λ m →
      let ball = interpolate lerpBall m.physics
          yPx = ball.y / 10  -- мм → пиксели
      in div [ className "game" ]
        [ div [ className "ball"
              , style [("bottom", show yPx ++ "px")]
              ] [ text "🔴" ]
        , button [ onClick Drop ] [ text "Drop Ball" ]
        , text ("FPS: " ++ show (getLastFps m))
        ]

  ; events = λ m →
      if m.running
      then mapE Frame animationFrame
      else never
  }
```

**Преимущества fixed timestep:**

| Свойство | Variable dt | Fixed dt |
|----------|-------------|----------|
| Детерминизм | ❌ Зависит от FPS | ✅ Всегда одинаково |
| Replay | ❌ Нужно сохранять dt | ✅ Только input |
| Стабильность | ❌ Глитчи при лагах | ✅ Физика не ломается |
| Сетевая игра | ❌ Рассинхрон | ✅ Lockstep возможен |

#### Сравнение с другими FRP-системами

| Система | Модель времени | Комментарий |
|---------|----------------|-------------|
| Fran (Conal Elliott) | Непрерывное | Красиво математически, проблемы на практике |
| Yampa | Дискретное (SF) | Signal Functions, нет time leaks |
| Reflex | Дискретное | Spider timeline, практичный |
| Elm | Дискретное | Такты по событиям |
| Игровые движки | Fixed timestep | Индустриальный стандарт |
| **Agdelte** | **Дискретное + fixed** | Такты + опциональный fixed timestep |

#### Итог

```
Событийное время (UI):     Кадровое время (анимации):    Физическое время (игры):

  Event ───► Такт            animationFrame               Fixed timestep
     │                            │                            │
     ▼                            ▼                            ▼
  update                    update(dt)                   updatePhysics(dt)
  render                      render                    interpolate + render
     │                            │                            │
     ▼                            ▼                            ▼
   idle                    requestAnimationFrame         while(acc >= FIXED_DT)
 (ждём событие)              (следующий кадр)              step(FIXED_DT)
```

**Философия:** время дискретно на всех уровнях. Непрерывное время — полезная абстракция для математики, но не для реализации.

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

### Sampling комбинаторы

Комбинаторы для взаимодействия Event и Signal. Взяты из Sodium и Reactive-banana.

```agda
-- snapshot: при событии A взять текущее значение Signal B, применить f
snapshot : (A → B → C) → Event A → Signal B → Event C
snapshot f e s .now  = List.map (λ a → f a (s .now)) (e .now)
snapshot f e s .next = snapshot f (e .next) (s .next)

-- attach: при событии приложить текущее значение Signal
attach : Event A → Signal B → Event (A × B)
attach = snapshot _,_

-- tag: при событии взять текущее значение Signal (игнорируя значение события)
tag : Signal A → Event B → Event A
tag s e = snapshot (λ _ a → a) e s

-- sample: синоним tag с другим порядком аргументов
sample : Event A → Signal B → Event B
sample e s = snapshot (λ _ b → b) e s

-- gate: пропускать события только когда Signal Bool = true
gate : Event A → Signal Bool → Event A
gate e s .now  = if s .now then e .now else []
gate e s .next = gate (e .next) (s .next)
```

**Примеры использования:**

```agda
-- 1. При клике на "Save" взять текущий текст из поля ввода
saveClicks : Event ⊤
currentText : Signal String

savedText : Event String
savedText = tag currentText saveClicks
-- или: savedText = sample saveClicks currentText

-- 2. При отправке формы собрать все поля
data FormData : Set where
  mkForm : String → String → FormData

submitEvent : Event ⊤
nameSignal : Signal String
emailSignal : Signal String

formSubmit : Event FormData
formSubmit = snapshot (λ _ name →
               snapshot (λ _ email → mkForm name email)
                        submitEvent emailSignal)
             submitEvent nameSignal

-- Или элегантнее с Applicative:
formSubmit = tag (pure mkForm <*> nameSignal <*> emailSignal) submitEvent

-- 3. Клики только когда кнопка активна
rawClicks : Event ⊤
isEnabled : Signal Bool

activeClicks : Event ⊤
activeClicks = gate rawClicks isEnabled

-- 4. Применить текущую операцию к данным события
currentOp : Signal (ℕ → ℕ)  -- например, (*2) или (+10)
numbers : Event ℕ

processed : Event ℕ
processed = snapshot (λ n f → f n) numbers currentOp
```

### Детекция изменений

```agda
-- changes: генерирует событие когда Signal меняет значение
changes : ⦃ Eq A ⦄ → Signal A → Event A
changes s .now  = []  -- в первый такт нет "изменения"
changes s .next .now  = if s .now ≡ s .next .now
                        then []
                        else [ s .next .now ]
changes s .next .next = changes (s .next) .next

-- Альтернативная реализация через zip
changes' : ⦃ Eq A ⦄ → Signal A → Event A
changes' s = filterE (uncurry (_≠_)) (attach (drop 1 (toEvent s)) s)
  where
    drop : ℕ → Event A → Event A
    drop 0 e = e
    drop (suc n) e = drop n (e .next)

    toEvent : Signal A → Event A
    toEvent s .now = [ s .now ]
    toEvent s .next = toEvent (s .next)
```

**Пример: реагировать только на изменение выбранной вкладки**

```agda
data Tab = Tab1 | Tab2 | Tab3

currentTab : Signal Tab

-- БЕЗ changes: обработчик вызывается каждый такт
-- tabEvents = mapE handle (toEvent currentTab)  -- плохо!

-- С changes: только при реальном изменении
tabChanged : Event Tab
tabChanged = changes currentTab

-- Загрузить данные при переключении вкладки
events m = merge
  (mapE LoadTabData tabChanged)  -- только при изменении
  (otherEvents m)
```

### Дополнительные комбинаторы

```agda
-- split: разделить Event (Either A B) на два Event
split : Event (Either A B) → Event A × Event B
split e = (filterMap leftToMaybe e , filterMap rightToMaybe e)
  where
    leftToMaybe : Either A B → Maybe A
    leftToMaybe (Left a) = Just a
    leftToMaybe (Right _) = Nothing

    rightToMaybe : Either A B → Maybe B
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right b) = Just b

-- filterMap: map + filter в одном (как mapMaybe)
filterMap : (A → Maybe B) → Event A → Event B
filterMap f e .now  = List.mapMaybe f (e .now)
filterMap f e .next = filterMap f (e .next)

-- fan: разделить по функции (обобщение split)
fan : Event A → (A → Either B C) → Event B × Event C
fan e f = split (mapE f e)

-- leftmost: взять первое событие из списка (приоритет слева)
leftmost : List (Event A) → Event A
leftmost [] = never
leftmost (e ∷ es) .now = case e .now of
  [] → leftmost es .now
  xs → xs  -- нашли события, остальные игнорируем
leftmost (e ∷ es) .next = leftmost (e .next ∷ List.map next es)

-- difference: события из первого, которых нет во втором (по значению)
difference : ⦃ Eq A ⦄ → Event A → Event A → Event A
difference e1 e2 .now  = filter (λ a → not (elem a (e2 .now))) (e1 .now)
difference e1 e2 .next = difference (e1 .next) (e2 .next)
```

### Time-based комбинаторы

Комбинаторы для работы с временными задержками. Критически важны для UI.

```agda
-- debounce: событие только после паузы в N мс
-- Если новое событие приходит до истечения таймера — таймер сбрасывается
debounce : ℕ → Event A → Event A

-- throttle: максимум одно событие за N мс
-- Первое событие проходит сразу, следующие игнорируются до истечения периода
throttle : ℕ → Event A → Event A

-- delay: задержка события на N мс
delay : ℕ → Event A → Event A

-- timeout: событие ⊤ если ничего не пришло за N мс
timeout : ℕ → Event A → Event ⊤

-- after: событие через N мс после исходного
after : ℕ → Event A → Event A
```

**Семантика debounce:**

```
Входные события:  [a]  []  [b]  []  []  []  [c]  []  []  []  []  []
Время (мс):        0   16   32  48  64  80  96  112 128 144 160 176
                   ↑        ↑                ↑
                   │        │                └─ сброс таймера
                   │        └─ сброс таймера
                   └─ старт таймера

debounce 50:      []  []  []  []  []  []  []  []  []  []  [c]  []
                                                          ↑
                                               50мс после последнего события
```

**Семантика throttle:**

```
Входные события:  [a]  [b]  [c]  []  []  []  [d]  [e]  []  []
Время (мс):        0   16   32  48  64  80  96  112 128 144
                   ↑    ↓    ↓              ↑    ↓
                   │    │    │              │    └─ игнорируется
                   │    │    │              └─ проходит (период истёк)
                   │    │    └─ игнорируется
                   │    └─ игнорируется
                   └─ проходит, старт периода

throttle 50:      [a]  []  []  []  []  []  [d]  []  []  []
```

**FFI реализация:**

```javascript
const debounce = (ms) => (event) => ({
  _type: 'debounce',
  _args: [ms, event],

  subscribe: (emit) => {
    let timerId = null
    let lastValue = null

    const innerUnsub = event.subscribe((values) => {
      if (values.length > 0) {
        lastValue = values[values.length - 1]  // берём последнее

        if (timerId) clearTimeout(timerId)
        timerId = setTimeout(() => {
          emit([lastValue])
          timerId = null
        }, ms)
      }
    })

    return { innerUnsub, timerId }
  },

  unsubscribe: ({ innerUnsub, timerId }) => {
    if (timerId) clearTimeout(timerId)
    innerUnsub()
  }
})

const throttle = (ms) => (event) => ({
  _type: 'throttle',
  _args: [ms, event],

  subscribe: (emit) => {
    let lastEmit = 0

    const innerUnsub = event.subscribe((values) => {
      const now = performance.now()
      if (values.length > 0 && now - lastEmit >= ms) {
        emit([values[0]])  // берём первое
        lastEmit = now
      }
    })

    return innerUnsub
  },

  unsubscribe: (innerUnsub) => innerUnsub()
})
```

**Пример: поиск с debounce**

```agda
data Msg = UpdateQuery String | Search String | GotResults (List Result)

record Model : Set where
  field
    query    : String
    results  : List Result
    loading  : Bool

app : App Msg Model
app = record
  { init = { query = ""; results = []; loading = false }

  ; update = λ where
      (UpdateQuery q) m → record m { query = q }
      (Search q) m → record m { loading = true }
      (GotResults rs) m → record m { loading = false; results = rs }

  ; view = λ m → div []
      [ input [ value (m .query)
              , onInput UpdateQuery
              , placeholder "Search..."
              ] []
      , if m .loading
        then text "Searching..."
        else ul [] (map viewResult (m .results))
      ]

  ; events = λ m →
      let queryChanges = changes (pure (m .query))  -- Signal → Event
          debouncedQuery = debounce 300 queryChanges  -- ждём 300мс паузы
      in merge
        (mapE Search debouncedQuery)
        (if m .loading
         then mapE GotResults (request (searchApi (m .query)))
         else never)
  }
```

**Пример: throttle для scroll**

```agda
-- Обновлять позицию скролла максимум 60 раз в секунду
scrollPosition : Event ℕ
scrollPosition = throttle 16 rawScrollEvents  -- ~60 FPS
```

### Switching комбинаторы

Динамическое переключение между Event/Signal. Идея из Reflex и Sodium.

```agda
-- switchE: переключиться на новый Event при каждом событии
switchE : Event A → Event (Event A) → Event A

-- Семантика:
-- Начинаем со первого Event
-- При событии во втором — переключаемся на Event из этого события
-- Старый Event отписывается, новый подписывается

switchE initial switch .now =
  case switch .now of
    []       → initial .now
    (e ∷ _)  → e .now  -- переключились на новый Event
switchE initial switch .next =
  case switch .now of
    []       → switchE (initial .next) (switch .next)
    (e ∷ _)  → switchE (e .next) (switch .next)

-- switchB / switchS: переключение Signal
switchS : Signal A → Event (Signal A) → Signal A
switchS initial switch .now = initial .now
switchS initial switch .next =
  case switch .now of
    []       → switchS (initial .next) (switch .next)
    (s ∷ _)  → switchS s (switch .next)  -- новый Signal

-- switcher: удобный синоним для switchS
switcher : Signal A → Event (Signal A) → Signal A
switcher = switchS

-- switchDyn: для Dynamic
switchDyn : Dynamic A → Event (Dynamic A) → Dynamic A

-- join для Event (безопасный — не вызывает time leaks)
coincidence : Event (Event A) → Event A
-- При событии внешнего Event — взять текущие события внутреннего
coincidence ee .now = case ee .now of
  []       → []
  (e ∷ es) → e .now ++ concatMap (.now) es
coincidence ee .next = coincidence (ee .next)

-- switchHold: переключиться и держать
switchHold : Event A → Event (Event A) → Event A
switchHold = switchE
```

**Пример: вкладки с разными источниками событий**

```agda
data Tab = Users | Posts | Settings
data Msg = SelectTab Tab | TabMsg TabMsg | ...

-- Каждая вкладка имеет свои события
usersEvents   : Model → Event TabMsg
postsEvents   : Model → Event TabMsg
settingsEvents : Model → Event TabMsg

-- Выбрать события для текущей вкладки
currentTabEvents : Tab → Model → Event TabMsg
currentTabEvents Users m    = usersEvents m
currentTabEvents Posts m    = postsEvents m
currentTabEvents Settings m = settingsEvents m

-- Переключение при смене вкладки
events m =
  let tabChange = changes (pure (m .currentTab))
      switched = switchE
        (currentTabEvents (m .currentTab) m)
        (mapE (λ tab → currentTabEvents tab m) tabChange)
  in mapE TabMsg switched
```

**Пример: форма с динамическими полями**

```agda
-- Тип формы меняется в зависимости от выбора
data FormType = Simple | Advanced

simpleFormEvents : Event FormMsg
advancedFormEvents : Event FormMsg  -- больше полей, валидация

formEvents : Signal FormType → Event FormMsg
formEvents formType = switchE
  simpleFormEvents
  (mapE selectForm (changes formType))
  where
    selectForm Simple   = simpleFormEvents
    selectForm Advanced = advancedFormEvents
```

**Пример: переключение WebSocket соединений**

```agda
-- При смене сервера — переподключиться
data Msg = SelectServer Url | WsMsg WsEvent

currentWs : Signal Url → Event WsEvent
currentWs serverUrl = switchE
  (websocket (serverUrl .now) .recv)                    -- начальный
  (mapE (λ url → websocket url .recv) (changes serverUrl))  -- при смене
```

### Merging комбинаторы

Разные стратегии объединения событий.

```agda
-- Текущий merge: конкатенация списков
merge : Event A → Event A → Event A
merge e1 e2 .now = e1 .now ++ e2 .now

-- mergeWith: объединить одновременные события функцией
mergeWith : (A → A → A) → Event A → Event A → Event A
mergeWith f e1 e2 .now = case (e1 .now, e2 .now) of
  ([], [])     → []
  (xs, [])     → xs
  ([], ys)     → ys
  (x ∷ _, y ∷ _) → [ f x y ]  -- объединяем первые
mergeWith f e1 e2 .next = mergeWith f (e1 .next) (e2 .next)

-- mergeAll: свернуть все события в такте
mergeAll : (A → A → A) → A → Event A → Event A
mergeAll f init e .now = case e .now of
  [] → []
  xs → [ foldl f init xs ]
mergeAll f init e .next = mergeAll f init (e .next)

-- unionWith: как mergeWith, но с приоритетом левого
unionWith : (A → A → A) → Event A → Event A → Event A
-- Если оба события — применить f
-- Если только левое — взять его
-- Если только правое — взять его

-- alignWith: объединение событий разных типов
data These A B = This A | That B | Both A B

alignWith : (These A B → C) → Event A → Event B → Event C
alignWith f ea eb .now = case (ea .now, eb .now) of
  ([], [])     → []
  (a ∷ _, [])  → [ f (This a) ]
  ([], b ∷ _)  → [ f (That b) ]
  (a ∷ _, b ∷ _) → [ f (Both a b) ]
alignWith f ea eb .next = alignWith f (ea .next) (eb .next)

-- align: alignWith с сохранением These
align : Event A → Event B → Event (These A B)
align = alignWith id
```

**Пример: mergeWith для приоритетов**

```agda
-- Два источника команд, локальный приоритетнее
localCommands : Event Command
remoteCommands : Event Command

-- При одновременных командах — выполнить локальную
commands : Event Command
commands = mergeWith (λ local _ → local) localCommands remoteCommands
```

**Пример: alignWith для синхронизации**

```agda
-- Синхронизация двух потоков данных
userUpdates : Event User
profileUpdates : Event Profile

-- Объединить в один поток обновлений
data Update = UserOnly User | ProfileOnly Profile | Both User Profile

syncedUpdates : Event Update
syncedUpdates = alignWith toUpdate userUpdates profileUpdates
  where
    toUpdate (This u)     = UserOnly u
    toUpdate (That p)     = ProfileOnly p
    toUpdate (Both u p)   = Both u p

-- В update обрабатываем все случаи
update (SyncUpdate upd) m = case upd of
  UserOnly u   → record m { user = u }
  ProfileOnly p → record m { profile = p }
  Both u p     → record m { user = u; profile = p }
```

**Пример: align для join**

```agda
-- Ждать оба события (как Applicative для Event)
both : Event A → Event B → Event (A × B)
both ea eb = filterMap extract (align ea eb)
  where
    extract (Both a b) = Just (a , b)
    extract _          = Nothing

-- Пример: ждать и пользователя и его настройки
userAndSettings : Event (User × Settings)
userAndSettings = both (request getUser) (request getSettings)
```

### Сводка комбинаторов Event

#### Базовые

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `never` | `Event A` | Никогда не происходит |
| `occur` | `A → Event A` | Одно событие сейчас |
| `merge` | `Event A → Event A → Event A` | Объединить потоки |
| `mapE` | `(A → B) → Event A → Event B` | Преобразовать |
| `filterE` | `(A → Bool) → Event A → Event A` | Отфильтровать |
| `filterMap` | `(A → Maybe B) → Event A → Event B` | Map + filter |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Разделить по предикату |
| `split` | `Event (Either A B) → Event A × Event B` | Разделить Either |
| `leftmost` | `List (Event A) → Event A` | Первое событие (приоритет) |
| `difference` | `Event A → Event A → Event A` | Разница множеств |

#### Sampling (Event + Signal)

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `snapshot` | `(A → B → C) → Event A → Signal B → Event C` | Семплировать Signal |
| `attach` | `Event A → Signal B → Event (A × B)` | Приложить Signal |
| `tag` | `Signal A → Event B → Event A` | Взять значение Signal |
| `gate` | `Event A → Signal Bool → Event A` | Фильтр по Signal |
| `changes` | `Signal A → Event A` | События изменения |

#### Time-based

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `debounce` | `ℕ → Event A → Event A` | После паузы N мс |
| `throttle` | `ℕ → Event A → Event A` | Максимум раз в N мс |
| `delay` | `ℕ → Event A → Event A` | Задержка на N мс |
| `timeout` | `ℕ → Event A → Event ⊤` | Событие если тишина N мс |
| `after` | `ℕ → Event A → Event A` | Через N мс после |

#### Switching

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `switchE` | `Event A → Event (Event A) → Event A` | Переключить Event |
| `switchS` | `Signal A → Event (Signal A) → Signal A` | Переключить Signal |
| `coincidence` | `Event (Event A) → Event A` | Join для Event |

#### Merging

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `mergeWith` | `(A → A → A) → Event A → Event A → Event A` | Merge с функцией |
| `mergeAll` | `(A → A → A) → A → Event A → Event A` | Свернуть все в такте |
| `alignWith` | `(These A B → C) → Event A → Event B → Event C` | Объединить разные типы |
| `align` | `Event A → Event B → Event (These A B)` | Выровнять события |

#### Accumulators

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `foldp` | `(A → B → B) → B → Event A → Signal B` | Свёртка в Signal |
| `hold` | `A → Event A → Signal A` | Запомнить последнее |
| `accumE` | `A → Event (A → A) → Event A` | Свёртка в Event |
| `accumB` | `A → Event (A → A) → Signal A` | foldp с функциями |
| `mapAccum` | `(A → S → S × B) → S → Event A → Event B` | Map + accumulate |

#### Deferred

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `pre` | `A → Signal A → Signal A` | Задержка на такт |
| `delayS` | `ℕ → A → Signal A → Signal A` | Задержка на N тактов |
| `edge` | `Signal Bool → Event ⊤` | Событие на фронте |
| `risingEdge` | `Signal Bool → Event ⊤` | Передний фронт |
| `fallingEdge` | `Signal Bool → Event ⊤` | Задний фронт |

#### Error Handling

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `filterOk` | `Event (Result E A) → Event A` | Только успехи |
| `filterErr` | `Event (Result E A) → Event E` | Только ошибки |
| `partitionResult` | `Event (Result E A) → Event A × Event E` | Разделить |
| `catchE` | `Event (Result E A) → (E → A) → Event A` | Обработать ошибку |

#### Testing

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `interpret` | `(Event A → Event B) → List (List A) → List (List B)` | Тест Event |
| `interpretS` | `(Signal A → Signal B) → List A → List B` | Тест Signal |
| `interpretApp` | `App Msg Model → List (List Msg) → List Model` | Тест App |
| `collectN` | `ℕ → Event A → List (List A)` | Собрать N тактов |

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

### Accumulator Variants

Разные способы накопления состояния из событий. Идеи из Reactive-banana.

```agda
-- accumE: применить функции к аккумулятору, выдать СОБЫТИЕ с результатом
-- В отличие от foldp, возвращает Event, не Signal
accumE : A → Event (A → A) → Event A
accumE init e .now  = case e .now of
  []       → []
  (f ∷ fs) → [ foldl (λ a g → g a) (f init) fs ]  -- применить все функции
accumE init e .next = accumE (foldl (λ a f → f a) init (e .now)) (e .next)

-- accumB: как foldp, но принимает функции (синоним для удобства)
accumB : A → Event (A → A) → Signal A
accumB init e = foldp (λ f a → f a) init e

-- stepper: запомнить последнее значение
-- Отличие от hold: семантика timing (когда именно меняется)
stepper : A → Event A → Signal A
stepper = hold  -- в дискретном времени эквивалентны

-- mapAccum: комбинация accumE и mapE
-- Обрабатывает событие, обновляет состояние, выдаёт результат
mapAccum : (A → S → S × B) → S → Event A → Event B
mapAccum f init e .now = case e .now of
  []       → []
  (a ∷ as) → let (s', b) = f a init
             in b ∷ mapAccum' f s' as
  where
    mapAccum' : (A → S → S × B) → S → List A → List B
    mapAccum' f s []       = []
    mapAccum' f s (a ∷ as) = let (s', b) = f a s in b ∷ mapAccum' f s' as
mapAccum f init e .next = mapAccum f (finalState f init (e .now)) (e .next)
  where
    finalState : (A → S → S × B) → S → List A → S
    finalState f s []       = s
    finalState f s (a ∷ as) = finalState f (fst (f a s)) as
```

**Пример accumE: история действий**

```agda
-- Поток функций-модификаторов
data Action = Increment | Double | Reset

toFn : Action → ℕ → ℕ
toFn Increment = suc
toFn Double    = λ n → n * 2
toFn Reset     = const 0

actions : Event Action
modifiers : Event (ℕ → ℕ)
modifiers = mapE toFn actions

-- Событие с текущим значением после каждого действия
counterEvents : Event ℕ
counterEvents = accumE 0 modifiers

-- actions       = [[], [Inc], [Double, Inc], [], [Reset], ...]
-- counterEvents = [[], [1],   [3],           [], [0],     ...]
--                       ↑      ↑↑
--                     0+1    (0+1)*2+1=3
```

**Пример mapAccum: нумерация событий**

```agda
-- Добавить порядковый номер к каждому событию
numberEvents : Event A → Event (ℕ × A)
numberEvents = mapAccum (λ a n → (suc n, (n, a))) 0

-- events           = [[], [a], [b,c], [], [d], ...]
-- numberEvents     = [[], [(0,a)], [(1,b),(2,c)], [], [(3,d)], ...]
```

### Deferred Evaluation

Комбинаторы для управления временем вычисления.

```agda
-- pre: задержка Signal на один такт
-- Критично для разрыва циклических зависимостей
pre : A → Signal A → Signal A
pre init s .now  = init
pre init s .next = s  -- не s.next, а s!

-- Пример: предыдущее значение
previous : A → Signal A → Signal A
previous = pre

-- delay для Signal (на N тактов)
delayS : ℕ → A → Signal A → Signal A
delayS 0 _ s = s
delayS (suc n) init s = pre init (delayS n init s)

-- edge: обнаружить изменение (событие на фронте)
edge : Signal Bool → Event ⊤
edge s .now = []
edge s .next .now = if not (s .now) && s .next .now then [ tt ] else []
edge s .next .next = edge (s .next) .next

-- risingEdge / fallingEdge
risingEdge : Signal Bool → Event ⊤
risingEdge = edge

fallingEdge : Signal Bool → Event ⊤
fallingEdge s = edge (map not s)
```

**Пример: разрыв цикла с pre**

```agda
-- БЕЗ pre: бесконечный цикл!
-- bad = map f bad  -- зависит от себя

-- С pre: работает
feedback : Signal ℕ
feedback = map suc (pre 0 feedback)
-- feedback = [0, 1, 2, 3, 4, ...]
--             ↑  ↑
--           init suc 0, suc 1, ...
```

**Пример: детектор изменения направления**

```agda
-- Событие когда значение начинает расти после падения
turningPoint : Signal ℕ → Event ⊤
turningPoint s =
  let prev = pre 0 s
      wasDecreasing = map (λ (p, c) → p > c) (zip prev s)
      nowIncreasing = map (λ (p, c) → p < c) (zip prev s)
  in gate (risingEdge nowIncreasing) wasDecreasing
```

### Error Handling

Комбинаторы для обработки ошибок в событиях.

```agda
-- Результат с возможной ошибкой
data Result (E A : Set) : Set where
  Err : E → Result E A
  Ok  : A → Result E A

-- Проверить результат
isOk : Result E A → Bool
isOk (Ok _) = true
isOk (Err _) = false

isErr : Result E A → Bool
isErr = not ∘ isOk

-- mapResult
mapResult : (A → B) → Result E A → Result E B
mapResult f (Ok a)  = Ok (f a)
mapResult f (Err e) = Err e

-- Фильтрация по результату
filterOk : Event (Result E A) → Event A
filterOk = filterMap (λ { (Ok a) → Just a; (Err _) → Nothing })

filterErr : Event (Result E A) → Event E
filterErr = filterMap (λ { (Err e) → Just e; (Ok _) → Nothing })

-- partitionResult: разделить на успехи и ошибки
partitionResult : Event (Result E A) → Event A × Event E
partitionResult e = (filterOk e, filterErr e)

-- catchE: обработать ошибку
catchE : Event (Result E A) → (E → A) → Event A
catchE e handler = mapE (λ { (Ok a) → a; (Err e) → handler e }) e

-- catchE с Event-обработчиком
catchEventE : Event (Result E A) → (E → Event A) → Event A
catchEventE e handler = merge (filterOk e) (switchE never (mapE handler (filterErr e)))

-- throwE: создать событие-ошибку
throwE : E → Event (Result E A)
throwE e = occur (Err e)

-- tryE: обернуть Event в Result (всегда Ok)
tryE : Event A → Event (Result E A)
tryE = mapE Ok

-- onError: выполнить действие при ошибке
onError : Event (Result E A) → Event E
onError = filterErr

-- onSuccess: выполнить действие при успехе
onSuccess : Event (Result E A) → Event A
onSuccess = filterOk
```

**HTTP с обработкой ошибок:**

```agda
data HttpError : Set where
  NetworkError : String → HttpError
  Timeout      : HttpError
  BadStatus    : ℕ → HttpError
  ParseError   : String → HttpError

-- Безопасный request
requestSafe : Request → Event (Result HttpError Response)

-- Пример использования
data Msg = Loading | GotData Data | GotError String | Retry

app = record
  { ...
  ; update = λ where
      Loading m → record m { status = InProgress }
      (GotData d) m → record m { status = Ready d }
      (GotError e) m → record m { status = Failed e }
      Retry m → record m { status = InProgress }  -- повторить

  ; events = λ m → case m.status of λ where
      InProgress →
        let response = requestSafe (get "/api/data")
            (oks, errs) = partitionResult response
        in merge
          (mapE (GotData ∘ parse) oks)
          (mapE (GotError ∘ showError) errs)
      _ → never
  }
  where
    showError : HttpError → String
    showError (NetworkError s) = "Network error: " ++ s
    showError Timeout = "Request timed out"
    showError (BadStatus n) = "Server error: " ++ show n
    showError (ParseError s) = "Parse error: " ++ s
```

**Retry с экспоненциальной задержкой:**

```agda
-- Повторять при ошибке с увеличивающейся задержкой
retryWithBackoff : ℕ → ℕ → Event (Result E A) → Event (Result E A)
retryWithBackoff maxRetries initialDelay e = go 0 initialDelay e
  where
    go : ℕ → ℕ → Event (Result E A) → Event (Result E A)
    go n delayMs evt =
      if n >= maxRetries
      then evt  -- отдать как есть
      else
        let (oks, errs) = partitionResult evt
        in merge
          (mapE Ok oks)  -- успехи проходят сразу
          (switchE never (mapE (λ _ → delay delayMs (go (suc n) (delayMs * 2) evt)) errs))
```

### Testing Combinators

Комбинаторы для тестирования реактивной логики без браузера.

```agda
-- Интерпретировать Event-трансформацию на тестовых данных
-- Каждый элемент списка = один такт
interpret : (Event A → Event B) → List (List A) → List (List B)
interpret f inputs = go (f (fromList inputs))
  where
    fromList : List (List A) → Event A
    fromList [] .now = []
    fromList [] .next = never
    fromList (xs ∷ xss) .now = xs
    fromList (xs ∷ xss) .next = fromList xss

    go : Event B → List (List B)
    go e = take (length inputs) (toList e)

    toList : Event B → List (List B)
    toList e = e .now ∷ toList (e .next)

-- interpretS: для Signal
interpretS : (Signal A → Signal B) → List A → List B
interpretS f inputs = go (f (fromList inputs))
  where
    fromList : List A → Signal A
    fromList [] .now = ⊥  -- или default
    fromList (x ∷ []) .now = x
    fromList (x ∷ []) .next = pure x
    fromList (x ∷ xs) .now = x
    fromList (x ∷ xs) .next = fromList xs

    go : Signal B → List B
    go s = take (length inputs) (toListS s)

    toListS : Signal B → List B
    toListS s = s .now ∷ toListS (s .next)

-- interpretApp: тестировать целое приложение
interpretApp : App Msg Model → List (List Msg) → List Model
interpretApp app inputs = go app.init inputs
  where
    go : Model → List (List Msg) → List Model
    go m [] = []
    go m (msgs ∷ rest) =
      let m' = foldl (flip app.update) m msgs
      in m' ∷ go m' rest
```

**Примеры тестов:**

```agda
-- Тест mapE
test_mapE : interpret (mapE suc) [[1,2], [], [3]] ≡ [[2,3], [], [4]]
test_mapE = refl

-- Тест filterE
test_filterE : interpret (filterE (_> 2)) [[1,2,3], [4,1], []] ≡ [[3], [4], []]
test_filterE = refl

-- Тест merge
test_merge : interpret (λ e → merge e (mapE (*10) e)) [[1], [2]]
           ≡ [[1,10], [2,20]]
test_merge = refl

-- Тест foldp через interpretS
test_foldp : interpretS (foldp _+_ 0) [1, 2, 3, 4] ≡ [0, 1, 3, 6]
test_foldp = refl

-- Тест debounce (концептуально)
-- debounce 2 такта: событие только если 2 такта тишины после
test_debounce_concept :
  interpret (debounce2Ticks) [[a], [], [], [b], [], []]
  ≡ [[], [], [a], [], [], [b]]
```

**Тестирование App:**

```agda
-- Counter app
counterApp : App CounterMsg ℕ
counterApp = record
  { init = 0
  ; update = λ { Inc n → suc n; Dec n → pred n }
  ; view = ...
  ; events = λ _ → never
  }

-- Тесты
test_counter_inc : interpretApp counterApp [[Inc], [Inc], [Inc]] ≡ [1, 2, 3]
test_counter_inc = refl

test_counter_mixed : interpretApp counterApp [[Inc, Inc], [Dec], []] ≡ [2, 1, 1]
test_counter_mixed = refl

-- Property-based тест
prop_counter_inc_dec : ∀ n →
  interpretApp counterApp (replicate n [Inc] ++ replicate n [Dec])
  ≡ [1..n] ++ [n-1..0]
```

**Утилиты для тестов:**

```agda
-- Собрать N тактов Event в список
collectN : ℕ → Event A → List (List A)
collectN 0 _ = []
collectN (suc n) e = e .now ∷ collectN n (e .next)

-- Проверить что Event никогда не срабатывает (на N тактов)
isNeverFor : ℕ → Event A → Bool
isNeverFor n e = all null (collectN n e)

-- Проверить что Event срабатывает ровно один раз
occursOnce : ℕ → Event A → Bool
occursOnce n e = length (concat (collectN n e)) ≡ 1
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

### Практический пример: форма с snapshot

Типичная задача: при отправке формы собрать текущие значения всех полей.

**Без snapshot (плохо — дублирование):**

```agda
-- Приходится хранить копию данных в Msg
data Msg = SetName String | SetEmail String | Submit String String
--                                                    ↑↑↑↑↑↑↑↑↑↑↑↑
--                                               дублирование Model!

update (Submit name email) m = record m { sending = true; ... }
-- name и email уже есть в m, зачем передавать?
```

**С snapshot (хорошо):**

```agda
data Msg = SetName String | SetEmail String | Submit | Sent Response

record Model : Set where
  field
    name    : String
    email   : String
    sending : Bool
    result  : Maybe Response

record FormData : Set where
  field
    name  : String
    email : String

app : App Msg Model
app = record
  { init = { name = ""; email = ""; sending = false; result = Nothing }

  ; update = λ where
      (SetName n) m  → record m { name = n }
      (SetEmail e) m → record m { email = e }
      Submit m       → record m { sending = true }
      (Sent r) m     → record m { sending = false; result = Just r }

  ; view = λ m → form [ onSubmit Submit ]
      [ input [ value (m .name), onInput SetName, placeholder "Name" ] []
      , input [ value (m .email), onInput SetEmail, placeholder "Email" ] []
      , button [ disabled (m .sending) ]
          [ text (if m .sending then "Sending..." else "Submit") ]
      , maybe empty viewResult (m .result)
      ]

  ; events = λ m →
      if m .sending
      then
        -- snapshot берёт текущие значения Model в момент отправки
        let formData = snapshot (λ _ m' → { name = m' .name; email = m' .email })
                                (request (post "/api/submit" (toJson formData)))
                                (pure m)
        in mapE Sent (request (post "/api/submit" (toJson { name = m .name; email = m .email })))
      else never
  }
```

**Ещё проще с tag:**

```agda
-- Если нужно просто текущее состояние при событии
events m =
  if m .sending
  then
    let formData = { name = m .name; email = m .email }
        response = request (post "/api/submit" (toJson formData))
    in mapE Sent response
  else never
```

### Практический пример: gate

**Кнопка активна только при валидной форме:**

```agda
isValid : Model → Bool
isValid m = length (m .name) > 0 && contains "@" (m .email)

-- Без gate: проверка в update
update Submit m = if isValid m then ... else m  -- легко забыть!

-- С gate: клики просто не проходят
app = record
  { ...
  ; events = λ m →
      let rawSubmit = domEvent "submit" (m .formElement)
          validSubmit = gate rawSubmit (pure (isValid m))
      in mapE (λ _ → DoSubmit) validSubmit
  }
```

### Практический пример: changes

**Загружать данные при смене вкладки, а не каждый такт:**

```agda
data Tab = Users | Posts | Settings

data Msg = SelectTab Tab | TabChanged Tab | LoadedData Data

app = record
  { ...
  ; events = λ m →
      merge
        -- Событие ТОЛЬКО когда вкладка изменилась
        (mapE TabChanged (changes (pure (m .currentTab))))
        -- Загрузка данных для новой вкладки
        (case m .loading of λ where
          (Just tab) → mapE LoadedData (request (getTabData tab))
          Nothing → never)

  ; update = λ where
      (SelectTab t) m → record m { currentTab = t }
      (TabChanged t) m → record m { loading = Just t }  -- начать загрузку
      (LoadedData d) m → record m { loading = Nothing; data = Just d }
  }
```

**Сравнение:**

| | Без changes | С changes |
|--|-------------|-----------|
| Событий | Каждый такт | Только при изменении |
| Загрузок | Много лишних | Ровно по необходимости |
| Производительность | ❌ | ✅ |

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

-- Информация о кадре (для animationFrame)
record FrameInfo : Set where
  field
    dt  : ℕ    -- миллисекунды с прошлого кадра (обычно 16-17)
    fps : ℕ    -- текущий FPS (скользящее среднее за секунду)
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

### animationFrame

```agda
animationFrame : Event FrameInfo
```

Событие на каждый кадр браузера (requestAnimationFrame, ~60 FPS).

```
animationFrame:
  кадр 0:   [FrameInfo { dt = 16, fps = 60 }]
  кадр 1:   [FrameInfo { dt = 17, fps = 59 }]
  кадр 2:   [FrameInfo { dt = 16, fps = 60 }]
  ...
```

**Отличие от interval:**

| | `interval 16` | `animationFrame` |
|--|---------------|------------------|
| Точность | ±4ms (setTimeout) | Синхронизирован с дисплеем |
| FPS info | ❌ Нет | ✅ Да |
| Батарея | ⚠️ Работает в фоне | ✅ Пауза в фоновых вкладках |
| Использование | Периодические задачи | Анимации, игры |

**Пример: анимация движения**

```agda
data Msg = Tick FrameInfo | Start | Stop

record Model : Set where
  field
    x : ℕ            -- позиция (пиксели)
    speed : ℕ        -- скорость (пиксели/сек)
    moving : Bool

app : App Msg Model
app = record
  { init = { x = 0; speed = 100; moving = false }

  ; update = λ where
      (Tick f) m → record m { x = m.x + m.speed * f.dt / 1000 }
      Start m → record m { moving = true }
      Stop m → record m { moving = false }

  ; view = λ m → div []
      [ div [ style [("left", show m.x ++ "px")] ] [ text "→" ]
      , button [ onClick (if m.moving then Stop else Start) ]
          [ text (if m.moving then "Stop" else "Start") ]
      ]

  ; events = λ m →
      if m.moving
      then mapE Tick animationFrame
      else never  -- цикл не крутится, браузер idle
  }
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
| `animationFrame` | `Event FrameInfo` | requestAnimationFrame | cancelAnimationFrame |
| `keyboard` | `Event Key` | addEventListener | removeEventListener |
| `request r` | `Event Response` | Отправить запрос | Отменить запрос |
| `websocket url` | `WebSocket` | — | — |
| `ws.recv` | `Event WsEvent` | Открыть соединение | Закрыть соединение |
| `ws.send msg` | `Event ⊤` | Отправить сообщение | — (уже отправлено) |

### animationFrame

```agda
record FrameInfo : Set where
  field
    dt  : ℕ    -- миллисекунды с прошлого кадра
    fps : ℕ    -- текущий FPS (скользящее среднее)

animationFrame : Event FrameInfo
```

**Семантика:**
- Подписка на `animationFrame` → запускает requestAnimationFrame loop
- Каждый кадр (~60 FPS) → событие `FrameInfo` с delta time
- Отписка → cancelAnimationFrame, loop останавливается

```
animationFrame:
  подписка → requestAnimationFrame(loop)
  кадр 0:   FrameInfo { dt = 16, fps = 60 }
  кадр 1:   FrameInfo { dt = 17, fps = 59 }
  кадр 2:   FrameInfo { dt = 16, fps = 60 }
  ...
  отписка → cancelAnimationFrame
```

**Важно:** когда `animationFrame` не в `events`, цикл не крутится — браузер idle, батарея не тратится.

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

### animationFrame

```javascript
const animationFrame = {
  _type: 'animationFrame',
  _args: [],

  subscribe: (emit) => {
    let lastTime = performance.now()
    let rafId = null

    // FPS tracking (скользящее среднее)
    let frameCount = 0
    let fpsTime = lastTime
    let currentFps = 60

    const loop = (now) => {
      const dt = Math.round(now - lastTime)
      lastTime = now

      // Вычисляем FPS раз в секунду
      frameCount++
      if (now - fpsTime >= 1000) {
        currentFps = frameCount
        frameCount = 0
        fpsTime = now
      }

      emit([{ dt, fps: currentFps }])
      rafId = requestAnimationFrame(loop)
    }

    rafId = requestAnimationFrame(loop)
    return { rafId, cancel: () => cancelAnimationFrame(rafId) }
  },

  unsubscribe: (handle) => {
    handle.cancel()
  }
}
```

**Особенности реализации:**

1. **Delta time** — `performance.now()` даёт миллисекунды с высокой точностью
2. **FPS** — вычисляется как количество кадров за последнюю секунду
3. **Cleanup** — `cancelAnimationFrame` останавливает loop при отписке
4. **Энергоэффективность** — когда Event не в `events`, loop не работает

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

{-# COMPILE JS animationFrame =
  (function() {
    return {
      _type: 'animationFrame',
      _args: [],
      subscribe: function(emit) {
        var lastTime = performance.now();
        var rafId = null;
        var frameCount = 0;
        var fpsTime = lastTime;
        var currentFps = 60;

        function loop(now) {
          var dt = Math.round(now - lastTime);
          lastTime = now;
          frameCount++;
          if (now - fpsTime >= 1000) {
            currentFps = frameCount;
            frameCount = 0;
            fpsTime = now;
          }
          emit([{ dt: dt, fps: currentFps }]);
          rafId = requestAnimationFrame(loop);
        }

        rafId = requestAnimationFrame(loop);
        return rafId;
      },
      unsubscribe: function(rafId) {
        cancelAnimationFrame(rafId);
      }
    };
  })()
#-}

{-# COMPILE JS debounce =
  function(ms) {
    return function(event) {
      return {
        _type: 'debounce',
        _args: [ms, event],
        subscribe: function(emit) {
          var timerId = null;
          var lastValue = null;

          var innerUnsub = event.subscribe(function(values) {
            if (values.length > 0) {
              lastValue = values[values.length - 1];
              if (timerId) clearTimeout(timerId);
              timerId = setTimeout(function() {
                emit([lastValue]);
                timerId = null;
              }, ms);
            }
          });

          return { innerUnsub: innerUnsub, timerId: timerId };
        },
        unsubscribe: function(handle) {
          if (handle.timerId) clearTimeout(handle.timerId);
          handle.innerUnsub();
        }
      };
    };
  }
#-}

{-# COMPILE JS throttle =
  function(ms) {
    return function(event) {
      return {
        _type: 'throttle',
        _args: [ms, event],
        subscribe: function(emit) {
          var lastEmit = 0;

          var innerUnsub = event.subscribe(function(values) {
            var now = performance.now();
            if (values.length > 0 && now - lastEmit >= ms) {
              emit([values[0]]);
              lastEmit = now;
            }
          });

          return innerUnsub;
        },
        unsubscribe: function(innerUnsub) {
          innerUnsub();
        }
      };
    };
  }
#-}

{-# COMPILE JS delay =
  function(ms) {
    return function(event) {
      return {
        _type: 'delay',
        _args: [ms, event],
        subscribe: function(emit) {
          var timers = [];

          var innerUnsub = event.subscribe(function(values) {
            values.forEach(function(v) {
              var timerId = setTimeout(function() {
                emit([v]);
              }, ms);
              timers.push(timerId);
            });
          });

          return { innerUnsub: innerUnsub, timers: timers };
        },
        unsubscribe: function(handle) {
          handle.timers.forEach(function(t) { clearTimeout(t); });
          handle.innerUnsub();
        }
      };
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
    │   ├── AnimationFrame.agda  -- animationFrame : Event FrameInfo
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

### Dynamic (Phase 2)

`Dynamic` объединяет `Signal` и `Event` — текущее значение плюс события изменений. Идея из Reflex.

```agda
-- Dynamic = Signal + Event изменений
record Dynamic (A : Set) : Set where
  field
    current : Signal A      -- текущее значение (всегда доступно)
    updated : Event A       -- события изменения (для оптимизации)

-- Конструкторы
holdDyn : A → Event A → Dynamic A
holdDyn init e = record
  { current = hold init e
  ; updated = e
  }

foldDyn : (A → B → B) → B → Event A → Dynamic B
foldDyn f init e = record
  { current = foldp f init e
  ; updated = -- событие с новым значением после применения f
  }

-- Из Signal (updated = changes)
fromSignal : ⦃ Eq A ⦄ → Signal A → Dynamic A
fromSignal s = record { current = s; updated = changes s }
```

**Зачем нужен Dynamic?**

```agda
-- Signal: нужно проверять каждый такт, изменилось ли
-- Event: знаем точно когда изменилось, но нет "текущего значения"
-- Dynamic: и то, и другое!

-- Пример: оптимизированный рендеринг
viewOptimized : Dynamic Model → Html Msg
viewOptimized dm = div []
  [ -- Перерисовывается только при изменении counter
    dynText (mapDyn (λ m → show m.counter) dm)
  , -- Статический контент
    footer [] [ text "Footer" ]
  ]

-- mapDyn : (A → B) → Dynamic A → Dynamic B
-- dynText : Dynamic String → Html Msg  (обновляет DOM только при updated)
```

**Комбинаторы Dynamic:**

```agda
-- Functor
mapDyn : (A → B) → Dynamic A → Dynamic B

-- Applicative
pureDyn : A → Dynamic A
apDyn : Dynamic (A → B) → Dynamic A → Dynamic B

-- Переключение
switchDyn : Dynamic A → Event (Dynamic A) → Dynamic A
```

### Widget (Phase 2)

`Widget` — виджет, который "возвращает значение" при завершении. Идея из Concur.

```agda
-- Widget A = виджет, который вернёт A когда завершится
record Widget (A : Set) : Set where
  field
    html   : Html WidgetMsg
    result : Event A

-- Примитивные виджеты
button : String → Widget ⊤
button label = record
  { html = Html.button [ onClick Done ] [ text label ]
  ; result = -- событие при клике
  }

textInput : Widget String
textInput = record
  { html = Html.input [ onKeyDown check, onInput Update ] []
  ; result = -- событие со строкой при Enter
  }
```

**Композиция виджетов:**

```agda
-- Applicative: оба виджета активны параллельно
instance Applicative Widget where
  pure a = record { html = empty; result = occur a }
  wf <*> wa = record
    { html = div [] [ wf .html, wa .html ]
    ; result = -- ждём оба результата
    }

-- Alternative: первый кто вернёт
instance Alternative Widget where
  w1 <|> w2 = record
    { html = div [] [ w1 .html, w2 .html ]
    ; result = race [ w1 .result, w2 .result ]
    }

-- Monad: последовательно
instance Monad Widget where
  wa >>= f = -- сначала wa, потом f с результатом
```

**Пример: форма логина**

```agda
loginForm : Widget Credentials
loginForm = do
  username ← labeled "Username:" textInput
  password ← labeled "Password:" passwordInput
  _ ← button "Login"
  pure (Credentials username password)

-- С альтернативой: логин или отмена
loginOrCancel : Widget (Maybe Credentials)
loginOrCancel = (Just <$> loginForm) <|> (Nothing <$ button "Cancel")
```

**Интеграция в App:**

```agda
-- Запустить виджет внутри App
embedWidget : Widget A → (A → Msg) → Model → Html Msg
```

### Incremental (Phase 3)

Инкрементальные вычисления для больших структур данных. Идея из Reflex.

```agda
-- Патч описывает изменение, не полное значение
data ListPatch (A : Set) : Set where
  Insert : ℕ → A → ListPatch A
  Delete : ℕ → ListPatch A
  Update : ℕ → A → ListPatch A

-- Incremental: значение + патчи
record Incremental (A : Set) (P : Set) : Set where
  field
    current : Signal A
    patches : Event P

-- Инкрементальный map (обновляет только изменённые элементы)
imapWithKey
  : (K → Dynamic V → Html Msg)
  → IncrementalMap K V
  → Html Msg
```

**Польза:** при добавлении одного элемента в список из 10000 — обновляется только один DOM-элемент, не весь список.

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

---

## На будущее: идеи для исследования

Идеи из FRP-систем, которые могут быть добавлены в будущих версиях. Требуют дополнительного исследования и проектирования.

### 1. Signal Functions (Yampa)

**Идея:** Вместо первоклассных `Signal A` — трансформации `SF A B = Signal A → Signal B`.

```agda
SF : Set → Set → Set
SF A B = Signal A → Signal B

-- Arrow комбинаторы
arr    : (A → B) → SF A B
_>>>_  : SF A B → SF B C → SF A C
_&&&_  : SF A B → SF A C → SF A (B × C)
first  : SF A B → SF (A × C) (B × C)
loop   : SF (A × C) (B × C) → SF A B  -- feedback

-- Для физики
integral   : SF ℕ ℕ
derivative : SF ℕ ℕ

-- Переключение
switch  : SF A (B × Event C) → (C → SF A B) → SF A B
rSwitch : SF A B → Event (SF A B) → SF A B
```

**Польза:** Гарантированно нет time leaks — `join : Signal (Signal A) → Signal A` невозможен.

**Сложность:** ★★★ — требует изменения базовой модели или параллельного API.

**Источник:** Yampa, Dunai/Rhine.

---

### 2. Collection Combinators (Reflex)

**Идея:** Эффективная работа с динамическими коллекциями виджетов.

```agda
-- Динамический список
simpleList
  : Dynamic (List A)
  → (Dynamic A → Widget B)
  → Widget (List B)

-- Список с ключами (обновляется только изменённый элемент)
listWithKey
  : Dynamic (Map K V)
  → (K → Dynamic V → Widget B)
  → Widget (Map K B)

-- Выбор из списка
selectViewListWithKey
  : Dynamic K                              -- выбранный
  → Dynamic (Map K V)                      -- элементы
  → (K → Dynamic V → Dynamic Bool → Widget B)
  → Widget (Event K)
```

**Польза:** При изменении одного элемента в списке из 10000 — обновляется один DOM-элемент.

**Сложность:** ★★★ — требует `Dynamic` и `Widget`.

**Источник:** Reflex.

---

### 3. FRPNow Patterns

**Идея:** Монада `Now` для описания "текущего момента" и планирования.

```agda
Now : Set → Set

sample   : Signal A → Now A                    -- текущее значение
plan     : Event (Now A) → Now (Event A)       -- запланировать
callback : Now (A → IO ⊤ × Event A)            -- создать callback
async    : IO A → Now (Event A)                -- async как Event
```

**Польза:** Удобная интеграция с императивным кодом, callbacks.

**Сложность:** ★★☆ — новая монада, но концептуально понятно.

**Источник:** FRPNow.

---

### 4. Resource Management (Bracket Pattern)

**Идея:** Гарантированное освобождение ресурсов.

```agda
-- Bracket: acquire → use → cleanup (всегда)
bracket : Event A → (A → Event ⊤) → (A → Event B) → Event B

-- Пример
withWebSocket : Url → (WebSocket → Event A) → Event A
withWebSocket url use = bracket
  (connect url)       -- acquire
  (λ ws → close ws)   -- cleanup
  use                 -- use

-- withFile, withTransaction, ...
```

**Польза:** Нет утечек ресурсов даже при ошибках.

**Сложность:** ★★☆ — нужна интеграция с runtime.

**Источник:** Haskell bracket, RAII.

---

### 5. Рекурсивные определения (MonadFix)

**Идея:** Ссылка на будущие значения в реактивной сети.

```agda
mfix : (Event A → Now (Event A)) → Now (Event A)

-- Позволяет:
network : Now ()
network = mfix $ λ clicks → do
  counter ← foldDyn (+1) 0 clicks
  button ← render counter
  return (buttonClicks button)  -- clicks через себя!
```

**Польза:** Элегантное описание взаимозависимых компонентов.

**Сложность:** ★★★ — требует MonadFix, сложная семантика.

**Источник:** Reflex (rec), Haskell MonadFix.

---

### 6. Push-Pull Hybrid

**Идея:** Комбинация push (события) и pull (ленивое вычисление).

```agda
record Reactive A : Set where
  field
    sample  : Time → A       -- pull: значение в момент t
    changes : Event ⊤        -- push: когда могло измениться
```

**Польза:** Эффективность — вычисляем только когда нужно.

**Сложность:** ★★★ — значительное изменение модели.

**Источник:** Conal Elliott "Push-Pull FRP".

---

### 7. Session Types для протоколов

**Идея:** Типизированные протоколы общения (WebSocket, Worker).

```agda
-- Протокол: Send Int, потом Recv String, потом End
Protocol : Session
Protocol = Send ℕ (Recv String End)

-- Канал следует протоколу
Channel : Session → Set

-- Операции проверяются типами
send : Channel (Send A S) → A → Channel S
recv : Channel (Recv A S) → Event (A × Channel S)
```

**Польза:** Невозможно нарушить протокол — ошибки на этапе компиляции.

**Сложность:** ★★★ — продвинутые типы.

**Источник:** Session Types literature.

---

### 8. Linear Types для ресурсов

**Идея:** Ресурсы, которые нужно использовать ровно один раз.

```agda
-- Линейный handle
data Handle¹ (A : Set) : Set where ...

-- Использовать можно только один раз
use : Handle¹ A → (A → B) → B

-- Нельзя забыть использовать, нельзя использовать дважды
```

**Польза:** Статическая гарантия корректного управления ресурсами.

**Сложность:** ★★★ — Agda не имеет встроенных линейных типов (нужна эмуляция).

**Источник:** Linear Haskell, Clean uniqueness types.

---

### 9. Time-Travel Debugging

**Идея:** Записать все события, воспроизвести состояние в любой момент.

```agda
-- Записать сессию
record Session : Set where
  field
    initialModel : Model
    events       : List (Timestamp × Msg)

-- Воспроизвести до момента t
replayTo : Session → Timestamp → Model

-- UI для отладки
debugger : App Msg Model → App DebugMsg (DebugModel Model)
```

**Польза:** Отладка сложных багов — "отмотать" и посмотреть что произошло.

**Сложность:** ★★☆ — архитектура уже позволяет (чистый update).

**Источник:** Redux DevTools, Elm Debugger.

---

### 10. Distributed/Replicated State

**Идея:** Синхронизация состояния между клиентами.

```agda
-- CRDT-совместимые операции
data Op : Set where ...

-- Применить операцию (коммутативно)
apply : Op → Model → Model
-- ∀ op1 op2 m → apply op1 (apply op2 m) ≡ apply op2 (apply op1 m)

-- Синхронизация
sync : Event Op → Event Op → Event Op
```

**Польза:** Collaborative editing, offline-first apps.

**Сложность:** ★★★ — CRDTs, конфликты, консистентность.

**Источник:** CRDTs literature, Yjs, Automerge.

---

### Сводка: приоритеты исследования

| Идея | Сложность | Польза | Приоритет |
|------|-----------|--------|-----------|
| Time-Travel Debugging | ★★☆ | ★★★ | Высокий |
| Collection Combinators | ★★★ | ★★★ | Высокий |
| Resource Management | ★★☆ | ★★☆ | Средний |
| Signal Functions | ★★★ | ★★☆ | Средний |
| FRPNow Patterns | ★★☆ | ★☆☆ | Низкий |
| Session Types | ★★★ | ★★☆ | Низкий |
| Linear Types | ★★★ | ★★☆ | Низкий |
| MonadFix/rec | ★★★ | ★☆☆ | Низкий |
| Push-Pull Hybrid | ★★★ | ★☆☆ | Исследование |
| Distributed State | ★★★ | ★★☆ | Исследование |

---

### Источники для изучения

| Тема | Ресурсы |
|------|---------|
| Signal Functions | "The Yampa Arcade" paper, Dunai/Rhine |
| Dynamic Collections | Reflex documentation, `reflex-dom` |
| FRPNow | "Practical Principled FRP" paper |
| Push-Pull | Conal Elliott "Push-Pull FRP" |
| Session Types | "Session Types for Functional Programmers" |
| CRDTs | "A comprehensive study of CRDTs" |
| Time-Travel | Redux DevTools, Elm Debugger source |
