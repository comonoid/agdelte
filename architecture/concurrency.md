# Конкурентность в Agdelte

> **Статус:** 📋 Phase 3 (планируется). Этот документ описывает архитектуру расширения для конкурентных вычислений. Не реализовано в MVP.
>
> **Расширение:** опциональное расширение базовой архитектуры из [README.md](README.md).
>
> **Предусловие:** знакомство с Signal, Event, App. См. [README.md](README.md).
>
> **Ключевой принцип:** Worker генерирует **дискретные события**, как и все остальные примитивы. Никакой "непрерывности" — результат, прогресс, отмена — всё это отдельные дискретные события.

---

## Когда НЕ нужна конкурентность

**Большинство UI-приложений не требуют этого модуля.**

| Задача | Нужен worker? | Почему |
|--------|---------------|--------|
| Формы, валидация | ❌ Нет | Синхронно, < 1мс |
| Списки, фильтрация (< 1000 элементов) | ❌ Нет | Синхронно, < 16мс |
| HTTP запросы | ❌ Нет | `request` уже асинхронный |
| WebSocket | ❌ Нет | `websocket` уже асинхронный |
| Таймеры, анимации | ❌ Нет | `interval` достаточно |
| Парсинг большого JSON (> 1MB) | ✅ Да | Блокирует UI |
| Криптография | ✅ Да | Тяжёлые вычисления |
| Обработка изображений | ✅ Да | Много вычислений |
| ML inference | ✅ Да | Очень тяжело |

**Правило:** если операция занимает < 16мс — используй синхронный код. Worker добавляет накладные расходы (сериализация, передача, десериализация).

---

## Мотивация

Базовая архитектура: всё IO — это Event. Runtime в главном потоке, вычисления синхронные.

Проблема: **тяжёлые** вычисления блокируют UI.

```agda
-- Плохо: блокирует рендеринг
events m = if m.needsCompute
  then map Done (heavyComputation m.data)  -- 5 секунд в main thread
  else never
```

Решение: конкурентные вычисления как Event. Вычисление уходит в worker, результат приходит как событие.

---

## Ключевая идея

**Worker — это ещё один примитив Event.** Точно как `request` или `interval`:

```agda
-- Базовые примитивы (все дискретные!)
interval       : ℕ → Event ⊤              -- дискретные тики
animationFrame : Event FrameInfo          -- дискретные события каждый кадр
request        : Request → Event Response -- дискретный ответ
websocket      : Url → WebSocket          -- дискретные сообщения

-- Примитив конкурентности (тоже дискретный)
worker         : WorkerFn A B → A → Event B  -- дискретный результат
```

**Единая модель (всё — дискретные события):**

| Примитив | Подписка | Дискретное событие | Отписка |
|----------|----------|--------------------|---------|
| `interval n` | Запустить таймер | `⊤` (тик) | Остановить |
| `request r` | Отправить HTTP | `Response` (ответ) | Отменить |
| `worker f x` | Запустить вычисление | `B` (результат) | Отменить |

Декларативная модель сохраняется:
- Event появился в `events(model)` → worker запускается
- Event исчез → worker отменяется (если ещё не завершён)

**Композиция работает одинаково:**

```agda
events m = merge
  (mapE Tick (interval 1000))           -- таймер
  (mapE GotData (request (get "/api"))) -- HTTP
  (mapE Done (worker heavy m.input))    -- конкурентное вычисление
```

---

## 1. Базовый Worker

### Определение

```agda
-- Функция, выполняемая в worker
WorkerFn : Set → Set → Set
WorkerFn A B = A → B  -- чистая функция

-- Запустить вычисление в worker
worker : WorkerFn A B → A → Event B
```

### Пример: факторизация

```agda
-- Тяжёлая функция
factorize : ℕ → List ℕ
factorize n = ...  -- может занять секунды

data Msg = Compute | GotFactors (List ℕ)

app : App Msg Model
app = record
  { init = { number = 12345678901234; computing = false; factors = Nothing }

  ; update = λ where
      Compute m → record m { computing = true }
      (GotFactors fs) m → record m { computing = false; factors = Just fs }

  ; view = ...

  ; events = λ m →
      if m.computing
      then map GotFactors (worker factorize (m.number))
      else never
  }
```

Runtime:
1. `computing = true` → spawn worker с `factorize`
2. Worker вычисляет в отдельном потоке
3. Результат готов → Event `GotFactors`
4. `computing = false` → worker больше не нужен

---

## 2. Прогресс и отмена

### Event с прогрессом

```agda
data Progress (A : Set) : Set where
  Running  : ℕ → Progress A      -- дискретное событие: "сейчас на 50%"
  Done     : A → Progress A       -- дискретное событие: результат
  Cancelled : Progress A          -- дискретное событие: отменено
  Failed   : String → Progress A  -- дискретное событие: ошибка

workerWithProgress : WorkerFn A B → A → Event (Progress B)
```

**Важно:** `Running 50` — это **одно дискретное событие**, не "непрерывный поток прогресса". Worker периодически отправляет дискретные события `Running n`, каждое из которых обрабатывается как отдельный такт.

### Пример: обработка большого файла

```agda
data Msg = Process | Progress ℕ | Done Result | Cancel

app = record
  { ...
  ; update = λ where
      Process m → record m { processing = true; progress = 0 }
      (Progress p) m → record m { progress = p }
      (Done r) m → record m { processing = false; result = Just r }
      Cancel m → record m { processing = false }  -- отмена

  ; events = λ m →
      if m.processing
      then map toMsg (workerWithProgress processFile m.file)
      else never
  }
  where
    toMsg : Progress Result → Msg
    toMsg (Running p) = Progress p
    toMsg (Done r) = Done r
    toMsg _ = NoOp
```

**Отмена:** когда пользователь нажимает Cancel:
1. `update Cancel` ставит `processing = false`
2. `events` возвращает `never`
3. Runtime видит, что Event исчез → отменяет worker
4. Worker получает сигнал отмены

---

## 3. Параллельные вычисления

### Комбинаторы

```agda
-- Запустить параллельно, собрать все результаты
parallel : List (Event A) → Event (List A)

-- Запустить параллельно, взять первый результат
race : List (Event A) → Event A

-- Запустить последовательно
sequence : List (Event A) → Event (List A)
```

### Пример: параллельная обработка чанков

```agda
processChunks : List Chunk → Event (List Result)
processChunks chunks = parallel (map (worker processChunk) chunks)

-- 4 чанка → 4 worker'а параллельно → один Event со списком результатов
```

### Пример: race для таймаута

```agda
withTimeout : ℕ → Event A → Event (Maybe A)
withTimeout ms e = map choose (race [map Just e, map (const Nothing) (delay ms)])
  where
    choose : Either A ⊤ → Maybe A
    choose (Left a) = Just a
    choose (Right _) = Nothing
```

### Дополнительные комбинаторы

Для полноты — комбинаторы, используемые в примерах:

```agda
-- Задержка на N мс, затем одно дискретное событие
delay : ℕ → Event ⊤
-- Примечание: реализуется через oneshot-вариант interval

-- Одно событие сейчас (см. combinators.md)
occur : A → Event A

-- Монадные операции для Event (см. combinators.md для полного списка)
_>>=_ : Event A → (A → Event B) → Event B  -- flatMap/bind
_>>_  : Event A → Event B → Event B        -- sequence
e1 >> e2 = e1 >>= const e2

-- Переключиться на новый Event при каждом событии
switchMap : (A → Event B) → Event A → Event B

-- Дискретные события изменения Signal (см. combinators.md)
changes : Signal A → Event A
```

---

## 4. Worker Pool

### Проблема

Создание worker'а дорого. Если много мелких задач — накладные расходы.

### Решение: пул

```agda
-- Пул из N worker'ов
WorkerPool : ℕ → Set

-- Создать пул (runtime управляет жизненным циклом)
pool : ℕ → WorkerPool

-- Выполнить в пуле
poolWorker : WorkerPool → WorkerFn A B → A → Event B
```

Runtime:
- Пул создаётся при первом использовании
- Задачи распределяются по свободным worker'ам
- Worker'ы переиспользуются
- Пул уничтожается когда не используется

**Жизненный цикл пула:**

```javascript
// Runtime отслеживает активные задачи пула
poolState = {
  workers: [...],        // созданные worker'ы
  queue: [...],          // очередь задач
  activeTasks: 0,        // сколько задач выполняется
  lastUsed: timestamp    // когда последний раз использовался
}

// Очистка по таймауту
setInterval(() => {
  if (poolState.activeTasks === 0 &&
      Date.now() - poolState.lastUsed > POOL_IDLE_TIMEOUT) {
    poolState.workers.forEach(w => w.terminate())
    poolState.workers = []
  }
}, POOL_CHECK_INTERVAL)
```

**Константы (настраиваемые):**
- `POOL_IDLE_TIMEOUT` = 30000 мс (30 сек без задач → очистка)
- `POOL_CHECK_INTERVAL` = 5000 мс

### Пример: пакетная обработка

```agda
myPool : WorkerPool
myPool = pool 4  -- 4 worker'а

processMany : List Item → Event (List Result)
processMany items = parallel (map (poolWorker myPool processItem) items)
-- До 4 задач выполняются параллельно, остальные ждут в очереди
```

### Идентификация worker'ов

Как runtime отличает "тот же worker" от "другого"?

```agda
-- Это один и тот же worker или два разных?
events m = if m.computing
  then worker factorize m.number
  else never
```

**Правило:** структурное сравнение по (функция, аргументы).

- `worker factorize 100` == `worker factorize 100` → тот же (переиспользовать)
- `worker factorize 100` != `worker factorize 200` → разные (отменить старый, запустить новый)
- `worker factorize 100` != `worker otherFn 100` → разные

**При изменении аргументов:**
1. Runtime видит: старый `worker f x` исчез, новый `worker f y` появился
2. Отменяет старый worker
3. Запускает новый

### Гонки: результат vs отмена

**Сценарий:** worker завершился, но Event уже убран из `events`.

```
Такт N:   events = worker f x     → worker запущен
Такт N+1: events = never          → отмена отправлена
          [результат приходит]    → ???
```

**Поведение:** результат игнорируется.

Runtime:
1. При отписке помечает worker как "отменённый"
2. Если результат приходит после отмены — не вызывает `emit`
3. Гарантия: после `events = never` никаких событий от этого worker'а

```javascript
unsubscribe: (w) => {
  w._cancelled = true  // пометить
  w.postMessage({ type: 'cancel' })
  w.terminate()
}

// В subscribe:
w.onmessage = (e) => {
  if (w._cancelled) return  // игнорировать
  emit([...])
}
```

---

## 5. Structured Concurrency

### Принцип

Дочерние задачи не переживают родительские. Если родитель отменён — дети тоже.

### В Agdelte

Естественно следует из декларативной модели:

```agda
events m =
  if m.parentTask
  then merge
    (worker taskA m.dataA)      -- дочерняя задача 1
    (worker taskB m.dataB)      -- дочерняя задача 2
  else never
```

Когда `parentTask = false`:
- Оба Event исчезают из `events`
- Runtime отменяет оба worker'а
- Structured concurrency без явного управления

### Scope

```agda
-- Явный scope для группы задач
scope : (Scope → Event A) → Event A

record Scope : Set where
  field
    -- Запустить задачу в этом scope
    launch : Event B → Event B
    -- Проверить, отменён ли scope
    cancelled : Signal Bool
```

**Семантика:**
- `scope` создаёт контекст для группы задач
- Все `launch`-нутые Event'ы привязаны к scope
- Когда внешний Event исчезает из `events` → scope отменяется → все дочерние отменяются

```agda
-- Пример: загрузить несколько ресурсов, отменить всё при уходе со страницы
events m = if m.onResourcePage
  then scope λ s →
    merge
      (s.launch (worker loadA m.idA))
      (s.launch (worker loadB m.idB))
      (s.launch (worker loadC m.idC))
  else never
-- Уход со страницы → scope отменён → все три worker'а отменены
```

---

## 6. Каналы и потоки

### Для сложных сценариев: двунаправленная связь

```agda
-- Канал: отправка и получение
record Channel (Send : Set) (Recv : Set) : Set where
  send   : Send → Event ⊤           -- отправить в worker
  recv   : Event Recv               -- получить из worker
  close  : Event ⊤                  -- закрыть канал

-- Создать канал к worker'у
channel : WorkerScript → Event (Channel Send Recv)
```

**Семантика канала:**

- `send` — отправляет сообщение в worker, возвращает Event ⊤ когда доставлено
- `recv` — поток сообщений от worker'а (может быть много за такт)
- `close` — закрывает канал

**Закрытие канала:**
1. Когда Channel исчезает из `events` (декларативно) → автоматически close
2. Явный вызов `close` → отправить сигнал worker'у
3. Pending сообщения в очереди — теряются (fire-and-forget)
4. Worker получает событие "channel closed" и должен завершиться

```javascript
// Worker-side
onmessage = (e) => {
  if (e.data.type === 'close') {
    cleanup()
    self.close()
    return
  }
  // обработка обычных сообщений
}
```

### Пример: стриминг данных

```agda
data Msg = Start | Chunk Data | End | SendMore

streamProcessor : App Msg Model
streamProcessor = record
  { ...
  ; events = λ m → case m.channel of λ where
      Nothing → if m.shouldStart
                then map GotChannel (channel "processor.js")
                else never
      (Just ch) → merge
        (ch.recv)                           -- получаем чанки
        (if m.needMore then ch.send More else never)  -- запрашиваем ещё
  }
```

---

## 7. SharedArrayBuffer

### Для тяжёлых данных

Обычная передача: копирование (медленно для больших массивов).

SharedArrayBuffer: общая память (быстро, но требует синхронизации).

```agda
-- Shared buffer между main thread и worker
SharedBuffer : ℕ → Set

-- Создать shared buffer
allocShared : ℕ → Event SharedBuffer

-- Worker с доступом к shared memory
workerShared : SharedBuffer → WorkerFn A B → A → Event B
```

### Пример: обработка изображения

```agda
processImage : App Msg Model
processImage = record
  { ...
  ; events = λ m → case m.phase of λ where
      -- 1. Выделить shared buffer
      Init → map GotBuffer (allocShared (m.width * m.height * 4))

      -- 2. Запустить worker с shared buffer
      Ready → map Done (workerShared m.buffer processPixels m.params)

      _ → never
  }
```

Worker читает/пишет напрямую в buffer, без копирования.

---

## 8. FFI реализация

### Worker primitive

```javascript
const worker = (fn) => (input) => ({
  _type: 'worker',
  _args: [fn.toString(), input],

  subscribe: (emit) => {
    const w = new Worker('agdelte-worker.js')

    w.onmessage = (e) => {
      if (e.data.type === 'progress') {
        emit([{ tag: 'Running', value: e.data.percent }])
      } else if (e.data.type === 'done') {
        emit([{ tag: 'Done', value: e.data.result }])
        w.terminate()
      }
    }

    w.onerror = (e) => {
      emit([{ tag: 'Failed', value: e.message }])
      w.terminate()
    }

    w.postMessage({ fn: fn.toString(), input })
    return w
  },

  unsubscribe: (w) => {
    w.postMessage({ type: 'cancel' })
    w.terminate()
  }
})
```

### Worker script (agdelte-worker.js)

```javascript
let cancelled = false

onmessage = async (e) => {
  if (e.data.type === 'cancel') {
    cancelled = true
    return
  }

  const fn = eval(e.data.fn)
  const input = e.data.input

  // Для функций с прогрессом
  const reportProgress = (percent) => {
    if (!cancelled) {
      postMessage({ type: 'progress', percent })
    }
  }

  try {
    const result = await fn(input, { reportProgress, isCancelled: () => cancelled })
    if (!cancelled) {
      postMessage({ type: 'done', result })
    }
  } catch (err) {
    if (!cancelled) {
      postMessage({ type: 'error', message: err.message })
    }
  }
}
```

### Как Agda-функция становится JS

**Проблема:** Agda компилируется в JS, но worker требует отдельный скрипт.

**Решение:** compile-time extraction.

```agda
-- В Agda: помечаем функцию как worker-совместимую
{-# WORKER factorize #-}
factorize : ℕ → List ℕ
factorize n = ...
```

Компилятор:
1. Компилирует `factorize` в JS как обычно
2. Дополнительно создаёт `factorize.worker.js` с той же логикой
3. `worker factorize` в runtime ссылается на этот файл

```javascript
// Сгенерированный код
const worker = (fnName) => (input) => ({
  _type: 'worker',
  _args: [fnName, input],

  subscribe: (emit) => {
    // Загружаем конкретный worker-файл
    const w = new Worker(`${fnName}.worker.js`)
    // ...
  }
})
```

**Ограничения WorkerFn:**
- Функция должна быть чистой (без побочных эффектов)
- Не может замыкаться на внешние переменные (только аргументы)
- Все зависимости должны быть доступны в worker-контексте

---

## 9. Типизация конкурентности

### Линейные типы для ресурсов (Phase 3+)

Worker — ресурс, который должен быть освобождён. Линейные типы гарантируют это.

**Примечание:** Agda не имеет встроенных линейных типов. Варианты реализации:

**Вариант A: Эмуляция через индексированные типы**

```agda
-- Состояние ресурса
data ResourceState : Set where
  Open Closed : ResourceState

-- Индексированный handle
data WorkerHandle (A : Set) : ResourceState → Set where
  mkHandle : WorkerId → WorkerHandle A Open

-- Операции меняют индекс
await : WorkerHandle A Open → Event (A × WorkerHandle A Closed)
cancel : WorkerHandle A Open → Event (WorkerHandle A Closed)

-- Нельзя использовать Closed handle
-- await : WorkerHandle A Closed → ... -- не типизируется
```

**Вариант B: Uniqueness types (как в Clean)**

```agda
-- Уникальный тип: компилятор отслеживает единственность
data Unique (A : Set) : Set where
  unique : A → Unique A

-- Операции потребляют и возвращают
useWorker : Unique (WorkerHandle A) → Event (A × Unique Consumed)
```

**Вариант C: Монада с линейным контекстом**

```agda
-- Linear monad отслеживает ресурсы
data LIO (resources : List ResourceType) (A : Set) : Set where
  ...

spawn : LIO rs (WorkerHandle A) → LIO (Worker ∷ rs) (WorkerHandle A)
await : WorkerHandle A → LIO (Worker ∷ rs) A → LIO rs A
```

**Для MVP:** декларативная модель (`events`) уже даёт автоматическое управление ресурсами. Линейные типы — оптимизация для явного низкоуровневого контроля.

### Session types для протоколов

Для сложных worker'ов с протоколом общения:

```agda
-- Протокол: отправить Int, получить String, конец
Protocol : Session
Protocol = Send ℕ (Recv String End)

-- Worker следует протоколу
typedWorker : (s : Session) → WorkerImpl s → SessionChannel s
```

---

## 10. Сравнение с Haskell async

### Выразительность: декларативно vs явные handle'ы

Всё, что можно сделать с явными handle'ами в Haskell, выражается декларативно:

| Операция | Haskell async | Agdelte |
|----------|---------------|---------|
| Запустить | `h <- async task` | `events = worker task x` |
| Дождаться | `wait h` | Результат приходит как Event |
| Отменить | `cancel h` | Убрать из `events` |
| Проверить статус | `poll h` | Хранить в Model |
| Передать компоненту | `passHandle h` | `mapE ChildMsg (child.events)` |
| Условная отмена | `when cond (cancel h)` | `if cond then never else worker ...` |

**Вывод:** декларативная модель эквивалентна по выразительности.

### Преимущества Agdelte

| Аспект | Haskell async | Agdelte |
|--------|---------------|---------|
| Утечки ресурсов | ⚠️ возможны (забыли cancel) | ✅ невозможны по построению |
| Structured concurrency | ⚠️ нужен явный `withAsync` | ✅ автоматически |
| Bracket/cleanup | ⚠️ ручной | ✅ автоматический |
| Progress reporting | ❌ строить вручную | ✅ встроено |
| Унификация с IO | ❌ отдельный API | ✅ единый Event |

### Соответствие API

```haskell
-- Haskell async
async       :: IO a -> IO (Async a)
wait        :: Async a -> IO a
cancel      :: Async a -> IO ()
race        :: IO a -> IO b -> IO (Either a b)
concurrently :: IO a -> IO b -> IO (a, b)
mapConcurrently :: (a -> IO b) -> [a] -> IO [b]
```

```agda
-- Agdelte (декларативно через events)
worker   : WorkerFn A B → A → Event B        -- async + wait
-- cancel = убрать Event из events
race     : List (Event A) → Event A          -- race
parallel : List (Event A) → Event (List A)   -- concurrently / mapConcurrently
```

### Пример: concurrently

```haskell
-- Haskell: загрузить два ресурса параллельно
main = do
  (users, posts) <- concurrently
    (fetchUsers)
    (fetchPosts)
  print (users, posts)
```

```agda
-- Agdelte: то же самое
data Msg = StartLoad | GotBoth (List User × List Post)

data Phase = Idle | Loading | Done (List User × List Post)

app : App Msg Model
app = record
  { init = { phase = Idle }

  ; update = λ where
      StartLoad m → record m { phase = Loading }
      (GotBoth (users , posts)) m → record m { phase = Done (users , posts) }

  ; view = λ m → case m.phase of λ where
      Idle → button [ onClick StartLoad ] [ text "Load" ]
      Loading → text "Loading..."
      (Done (users , posts)) → viewResults users posts

  ; events = λ m → case m.phase of λ where
      Loading → mapE GotBoth (both
        (worker fetchUsers tt)
        (worker fetchPosts tt))
      _ → never
  }
  where
    -- Комбинатор для пары (специализация parallel)
    both : Event A → Event B → Event (A × B)
    both ea eb = map toPair (parallel [map Left ea, map Right eb])
      where
        toPair [Left a, Right b] = (a , b)
```

### Пример: race с таймаутом

```haskell
-- Haskell: запрос с таймаутом
fetchWithTimeout :: Int -> IO (Maybe Response)
fetchWithTimeout ms = do
  result <- race
    (threadDelay ms >> return Nothing)
    (Just <$> fetchData)
  return (either id id result)
```

```agda
-- Agdelte: то же самое
data Msg = Fetch | GotResult (Maybe Response)

app = record
  { ...
  ; events = λ m →
      if m.fetching
      then mapE GotResult (raceTimeout 5000 (worker fetchData m.url))
      else never
  }
  where
    raceTimeout : ℕ → Event A → Event (Maybe A)
    raceTimeout ms e = race
      [ mapE Just e
      , mapE (const Nothing) (delay ms)
      ]
```

### Пример: mapConcurrently

```haskell
-- Haskell: обработать список параллельно
processAll :: [Item] -> IO [Result]
processAll items = mapConcurrently processItem items
```

```agda
-- Agdelte: то же самое
data Msg = Process | GotResults (List Result)

app = record
  { ...
  ; events = λ m →
      if m.processing
      then mapE GotResults (parallel (map (worker processItem) m.items))
      else never
  }
-- 10 items → 10 worker'ов параллельно → один Event со списком результатов
```

### Пример: async/await стиль (последовательные зависимые вычисления)

```haskell
-- Haskell: сначала одно, потом другое (зависит от результата первого)
main = do
  user <- async fetchUser
  userId <- wait user
  posts <- async (fetchPostsFor userId)
  userPosts <- wait posts
  return userPosts
```

```agda
-- Agdelte: state machine для последовательности
data Phase
  = Idle
  | FetchingUser
  | FetchingPosts UserId
  | Done (List Post)

data Msg
  = Start
  | GotUser User
  | GotPosts (List Post)

app = record
  { init = { phase = Idle }

  ; update = λ where
      Start m → record m { phase = FetchingUser }
      (GotUser user) m → record m { phase = FetchingPosts (user.id) }
      (GotPosts posts) m → record m { phase = Done posts }

  ; events = λ m → case m.phase of λ where
      FetchingUser → mapE GotUser (worker fetchUser tt)
      (FetchingPosts uid) → mapE GotPosts (worker fetchPostsFor uid)
      _ → never
  }
```

**Паттерн:** фаза в Model определяет, какой worker активен. Результат одного → следующая фаза → следующий worker.

### Пример: withAsync (bracket-style)

```haskell
-- Haskell: гарантированная отмена при выходе из scope
withAsync :: IO a -> (Async a -> IO b) -> IO b
withAsync action inner = bracket (async action) cancel inner
```

```agda
-- Agdelte: автоматически через декларативность!
events m =
  if m.pageActive
  then worker longComputation m.data  -- активен пока на странице
  else never                          -- ушли со страницы → отмена

-- Не нужен явный bracket — отмена происходит автоматически
-- когда Event исчезает из events
```

### Сводка соответствий

| Haskell async | Agdelte | Примечание |
|---------------|---------|------------|
| `async action` | `worker fn x` | Возвращает Event |
| `wait handle` | Подписка через events | Декларативно |
| `cancel handle` | Убрать из events | Автоматически |
| `race a b` | `race [ea, eb]` | Идентично |
| `concurrently a b` | `both ea eb` | Через parallel |
| `mapConcurrently f xs` | `parallel (map (worker f) xs)` | Идентично |
| `withAsync` | Декларативность | Автоматическая отмена |
| Последовательность | State machine | Фазы в Model |

**Ключевое отличие:** в Haskell управление явное (handle'ы), в Agdelte — декларативное (events). Результат тот же, но без ручного управления ресурсами.

### STM (Software Transactional Memory)

Haskell async имеет мощную интеграцию с STM для координации конкурентных процессов.

**Многие паттерны STM уже покрыты в Agdelte:**

| STM паттерн | Аналог в Agdelte | Примечание |
|-------------|------------------|------------|
| `TVar` (следить за изменениями) | `changes` на Signal | Signal — дискретный поток, не TVar |
| `retry` (ждать условие) | `if cond then worker ... else never` | Декларативно через events |
| `orElse` (альтернатива) | `race` | Первый завершившийся |
| Атомарность | `update` атомарен | Один такт = атомарная операция |

**Когда нужен настоящий STM:**
- Сложная координация между множеством worker'ов
- Разделяемое мутабельное состояние между потоками
- Паттерны, которые трудно выразить через Event-комбинаторы

**Решение для серверной части:**

Серверная часть Agdelte компилируется в Haskell и исполняется на GHC. STM доступен напрямую:

```agda
-- На сервере: использовать STM из GHC
postulate
  TVar    : Set → Set
  newTVar : A → IO (TVar A)
  readTVar : TVar A → STM A
  writeTVar : TVar A → A → STM ⊤
  atomically : STM A → IO A

{-# COMPILE GHC TVar = type Control.Concurrent.STM.TVar #-}
{-# COMPILE GHC atomically = Control.Concurrent.STM.atomically #-}
```

**Архитектура клиент-сервер:**

```
┌─────────────────────────────────────────────────────────────┐
│                        Agdelte                              │
├─────────────────────────────────────────────────────────────┤
│  Клиент (JS)          │  Сервер (GHC)                       │
│  ─────────────        │  ────────────                       │
│  Web Workers          │  Green threads (миллионы)           │
│  Event-модель         │  Event-модель + STM                 │
│  SharedArrayBuffer    │  MVar, TVar, Chan                   │
└─────────────────────────────────────────────────────────────┘
```

Клиент и сервер используют одну Event-модель. Сервер дополнительно имеет доступ к STM для сложной координации.

### Итог сравнения с Haskell async

| | Haskell async | Agdelte |
|--|---------------|---------|
| Выразительность | ✅ | ✅ эквивалентна |
| Безопасность | ⚠️ требует дисциплины | ✅ по построению |
| Structured concurrency | ⚠️ явно | ✅ по умолчанию |
| Унификация | ❌ отдельный API | ✅ единый Event |
| STM | ✅ | ✅ на сервере (GHC) |

**Вывод:** Agdelte конкурентность не уступает Haskell async в выразительности, превосходит в безопасности и унификации, имеет доступ к STM на сервере через GHC.

---

### Другие паттерны

#### Background computation

```agda
-- Простой случай: вычислить в фоне
background : (A → B) → A → Event B
background = worker
```

#### Debounced worker

```agda
-- Запустить worker только после паузы в вводе
debouncedWorker : ℕ → WorkerFn A B → Signal A → Event B
debouncedWorker ms fn input =
  switchMap (λ a → delay ms >> worker fn a) (changes input)
```

#### Cached worker

```agda
-- Кэшировать результаты
cachedWorker : Eq A → WorkerFn A B → A → Event B
cachedWorker eq fn a =
  case lookup a cache of
    Just b  → occur b          -- из кэша (одно дискретное событие)
    Nothing → map (cache!) (worker fn a)  -- вычислить и сохранить
```

#### Retry with backoff

```agda
-- Повторить при ошибке с экспоненциальной задержкой
retryWorker : ℕ → WorkerFn A B → A → Event (Either String B)
retryWorker maxRetries fn a = go 0 100
  where
    go : ℕ → ℕ → Event (Either String B)
    go n delayMs =
      if n >= maxRetries
      then occur (Left "Max retries exceeded")  -- одно дискретное событие
      else race
        [ map Right (worker fn a)
        , delay delayMs >> go (n + 1) (delayMs * 2)
        ]
```

---

## 11. Интеграция с App

### App остаётся неизменным

Worker'ы интегрируются через стандартный `events` — никаких расширений App не требуется:

```agda
record App (Msg : Set) (Model : Set) : Set where
  field
    init    : Model
    update  : Msg → Model → Model
    view    : Model → Html Msg
    events  : Model → Event Msg
    -- Worker'ы — просто ещё один Event в events
```

### Автоматическое управление

`events` достаточно для всех случаев:

```agda
events m = merge
  (domEvents m)
  (if m.computing then worker heavy m.data else never)
  (if m.fetching then request (get "/api") else never)
```

Runtime сам определяет:
- Какие worker'ы запустить
- Какие переиспользовать из пула
- Какие отменить

---

## Итого

### Примитивы конкурентности

| Примитив | Тип | Описание |
|----------|-----|----------|
| `worker` | `WorkerFn A B → A → Event B` | Вычисление в отдельном потоке |
| `workerWithProgress` | `WorkerFn A B → A → Event (Progress B)` | С отчётом о прогрессе |
| `parallel` | `List (Event A) → Event (List A)` | Параллельно, собрать все |
| `race` | `List (Event A) → Event A` | Параллельно, взять первый |
| `poolWorker` | `Pool → WorkerFn A B → A → Event B` | Через пул worker'ов |
| `channel` | `WorkerScript → Event (Channel S R)` | Двунаправленная связь |

### Связь с базовой архитектурой

```
README.md (базовая)                concurrency.md (расширение)
───────────────────                ────────────────────────────
Signal, Event          ◄────────   (используются как есть)
App, Html, Runtime     ◄────────   (используются как есть)

interval, request      ◄── тот ──► worker, parallel, race
websocket                же           channel, pool
                       паттерн:
                       дискретные
                       события
```

### Ключевой принцип

**Worker = ещё один Event-примитив, генерирующий дискретные события.** Конкурентность не меняет архитектуру — она добавляет новые примитивы, следующие той же модели:

- **Дискретность:** результат, прогресс, отмена — отдельные дискретные события
- **Декларативность:** `events m = if m.computing then worker f x else never`
- **Автоматическое управление:** подписка/отписка через runtime
- **Композиция:** `merge`, `mapE`, `filterE` работают одинаково
- **Structured concurrency:** следует из декларативной модели

### Когда использовать

```
┌─────────────────────────────────────────────────────────┐
│                    UI-приложение                         │
├─────────────────────────────────────────────────────────┤
│  95% кода: формы, списки, навигация, HTTP               │
│  ────────────────────────────────────────               │
│  → DOM events + request + interval                      │
│  → НЕ нужен модуль Concurrent/                          │
├─────────────────────────────────────────────────────────┤
│  5% кода: тяжёлые вычисления                            │
│  ────────────────────────────                           │
│  → worker, parallel                                     │
│  → импортировать Concurrent/ только здесь               │
└─────────────────────────────────────────────────────────┘
```

---

## Roadmap

> Конкурентность — **Phase 3** общего roadmap (после MVP и Extensions).
> См. [README.md](../README.md) для полного roadmap.

**Phase 3a: Базовая конкурентность**
- `worker : WorkerFn A B → A → Event B`
- Базовая отмена
- `parallel`, `race`

**Phase 3b: Расширенная конкурентность**
- `workerWithProgress`
- Worker pool
- Channels

**Phase 4: Продвинутое**
- SharedArrayBuffer
- Linear types для ресурсов
- Session types
- STM интеграция (серверная часть через GHC)
- Distributed workers
- GPU compute (WebGPU)
