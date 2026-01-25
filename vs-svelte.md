# Svelte 5 vs Agdelte: Сравнение примеров

10 примеров с анализом достоинств и недостатков обоих подходов.

---

## 1. Счётчик (базовая реактивность)

### Svelte 5

```svelte
<script>
  let count = $state(0)
</script>

<button onclick={() => count++}>
  Clicked {count} times
</button>
```

### Agdelte

```agda
data Msg = Inc

counter : App Msg ℕ
counter = record
  { init   = 0
  ; update = λ { Inc n → suc n }
  ; view   = λ n → button [ onClick Inc ] [ text ("Clicked " ++ show n ++ " times") ]
  ; events = λ _ → never
  }
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Краткость** | ✅ 5 строк | ❌ 10 строк |
| **Явность** | ❌ Мутация скрыта | ✅ Всё явно: Msg → update |
| **Типизация** | ⚠️ TypeScript (опционально) | ✅ Зависимые типы |
| **Тестируемость** | ⚠️ Нужен DOM/mock | ✅ `update Inc 0 ≡ 1` |

**Svelte лучше:** быстрое прототипирование, меньше boilerplate.

**Agdelte лучше:** предсказуемость, доказуемость, тестируемость.

---

## 2. Двусторонняя привязка (input)

### Svelte 5

```svelte
<script>
  let name = $state('')
</script>

<input bind:value={name} />
<p>Hello, {name}!</p>
```

### Agdelte

```agda
data Msg = SetName String

app : App Msg String
app = record
  { init   = ""
  ; update = λ { (SetName s) _ → s }
  ; view   = λ name → div []
      [ input [ value name, onInput SetName ] []
      , p [] [ text ("Hello, " ++ name ++ "!") ]
      ]
  ; events = λ _ → never
  }
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Синтаксис** | ✅ `bind:value` — одна строка | ❌ Явный `value` + `onInput` |
| **Направление данных** | ⚠️ Двунаправленное (магия) | ✅ Однонаправленное (явное) |
| **Отладка** | ⚠️ Сложнее отследить источник | ✅ Всегда видно откуда данные |
| **Валидация** | ⚠️ Нужен отдельный `$effect` | ✅ В `update` естественно |

**Svelte лучше:** эргономика для простых форм.

**Agdelte лучше:** сложные формы с валидацией, отладка data flow.

---

## 3. Производные значения (derived)

### Svelte 5

```svelte
<script>
  let items = $state([1, 2, 3, 4, 5])
  let total = $derived(items.reduce((a, b) => a + b, 0))
  let average = $derived(total / items.length)
</script>

<p>Total: {total}, Average: {average}</p>
```

### Agdelte

```agda
record Model : Set where
  field items : List ℕ

-- Производные — просто функции
total : Model → ℕ
total m = sum (m .items)

average : Model → ℕ
average m = total m / length (m .items)

app : App Msg Model
app = record
  { ...
  ; view = λ m → p []
      [ text ("Total: " ++ show (total m) ++ ", Average: " ++ show (average m)) ]
  }
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Синтаксис** | ✅ `$derived` — декларативно | ✅ Просто функции |
| **Мемоизация** | ✅ Автоматическая | ⚠️ Вручную (если нужна) |
| **Композиция** | ⚠️ Только в компоненте | ✅ Обычные функции, легко тестировать |
| **Зависимости** | ⚠️ Отслеживаются runtime | ✅ Явные (аргументы функции) |

**Svelte лучше:** автоматическая мемоизация, меньше кода.

**Agdelte лучше:** производные — обычные функции, легко тестировать и переиспользовать.

---

## 4. Эффекты (side effects)

### Svelte 5

```svelte
<script>
  let count = $state(0)

  $effect(() => {
    console.log('Count changed:', count)
    document.title = `Count: ${count}`
  })
</script>
```

### Agdelte

```agda
-- Эффекты не внутри компонента!
-- Логирование — через middleware в runtime
-- document.title — через специальный Event

data Msg = Inc | SetTitle String

app = record
  { ...
  ; update = λ where
      Inc m → record m { count = suc (m .count); needTitleUpdate = true }
      (SetTitle _) m → record m { needTitleUpdate = false }

  ; events = λ m →
      if m .needTitleUpdate
      then mapE SetTitle (setDocumentTitle ("Count: " ++ show (m .count)))
      else never
  }

-- Или: title как часть view (декларативно)
-- view m = { body = ..., title = "Count: " ++ show (m.count) }
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Простота** | ✅ `$effect` — одна конструкция | ❌ Нужен отдельный Event примитив |
| **Чистота** | ❌ Эффекты везде | ✅ Эффекты только в events |
| **Предсказуемость** | ⚠️ Когда выполнится? | ✅ Явно: когда Event активен |
| **Тестирование** | ❌ Нужен mock DOM | ✅ update чистый, эффекты изолированы |

**Svelte лучше:** быстрая интеграция с императивным кодом.

**Agdelte лучше:** все эффекты явные, легче отлаживать и тестировать.

---

## 5. Условный рендеринг

### Svelte 5

```svelte
<script>
  let loggedIn = $state(false)
</script>

{#if loggedIn}
  <Dashboard />
{:else}
  <LoginForm />
{/if}
```

### Agdelte

```agda
view : Model → Html Msg
view m = if m .loggedIn
  then mapHtml DashboardMsg (dashboard m.user)
  else mapHtml LoginMsg loginForm
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Синтаксис** | ✅ `{#if}` — читаемый шаблон | ✅ Обычный `if-then-else` |
| **Вложенность** | ⚠️ `{:else if}` — многословно | ✅ `case`, pattern matching |
| **Типобезопасность** | ⚠️ Runtime проверки | ✅ Compile-time |
| **Exhaustiveness** | ❌ Нет проверки | ✅ Agda проверяет все случаи |

**Svelte лучше:** визуально ближе к HTML.

**Agdelte лучше:** pattern matching, проверка полноты cases.

---

## 6. Списки

### Svelte 5

```svelte
<script>
  let todos = $state([
    { id: 1, text: 'Learn Svelte', done: false },
    { id: 2, text: 'Build app', done: false }
  ])
</script>

<ul>
  {#each todos as todo (todo.id)}
    <li class:done={todo.done}>
      {todo.text}
    </li>
  {/each}
</ul>
```

### Agdelte

```agda
view : Model → Html Msg
view m = ul []
  (map viewTodo (m .todos))
  where
    viewTodo : Todo → Html Msg
    viewTodo t = li [ className (if t .done then "done" else "") ]
      [ text (t .text) ]
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Синтаксис** | ✅ `{#each}` с деструктуризацией | ✅ `map` — стандартная функция |
| **Keyed списки** | ✅ `(todo.id)` встроено | ⚠️ Нужен отдельный `keyed` (Phase 2) |
| **Производительность** | ✅ Оптимизированный diff | ⚠️ Без ключей — O(n) пересоздание |
| **Читаемость** | ✅ Шаблон похож на HTML | ✅ Функциональный стиль |

**Svelte лучше:** keyed списки из коробки, привычный синтаксис.

**Agdelte лучше:** `map` — универсальная функция, работает везде.

---

## 7. Загрузка данных (fetch)

### Svelte 5

```svelte
<script>
  let data = $state(null)
  let loading = $state(false)
  let error = $state(null)

  async function loadData() {
    loading = true
    error = null
    try {
      const res = await fetch('/api/data')
      data = await res.json()
    } catch (e) {
      error = e.message
    } finally {
      loading = false
    }
  }
</script>

<button onclick={loadData} disabled={loading}>
  {loading ? 'Loading...' : 'Load Data'}
</button>

{#if error}
  <p class="error">{error}</p>
{/if}

{#if data}
  <pre>{JSON.stringify(data, null, 2)}</pre>
{/if}
```

### Agdelte

```agda
data Status = Idle | Loading | Success Data | Failure String

data Msg = LoadData | GotData Response

app = record
  { init = { status = Idle }

  ; update = λ where
      LoadData m → record m { status = Loading }
      (GotData (ok _ body)) m → record m { status = Success (parse body) }
      (GotData (error _ msg)) m → record m { status = Failure msg }

  ; view = λ m → div []
      [ button [ onClick LoadData, disabled (isLoading m) ]
          [ text (if isLoading m then "Loading..." else "Load Data") ]
      , case m .status of λ where
          (Failure msg) → p [ className "error" ] [ text msg ]
          (Success d) → pre [] [ text (show d) ]
          _ → empty
      ]

  ; events = λ m → case m .status of λ where
      Loading → mapE GotData (request (get "/api/data"))
      _ → never
  }
  where
    isLoading m = m .status ≡ Loading
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Количество состояний** | ⚠️ 3 переменные (data, loading, error) | ✅ 1 ADT (Status) |
| **Невозможные состояния** | ❌ `loading=true, data=X` возможно | ✅ Исключены типом |
| **Отмена запроса** | ❌ Нужен AbortController вручную | ✅ Автоматически (убрать из events) |
| **Boilerplate** | ⚠️ try/catch/finally | ⚠️ Явный pattern matching |
| **Ретраи** | ❌ Вручную | ✅ Просто оставить в Loading |

**Svelte лучше:** привычный async/await, меньше кода для простых случаев.

**Agdelte лучше:** невозможные состояния исключены типами, автоматическая отмена.

---

## 8. Компоненты и props

### Svelte 5

```svelte
<!-- Button.svelte -->
<script>
  let { label, disabled = false, onclick } = $props()
</script>

<button {disabled} {onclick}>{label}</button>

<!-- Parent.svelte -->
<script>
  import Button from './Button.svelte'
</script>

<Button label="Click me" onclick={() => alert('clicked')} />
```

### Agdelte

```agda
-- Button как функция
button' : String → Bool → Msg → Html Msg
button' label disabled msg =
  button [ onClick msg, disabled disabled ] [ text label ]

-- Или как параметризованный модуль
module Button (Msg : Set) where
  record Props : Set where
    field
      label    : String
      disabled : Bool
      onClick  : Msg

  view : Props → Html Msg
  view p = button [ onClick (p .onClick), disabled (p .disabled) ]
    [ text (p .label) ]

-- Использование
view m = div []
  [ Button.view (record { label = "Click me"; disabled = false; onClick = Clicked })
  ]
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Инкапсуляция** | ✅ .svelte файл = компонент | ✅ Модуль = компонент |
| **Props типизация** | ⚠️ TypeScript (опционально) | ✅ Record с типами |
| **Default props** | ✅ `= false` в деструктуризации | ⚠️ Нужна функция-обёртка |
| **Простые случаи** | ✅ Компонент не нужен | ✅ Просто функция |

**Svelte лучше:** файловая система как структура, default props.

**Agdelte лучше:** компоненты — обычные функции/модули, унифицированная типизация.

---

## 9. События между компонентами

### Svelte 5

```svelte
<!-- Child.svelte -->
<script>
  import { createEventDispatcher } from 'svelte'
  const dispatch = createEventDispatcher()
</script>

<button onclick={() => dispatch('select', { id: 42 })}>
  Select
</button>

<!-- Parent.svelte -->
<script>
  function handleSelect(e) {
    console.log('Selected:', e.detail.id)
  }
</script>

<Child on:select={handleSelect} />
```

### Agdelte

```agda
-- Child
module Child where
  data Msg = Select ℕ

  view : Html Msg
  view = button [ onClick (Select 42) ] [ text "Select" ]

-- Parent
module Parent where
  data Msg = ChildMsg Child.Msg | Other

  update : Msg → Model → Model
  update (ChildMsg (Child.Select id)) m = handleSelect id m
  update Other m = ...

  view : Model → Html Msg
  view m = div []
    [ mapHtml ChildMsg Child.view  -- трансформация Msg
    ]
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Механизм** | ⚠️ Отдельный dispatch API | ✅ Просто типы (Msg) |
| **Типизация событий** | ❌ `e.detail` — any | ✅ `Child.Select ℕ` |
| **Bubbling** | ⚠️ Через `on:select` | ✅ Явный `mapHtml` |
| **Обработка** | ⚠️ Callback в шаблоне | ✅ Централизованно в update |

**Svelte лучше:** привычная модель DOM событий.

**Agdelte лучше:** типобезопасность, все обработчики в одном месте (update).

---

## 10. Глобальное состояние (stores)

### Svelte 5

```svelte
<!-- stores.js -->
import { writable } from 'svelte/store'
export const user = writable(null)
export const theme = writable('light')

<!-- Component.svelte -->
<script>
  import { user, theme } from './stores'
</script>

<p>User: {$user?.name}</p>
<button onclick={() => $theme = $theme === 'light' ? 'dark' : 'light'}>
  Toggle theme
</button>
```

### Agdelte

```agda
-- Всё состояние в одном Model
record Model : Set where
  field
    user  : Maybe User
    theme : Theme
    ...   -- остальное состояние приложения

data Msg = SetUser (Maybe User) | ToggleTheme | ...

-- Глобальное состояние = App Model
app : App Msg Model
app = record
  { init = { user = Nothing; theme = Light; ... }
  ; update = λ where
      (SetUser u) m → record m { user = u }
      ToggleTheme m → record m { theme = toggle (m .theme) }
      ...
  ; ...
  }

-- Доступ в любом view через Model
viewHeader : Model → Html Msg
viewHeader m = div []
  [ text ("User: " ++ maybe "Guest" name (m .user))
  , button [ onClick ToggleTheme ] [ text "Toggle theme" ]
  ]
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Модульность** | ✅ Отдельные stores | ⚠️ Один большой Model |
| **Реактивность** | ✅ Автоподписка через `$` | ✅ view получает весь Model |
| **Согласованность** | ⚠️ Stores независимы | ✅ Всё состояние атомарно |
| **Time-travel debug** | ❌ Сложно | ✅ Легко (один Model) |
| **Селекторы** | ⚠️ derived stores | ✅ Просто функции `Model → A` |

**Svelte лучше:** модульность, независимые stores для разных частей.

**Agdelte лучше:** единый источник правды, атомарные обновления, time-travel debugging.

---

## Сводная таблица

| Аспект | Svelte 5 | Agdelte |
|--------|----------|---------|
| **Кривая обучения** | ✅ Низкая | ⚠️ Требует Agda |
| **Boilerplate** | ✅ Минимум | ⚠️ Больше кода |
| **Типобезопасность** | ⚠️ Опциональная | ✅ Встроенная |
| **Тестируемость** | ⚠️ Нужны моки | ✅ Чистые функции |
| **Предсказуемость** | ⚠️ Неявная реактивность | ✅ Явный data flow |
| **Производительность** | ✅ Оптимизированная | ⚠️ Зависит от реализации |
| **Экосистема** | ✅ Богатая | ❌ Новая |
| **Инструменты** | ✅ DevTools, HMR | ⚠️ Базовые |

---

## Когда что выбрать

### Svelte лучше для:
- Быстрого прототипирования
- Небольших проектов
- Команд без опыта ФП
- Интеграции с существующим JS кодом
- Когда важна экосистема и инструменты

### Agdelte лучше для:
- Критичных приложений (финансы, медицина)
- Сложной бизнес-логики
- Когда нужны формальные гарантии
- Команд с опытом ФП
- Долгоживущих проектов с высокими требованиями к качеству
- Обучения FRP и зависимым типам

---

## Философское различие

**Svelte:** "Сделай просто, компилятор разберётся"
- Магия компилятора скрывает сложность
- Оптимизация для developer experience
- Императивный код выглядит декларативным

**Agdelte:** "Сделай явно, типы гарантируют"
- Явная модель данных и потока событий
- Оптимизация для correctness
- Декларативный код и есть декларативный

Оба подхода валидны — выбор зависит от приоритетов проекта.
