# Svelte 5 vs Agdelte: Сравнение примеров

> Детальное сравнение подходов. Архитектура Agdelte: [README.md](README.md)
>
> **Ключевое сходство:** И Svelte, и Agdelte используют **прямые обновления DOM без Virtual DOM**.
> Разница в том, что Svelte достигает этого компиляцией, а Agdelte — явными биндингами.
>
> **Примечание:** Примеры ниже используют **ReactiveApp** (шаблон с биндингами).
> Для полного API см. [doc/api.md](../doc/api.md).

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

template : Node ℕ Msg
template = button [ onClick Inc ] [ bindF (λ n → "Clicked " ++ show n ++ " times") ]

app = mkReactiveApp 0 (λ { Inc n → suc n }) template
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Краткость** | ✅ 5 строк | ✅ 4 строки |
| **DOM обновления** | ✅ Прямые (компилятор) | ✅ Прямые (биндинги) |
| **Типизация** | ⚠️ TypeScript (опционально) | ✅ Зависимые типы |
| **Virtual DOM** | ❌ Нет | ❌ Нет |

**Общее:** Оба используют прямые DOM обновления без diffing!

**Svelte:** Компилятор генерирует код обновлений.

**Agdelte:** `bindF` явно указывает, что обновляется.

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

template : Node String Msg
template = div []
  ( input [ valueBind id, onInput SetName ] []
  ∷ p [] [ bindF (λ name → "Hello, " ++ name ++ "!") ]
  ∷ [] )

app = mkReactiveApp "" (λ { (SetName s) _ → s }) template
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Синтаксис** | ✅ `bind:value` — одна строка | ⚠️ `valueBind` + `onInput` |
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

template : Node Model Msg
template = p []
  [ bindF (λ m → "Total: " ++ show (total m) ++ ", Average: " ++ show (average m)) ]
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
template : Node Model Msg
template = div []
  ( when loggedIn (focusNode user dashboardTemplate)
  ∷ when (not ∘ loggedIn) loginTemplate
  ∷ [] )
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
template : Node Model Msg
template = ul []
  [ foreach todos (λ t _ →
      li [ classBind (λ _ → if done t then "done" else "") ]
        [ text (todoText t) ]
    ) ]
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

data Msg = LoadData | GotData String | GotError String

update : Msg → Model → Model
update LoadData m = record m { status = Loading }
update (GotData d) m = record m { status = Success (parse d) }
update (GotError e) m = record m { status = Failure e }

template : Node Model Msg
template = div []
  ( button [ onClick LoadData, disabledBind isLoading ]
      [ bindF (λ m → if isLoading m then "Loading..." else "Load Data") ]
  ∷ when isFailure (p [ class "error" ] [ bindF showError ])
  ∷ when isSuccess (pre [] [ bindF showData ])
  ∷ [] )

cmd : Msg → Model → Cmd Msg
cmd LoadData _ = httpGet "/api/data" GotData GotError
cmd _ _ = ε

app = mkReactiveApp initModel update template
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

## 11. Анимации (animationFrame)

### Svelte 5

```svelte
<script>
  import { onMount, onDestroy } from 'svelte'

  let position = $state(0)
  let velocity = 200  // px/sec
  let rafId
  let lastTime

  function animate(time) {
    if (lastTime) {
      const dt = time - lastTime
      position += velocity * dt / 1000
    }
    lastTime = time
    rafId = requestAnimationFrame(animate)
  }

  onMount(() => {
    rafId = requestAnimationFrame(animate)
  })

  onDestroy(() => {
    cancelAnimationFrame(rafId)
  })
</script>

<div style="transform: translateX({position}px)">●</div>
```

### Agdelte

```agda
data Msg = Tick FrameInfo | ToggleAnimation

record Model : Set where
  field
    position  : ℕ
    velocity  : ℕ
    animating : Bool

update : Msg → Model → Model
update (Tick frame) m = record m
  { position = m .position + m .velocity * frame .dt / 1000 }
update ToggleAnimation m = record m { animating = not (m .animating) }

template : Node Model Msg
template = div [ styleBind "transform" (λ m → "translateX(" ++ show (m .position) ++ "px)") ]
  [ text "●" ]

subs : Model → Event Msg
subs m = if m .animating
  then mapE Tick animationFrame  -- браузер даёт dt и fps
  else never                      -- автоматическая отмена RAF

app = mkReactiveApp initModel update template
```

### Анализ

| | Svelte | Agdelte |
|--|--------|---------|
| **Управление RAF** | ⚠️ Вручную (onMount/onDestroy) | ✅ Автоматически (events) |
| **Delta time** | ⚠️ Считать вручную | ✅ Готовый `frame.dt` |
| **FPS** | ❌ Нет | ✅ Готовый `frame.fps` |
| **Cleanup** | ⚠️ Можно забыть cancelAnimationFrame | ✅ Автоматический при `never` |
| **Пауза анимации** | ⚠️ Флаги, условия в animate | ✅ `if animating then ... else never` |

**Svelte лучше:** привычный императивный подход.

**Agdelte лучше:** декларативное управление анимацией, автоматический cleanup, встроенный dt/fps.

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

### Общее: No Virtual DOM!

И Svelte, и Agdelte отказались от Virtual DOM в пользу прямых обновлений DOM:

| | Virtual DOM (React/Elm) | Svelte | Agdelte |
|--|-------------------------|--------|---------|
| Как обновляется DOM | diff(oldTree, newTree) → patches | Компилятор генерирует `if (changed.x)` | `bindF` отслеживает изменения |
| Производительность | O(tree size) | O(changed bindings) | O(changed bindings) |
| Когда происходит анализ | Runtime | Compile time | Runtime (explicit bindings) |

### Разница: Магия vs Явность

**Svelte:** "Сделай просто, компилятор разберётся"
- Компилятор анализирует шаблон и генерирует оптимальные обновления
- Пользователь не видит как это работает
- Реактивность — свойство компилятора

**Agdelte:** "Сделай явно, типы гарантируют"
- `bindF show` явно говорит: "это место зависит от модели"
- Пользователь видит все реактивные связи
- Реактивность — явная структура данных

### Три слоя Agdelte

```
┌─────────────────────────────────────────────────────────┐
│  Level 3: Declarative DSL                               │
│  button [ onClick Dec ] [ bindF show ]                 │
│  Svelte-like syntax, explicit bindings                  │
├─────────────────────────────────────────────────────────┤
│  Level 2: Lenses                                        │
│  Navigation, modification, composition                  │
│  Runtime flexibility                                    │
├─────────────────────────────────────────────────────────┤
│  Level 1: Polynomials (Theory/)                         │
│  Mathematical foundation                                │
│  Formal guarantees, proofs                              │
└─────────────────────────────────────────────────────────┘
```

Svelte и Agdelte пришли к одному решению (No VDOM) разными путями:
- Svelte — через анализ компилятора
- Agdelte — через явные биндинги с типами
