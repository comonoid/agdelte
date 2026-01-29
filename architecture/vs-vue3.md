# Agdelte vs Vue 3: Анализ сложности реализации фич

> Сравнение фич и подходов. Архитектура Agdelte: [README.md](README.md)
>
> **Примечание:** Agdelte использует **ReactiveApp** с шаблонами и биндингами (Svelte-style, без Virtual DOM).
> Некоторые примеры ниже используют старый `App` с `view` для иллюстрации паттернов — актуальный API см. в [doc/api.md](../doc/api.md).

## Полный список необходимых фич

### Ядро (Core)

| Фича | Описание |
|------|----------|
| Реактивность | Автоматическое обновление при изменении данных |
| Условный рендеринг | v-if, v-else, v-show |
| Списки | v-for с key для оптимизации |
| События | Обработка DOM событий |
| Двусторонняя привязка | v-model для форм |
| Вычисляемые значения | computed, производные данные |
| Наблюдатели | watch, реакция на изменения |

### Компоненты

| Фича | Описание |
|------|----------|
| Props | Передача данных в компонент |
| Events (emit) | Передача событий из компонента |
| Slots | Передача контента в компонент |
| Scoped slots | Slots с доступом к данным компонента |
| provide/inject | Передача данных через дерево без props |
| Async components | Ленивая загрузка компонентов |
| Dynamic components | Переключение компонентов |

### Lifecycle и состояние

| Фича | Описание |
|------|----------|
| Lifecycle hooks | onMounted, onUnmounted, etc. |
| KeepAlive | Сохранение состояния при переключении |
| Локальное состояние | Состояние внутри компонента |
| Composables | Переиспользуемая логика с состоянием |

### Специальные возможности

| Фича | Описание |
|------|----------|
| Teleport | Рендеринг в другое место DOM |
| Transition | Анимации появления/исчезновения |
| TransitionGroup | Анимации списков |
| Suspense | Ожидание async компонентов |
| Template refs | Доступ к DOM элементам |
| Custom directives | Пользовательские директивы |

### Инфраструктура

| Фича | Описание |
|------|----------|
| SSR | Server-Side Rendering |
| Hydration | Подключение к SSR-разметке |
| DevTools | Инструменты отладки |
| HMR | Hot Module Replacement |
| Scoped CSS | Изолированные стили |

---

## Сложность реализации в Agdelte

### Категория A: Тривиально (уже есть или очевидная реализация)

| Фича Vue | В Agdelte | Почему просто |
|----------|-----------|---------------|
| ref/reactive | Signal | Это и есть Signal |
| computed | map, Applicative | `doubled = (2 *_) <$> count` |
| v-if/v-else | if/else в view | Обычный код |
| v-show | style display | `style [("display", "none")]` |
| v-for | map | `map viewItem items` |
| v-for :key | key атрибут | Добавить в diff алгоритм |
| v-on | onClick, onInput | Уже есть |
| v-model | value + onInput | Хелпер: `vmodel msg val` |
| Props | Аргументы функций | `view : Props → Html Msg` |
| emit | Msg | Возвращается через onClick и т.д. |
| Slots | Html как аргумент | `card : Html Msg → Html Msg` |
| Scoped slots | Функция | `list : (A → Html Msg) → List A → Html Msg` |
| watch | events от Model | `events m = if changed ... then ...` |
| Async components | Event (Html Msg) | Загрузка как событие |
| Dynamic components | case в view | `case m.tab of ...` |
| KeepAlive | Model хранит всё | Состояние не теряется |

**Итого: ~16 фич — сложность 0-1**

### Категория B: Небольшая работа (понятно как, нужно написать)

| Фича Vue | В Agdelte | Работа |
|----------|-----------|--------|
| Keyed diff | Изменить diffChildren | Алгоритм известен (React/Vue) |
| Teleport | Runtime поддержка | ~50 строк в runtime |
| Transition (CSS) | Runtime + классы | enter/leave классы |
| Suspense | Паттерн | `hold fallback asyncContent` |
| provide/inject | Model или implicit args | Выбрать паттерн |

**Итого: ~5 фич — сложность 2-3**

### Категория C: Требует проектирования

| Фича Vue | В Agdelte | Вопросы |
|----------|-----------|---------|
| TransitionGroup | FLIP анимации | Координация, алгоритм FLIP |
| Scoped CSS | Tooling | Bundler plugin или CSS-in-JS |
| SSR | renderToString + hydrate | Много кода, алгоритмы известны |
| DevTools | Browser extension | UI работа |
| HMR | Bundler интеграция | Vite/Webpack plugin |

**Итого: ~5 фич — сложность 4-6**

---

## Фичи, которые КАЖУТСЯ сложнее из-за архитектуры

### 1. Локальное состояние компонента

**Vue:**
```javascript
const localCount = ref(0)  // живёт в компоненте
```

**Agdelte:** Всё состояние в глобальном Model.

**Кажется сложнее?** Нет. Это другой паттерн:

```agda
-- Вариант 1: Вложенная модель
record Model : Set where
  counter1 : ℕ
  counter2 : ℕ

-- Вариант 2: Map для динамических компонентов
record Model : Set where
  counters : Map Id ℕ
```

**Elm доказал:** Глобальное состояние работает для приложений любого размера. Нужны хелперы (линзы), но это библиотека, не архитектура.

**Сложность реализации фичи: 0** (уже работает)
**Нужно:** Библиотека линз для удобства (~2)

---

### 2. Composables (переиспользуемая логика)

**Vue:**
```javascript
function useCounter() {
  const count = ref(0)
  const increment = () => count.value++
  return { count, increment }
}
```

**Agdelte:**
```agda
-- Модуль с параметризованными типами
module Counter where
  data Msg = Inc | Dec

  update : Msg → ℕ → ℕ
  update Inc n = suc n
  update Dec n = pred n

  view : ℕ → (Msg → parentMsg) → Html parentMsg
  view n wrap = button [ onClick (wrap Inc) ] [ text "+" ]
```

**Сложнее?** Нет. Это стандартный функциональный паттерн — модули и higher-order functions.

**Сложность реализации фичи: 0** (это просто модули Agda)
**Нужно:** Документация и примеры (~1)

---

### 3. Lifecycle hooks (onMounted, onUnmounted)

**Vue:**
```javascript
onMounted(() => console.log('mounted'))
onUnmounted(() => clearInterval(id))
```

**Agdelte:** Нет явных lifecycle hooks, но:

```agda
-- onMounted: событие при первом появлении
events m = if m.justMounted then ... else never

-- onUnmounted: автоматически!
-- Когда events возвращает never — отписка происходит
-- Runtime сам очищает ресурсы
```

**Сложнее?** ПРОЩЕ! В Vue нужно помнить про cleanup. В Agdelte cleanup автоматический — Event исчез из events → отписка.

**Сложность: 0** (уже работает лучше чем в Vue)

---

### 4. Template refs (доступ к DOM)

**Vue:**
```javascript
const inputRef = ref(null)
onMounted(() => inputRef.value.focus())
```

**Agdelte:**
```agda
-- Вариант 1: через id + Event
input [ id "my-input" ] []

events m = if m.needFocus then focus "my-input" else never

-- Вариант 2: autofocus атрибут (для простых случаев)
input [ autofocus ] []
```

**Сложнее?** По-другому. Декларативный подход вместо императивного.

**Сложность реализации `focus` примитива: ~1**

---

### 5. Custom directives

**Vue:**
```javascript
app.directive('focus', {
  mounted: (el) => el.focus()
})
```

**Agdelte:** Директивы — это атрибуты с особым поведением:

```agda
-- v-focus становится:
autofocus : Attr Msg

-- v-click-outside становится:
onClickOutside : Msg → Attr Msg
```

**Сложнее?** Нет. Каждая директива — это атрибут. Нет "общего механизма директив", но он и не нужен — атрибуты покрывают все случаи.

**Сложность каждой "директивы": ~1-2**

---

## Вывод: Есть ли фичи, которые ЗАМЕТНО труднее?

### Ответ: НЕТ

При правильном понимании архитектуры **ни одна фича не сложнее**. Некоторые — проще (lifecycle, cleanup). Некоторые — по-другому (локальное состояние, composables).

**Что выглядит сложнее для пользователя (не для реализации!):**

| Аспект | Vue | Agdelte |
|--------|-----|---------|
| Добавить поле состояния | 1 строка: `ref(0)` | 3 места: Model, Msg, update |
| Локальный счётчик | В компоненте | В глобальном Model |

Но это **эргономика использования**, не **сложность реализации фреймворка**.

---

## Правильная последовательность реализации

Если реализовывать в правильном порядке, каждая следующая фича опирается на предыдущие:

### Phase 1-2: Завершено ✅

Core, примитивы IO, ReactiveApp, 9 примеров, рантайм без VDOM.

### Phase 3-4: Комбинаторы и формальные свойства

Расширение Event API, доказательства линз.

### Phase 5: Инкрементальные обновления

Keyed foreach, вложенные биндинги, анимации.

### Phase 6-7: Concurrency и DX

Worker pools, DevTools, hot reload.

Полный roadmap: [README.md](../README.md#roadmap).

---

## Сравнение сложности

| Категория | Количество фич | Сложность |
|-----------|----------------|-----------|
| Тривиально | ~16 | 0-1 |
| Небольшая работа | ~5 | 2-3 |
| Проектирование | ~5 | 4-6 |

**Ключевое отличие от Vue:**

- **Vue:** Нужно изобретать реактивность (Proxy), Virtual DOM, компилятор шаблонов
- **Agdelte:** Signal/Event — известная модель из FRP, Runtime проще, теория (Poly) гарантирует корректность

---

## Что Agdelte получает "бесплатно" из архитектуры

| Фича | В Vue | В Agdelte |
|------|-------|-----------|
| Time-travel debugging | Плагин, сложно | Тривиально (список Model) |
| Undo/Redo | Писать руками | `history[n-1]` |
| Сериализация состояния | Сложно (Proxy) | `JSON.stringify(model)` |
| Воспроизведение багов | Сложно | Записать Msg, воспроизвести |
| Тестирование update | Моки | `update msg model ≡ expected` |
| Отмена запросов | AbortController вручную | Автоматически |
| Cleanup ресурсов | onUnmounted (забыть легко) | Автоматически |
| Race conditions | Возможны | Невозможны |

---

## Финальный ответ

### Вопрос: Есть ли фичи, которые заметно труднее из-за архитектуры?

**Ответ: НЕТ.**

Все фичи Vue 3 реализуемы в Agdelte с сопоставимой или меньшей сложностью.

### Вопрос: Что требует другого подхода?

1. **Локальное состояние** → Вложенные модели + линзы
2. **Composables** → Модули + higher-order functions
3. **Императивный DOM доступ** → Декларативные Events (focus, blur)
4. **Custom directives** → Атрибуты

### Вопрос: Что требует работы (но не из-за архитектуры)?

1. **Tooling:** SSR, DevTools UI, HMR, Scoped CSS
2. **Документация:** Паттерны композиции, примеры

### Вопрос: Правильная ли последовательность устраняет сложности?

**ДА.** При правильной последовательности:
- Каждая фича опирается на предыдущие
- Нет "архитектурных тупиков"
- Сложность растёт линейно, не экспоненциально

---

## Резюме

**Архитектура Agdelte не создаёт дополнительной сложности для реализации фич Vue 3.**

- Некоторые фичи **проще** (cleanup, time-travel, отмена запросов)
- Некоторые требуют **других паттернов** (локальное состояние → вложенные модели)
- Все реализуемы с **сопоставимой сложностью**

**Преимущество Agdelte:** теоретический фундамент (Polynomial Functors) в изолированном модуле `Theory/` гарантирует, что архитектура не приведёт в тупик:

- **Phase 1-2 (done):** простые определения для пользователя, ReactiveApp
- **Phase 3+:** Poly используется внутри комбинаторов (гарантии by construction)
- **Phase 6+:** Wiring diagrams для сложных систем

Комбинаторы композируются корректно по построению.
