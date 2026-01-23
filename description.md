# Agdelte

## Что это

Svelte 5 ввёл Runes — `$state`, `$derived`, `$effect`. Явная реактивность вместо магии. Правильный шаг, но Runes остаются надстройкой над компилятором: TypeScript о них не знает, это специальный синтаксис, который Svelte трансформирует при сборке.

Agdelte показывает, как реактивность выглядит в языке с настоящей системой типов. Не порт Svelte, а переосмысление: те же идеи, но выраженные через Functor, Applicative, монады — стандартные абстракции, которые работают не только для сигналов.

---

## Почему не Runes

TypeScript — хороший язык, но ему не хватает:

**Системы эффектов.** Обе функции имеют тип `number → number`, хотя одна чистая, а другая мутирует глобальное состояние:

```typescript
const pure = (x: number): number => x * 2;
const impure = (x: number): number => { globalState = x; return x * 2; };
```

**Higher-Kinded Types.** Нельзя абстрагироваться над Signal, Array, Promise одновременно — приходится дублировать код:

```typescript
function mapArray<A, B>(f: (a: A) => B, xs: A[]): B[] { ... }
function mapSignal<A, B>(f: (a: A) => B, s: Signal<A>): Signal<B> { ... }
function mapPromise<A, B>(f: (a: A) => B, p: Promise<A>): Promise<B> { ... }
```

**Зависимых типов.** Нельзя выразить "сигнал зависит от сигналов X и Y", нельзя доказать отсутствие циклов в графе зависимостей.

Поэтому Svelte строит параллельную систему поверх компилятора. В Agda всё это выражается средствами языка.

---

## Правильный подход

### Signal как Functor

Вместо специального `$derived`:

```typescript
// Svelte
let doubled = $derived(count * 2);
```

Signal — обычный Functor:

```agda
doubled : Signal ℕ
doubled = (2 *_) <$> count
```

`<$>` — стандартная операция, один синтаксис для List, Maybe, IO, Signal, Parser.

### Signal как Applicative

Комбинирование нескольких сигналов:

```typescript
// Svelte
let sum = $derived(a + b);
```

```agda
sum : Signal ℕ
sum = ⦇ a + b ⦈
```

Idiom brackets — стандартный Applicative, работает для любого типа с такой структурой.

### Эффекты в типах

```agda
pure   : ℕ → ℕ        -- гарантированно чистая
impure : ℕ → IO ℕ     -- эффекты явны
```

Компилятор не даст вызвать `impure` в чистом контексте.

---

## Три уровня

Код в Agdelte делится на три уровня по типу эффектов. Это деление достаточно простое для MVP, но годится и для production — большинству приложений не нужно больше. В дальнейшем, если понадобится более тонкий контроль (мокать HTTP отдельно от таймеров, ограничивать компоненты по типу эффектов), можно применить полноценную effect system поверх этой структуры.

```
┌─────────────────────────────────────┐
│  Чистый                             │  Signal как Applicative
│  view, derived, бизнес-логика       │  90% кода
├─────────────────────────────────────┤
│  Sig                                │  Монада для сигналов
│  создание, чтение, запись           │  Синхронно, локально
├─────────────────────────────────────┤
│  IO                                 │  Внешний мир
│  HTTP, таймеры, storage             │  Асинхронно, недетерминизм
└─────────────────────────────────────┘
```

### Чистый уровень

Большая часть кода — комбинирование сигналов через Applicative:

```agda
-- Декларация зависимостей, не императивное чтение
doubled : Signal ℕ
doubled = (2 *_) <$> count

total : Signal ℕ
total = ⦇ price * quantity ⦈

view : Signal Html
view = renderCart <$> items
```

Это чистые значения. Runtime сам отслеживает зависимости и обновляет.

### Sig — монада для сигналов

Создание и изменение состояния:

```agda
state  : A → Sig (Signal A)
get    : Signal A → Sig A
set    : Signal A → A → Sig ⊤
update : Signal A → (A → A) → Sig ⊤
```

Sig — это State monad над хранилищем сигналов:

```agda
-- Хранилище: отображение Id → значение
SignalStore = Map SignalId Dynamic

-- Sig — функция из хранилища в (результат, новое хранилище)
Sig : Set → Set
Sig A = SignalStore → (A × SignalStore)

-- pure: вернуть значение, не менять хранилище
pure : A → Sig A
pure a = λ store → (a , store)

-- bind: выполнить первое, передать результат во второе
_>>=_ : Sig A → (A → Sig B) → Sig B
(ma >>= f) store =
  let (a , store') = ma store   -- выполнить ma
  in f a store'                 -- передать результат в f

-- Примитивные операции
state : A → Sig (Signal A)
state initial store =
  let id = freshId store
      store' = insert id initial store
  in (Signal id , store')

get : Signal A → Sig A
get (Signal id) store = (lookup id store , store)

set : Signal A → A → Sig ⊤
set (Signal id) value store = (tt , insert id value store)
```

Пример использования:

```agda
transferPoints : Signal ℕ → Signal ℕ → ℕ → Sig ⊤
transferPoints from to amount = do
  current ← get from           -- прочитать текущее значение
  when (current ≥ amount) do   -- если хватает
    update from (_∸ amount)    -- уменьшить источник
    update to (amount +_)      -- увеличить цель
```

Обработчики событий работают в Sig:

```agda
onClick : Sig ⊤
onClick = update count suc

onInput : String → Sig ⊤
onInput s = set inputValue s
```

Sig отделён от IO: синхронный, детерминированный, легко тестируется.

### IO — внешний мир

Всё, что выходит за пределы приложения:

```agda
-- HTTP
httpGet  : Url → IO (Either Error Response)
httpPost : Url → Body → IO (Either Error Response)

-- Таймеры
setTimeout  : ℕ → IO ⊤ → IO TimerId
setInterval : ℕ → IO ⊤ → IO TimerId
clearTimeout : TimerId → IO ⊤

-- Storage
localGet : String → IO (Maybe String)
localSet : String → String → IO ⊤

-- Навигация
getLocation : IO Url
pushState   : Url → IO ⊤

-- Прочее
now    : IO Timestamp
random : IO Float
log    : String → IO ⊤
```

Sig поднимается в IO через `liftSig`:

```agda
onSubmit : IO ⊤
onSubmit = do
  form ← liftSig (get formData)
  resp ← httpPost "/api" form
  liftSig (set response resp)
```

### Почему разделение

| | Sig | IO |
|-|-----|-----|
| Состояние | Локальное | Внешний мир |
| Синхронность | Да | Не всегда |
| Детерминизм | Да | Нет |
| Тестируемость | Легко | Нужны заглушки |

Типы документируют намерение:

```agda
increment : Sig ⊤           -- только меняет состояние
fetchUser : UserId → IO User -- лезет в сеть
```

---

## HTML

### Типизированные элементы

```agda
data Tag : Set where
  div span p button input form table tr td : Tag

Attrs : Tag → Set
Attrs button = record { onClick : Maybe (Sig ⊤); disabled : Maybe Bool; ... }
Attrs input  = record { value : Maybe String; onInput : Maybe (String → Sig ⊤); ... }
Attrs _ = CommonAttrs
```

### Пример компонента

```agda
module Counter where

open import Agdelte

count : Signal ℕ
count = state 0

view : Signal Html
view = do
  c ← count
  pure $ div []
    [ button [ onClick (update count pred) ] [ text "-" ]
    , span [] [ text (show c) ]
    , button [ onClick (update count suc) ] [ text "+" ]
    ]
```

Или через Applicative:

```agda
view : Signal Html
view = renderCounter <$> count
  where
    renderCounter c = div []
      [ button [ onClick (update count pred) ] [ text "-" ]
      , span [] [ text (show c) ]
      , button [ onClick (update count suc) ] [ text "+" ]
      ]
```

### Типобезопасная структура

```agda
-- table принимает только thead/tbody
data TableChild : Set where
  thead : List (Element th) → TableChild
  tbody : List (Element tr) → TableChild

table : List Attr → List TableChild → Html
```

Невалидная структура не компилируется.

---

## Full-Stack

Если сервер тоже на Agda, часть кода становится общей.

### Ограничение

Разные backend'ы компилятора:

```
Клиент: Agda --js→ JavaScript (браузер)
Сервер: Agda --ghc→ Haskell (или --js→ Node.js)
```

Это означает разный FFI: `{-# COMPILE JS #-}` ≠ `{-# COMPILE GHC #-}`.

### Что общее

Чистый код без FFI работает везде:

```agda
-- Shared/Types.agda
record User : Set where
  field
    id   : ℕ
    name : List Char
    email : List Char

-- Shared/Logic.agda
discount : Order → ℕ
discount order = if total order > 1000 then 10 else 0

validate : Form → Maybe ValidForm
```

Один тип, одна валидация, одна бизнес-логика — на клиенте и сервере.

### Что раздельное

Платформенный код:

```agda
-- Client/Http.agda
httpPost : Url → Body → IO Response  -- {-# COMPILE JS fetch... #-}

-- Server/Http.agda
httpPost : Url → Body → IO Response  -- {-# COMPILE GHC http-client... #-}
```

### Структура проекта

```
src/
  Shared/           -- чистый код
    Types.agda
    Validation.agda
    Logic.agda
  Client/           -- браузер
    FFI.agda
    App.agda
  Server/           -- сервер
    FFI.agda
    Api.agda
```

### Упрощённый вариант

Оба на `--js`:

```
Клиент: Agda --js→ браузер
Сервер: Agda --js→ Node.js
```

Один FFI, проще согласование.

---

## Архитектура

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   .agda     │ ──▶ │    Agda     │ ──▶ │     .js     │
│ компоненты  │     │  compiler   │     │   bundle    │
└─────────────┘     └─────────────┘     └─────────────┘
```

Никакого специального компилятора. Стандартный Agda с `--js`. Реактивность — часть системы типов.

---

## Сравнение

| Runes (Svelte) | Agdelte |
|----------------|---------|
| Магия компилятора | Стандартные абстракции |
| `$state`, `$derived`, `$effect` | Signal (Functor/Applicative), Sig, IO |
| TypeScript не знает о Runes | Всё в системе типов |
| Один map для каждого типа | Один fmap для всех Functor |
| Циклы → runtime error | Возможно: циклы → ошибка компиляции |
| Эффекты невидимы | Sig и IO в типе |

---

## FRP

Functional Reactive Programming существует с 1997 года (Conal Elliott, Fran). В Haskell: reflex, reactive-banana, Yampa.

Svelte 5 переоткрыл эти идеи для веб-разработчиков. Agdelte показывает их в чистом виде.

---

## Roadmap

**Phase 1: Ядро**
- Signal как Functor/Applicative
- Sig монада
- Базовый IO (HTTP, таймеры, storage)
- FFI к DOM

**Phase 2: HTML**
- Типизированный DSL
- События
- Рендеринг

**Phase 3: Компоненты**
- Props как записи
- Lifecycle
- Композиция

**Phase 4: Гарантии**
- Зависимости сигналов в типах
- Доказательство отсутствия циклов

---

## Открытые вопросы

1. **Bundle size** — Agda runtime может быть большим
2. **Debugging** — source maps?
3. **Hot reload** — возможен ли?
4. **Интероп** — типизация JS-библиотек

---

## Заключение

Svelte показал веб-разработчикам, что реактивность может быть явной. Agdelte показывает, что она может быть типобезопасной:

- Functor/Applicative вместо `$derived`
- Sig для состояния, IO для внешнего мира
- Эффекты видны в типах
- Чистый код отделён от эффектов

Runes — правильная идея, ограниченная инструментом. Agdelte — та же идея без ограничений.
