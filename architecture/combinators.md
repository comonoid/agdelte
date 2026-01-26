# Справочник комбинаторов

> Справочник API. Концептуальное понимание: [README.md](README.md)

**Условные обозначения:**
- 🟢 MVP — интуитивно понятно, включено в Phase 1
- 🟡 Phase 2 — требует отдельного изучения

## Базовые 🟢

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

---

## Sampling (Event + Signal) 🟢

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `snapshot` | `(A → B → C) → Event A → Signal B → Event C` | Семплировать Signal |
| `attach` | `Event A → Signal B → Event (A × B)` | Приложить Signal |
| `tag` | `Signal A → Event B → Event A` | Взять значение Signal |
| `sample` | `Event A → Signal B → Event B` | Синоним tag |
| `gate` | `Event A → Signal Bool → Event A` | Фильтр по Signal |
| `changes` | `Signal A → Event A` | События изменения |

### Примеры

```agda
-- При клике "Save" взять текущий текст
saveClicks : Event ⊤
currentText : Signal String

savedText : Event String
savedText = tag currentText saveClicks

-- Собрать форму при отправке
formSubmit : Event FormData
formSubmit = tag (pure mkForm <*> nameSignal <*> emailSignal) submitEvent

-- Клики только когда кнопка активна
activeClicks : Event ⊤
activeClicks = gate rawClicks isEnabled
```

---

## Time-based 🟢

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `debounce` | `ℕ → Event A → Event A` | После паузы N мс |
| `throttle` | `ℕ → Event A → Event A` | Максимум раз в N мс |
| `delay` | `ℕ → Event A → Event A` | Задержка на N мс |
| `timeout` | `ℕ → Event A → Event ⊤` | Событие если тишина N мс |
| `after` | `ℕ → Event A → Event A` | Через N мс после |

### Семантика debounce

```
Входные события:  [a]  []  [b]  []  []  []  [c]  []  []  []  []  []
Время (мс):        0   16   32  48  64  80  96  112 128 144 160 176
                   ↑        ↑                ↑
                   │        │                └─ сброс таймера
                   │        └─ сброс таймера
                   └─ старт таймера

debounce 50:      []  []  []  []  []  []  []  []  []  []  [c]  []
                                                          ↑
                                               50мс после последнего
```

### Семантика throttle

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

### Пример: поиск с debounce

```agda
events m =
  let queryChanges = changes (pure (m.query))
      debouncedQuery = debounce 300 queryChanges
  in merge
    (mapE Search debouncedQuery)
    (if m.loading
     then mapE GotResults (request (searchApi m.query))
     else never)
```

---

## Switching 🟡

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `switchE` | `Event A → Event (Event A) → Event A` | Переключить Event |
| `switchS` | `Signal A → Event (Signal A) → Signal A` | Переключить Signal |
| `coincidence` | `Event (Event A) → Event A` | Join для Event |

### Пример: вкладки с разными источниками

```agda
events m =
  let tabChange = changes (pure m.currentTab)
      switched = switchE
        (currentTabEvents m.currentTab m)
        (mapE (λ tab → currentTabEvents tab m) tabChange)
  in mapE TabMsg switched
```

### Пример: переключение WebSocket

```agda
currentWs : Signal Url → Event WsEvent
currentWs serverUrl = switchE
  (websocket (serverUrl.now).recv)
  (mapE (λ url → websocket url .recv) (changes serverUrl))
```

---

## Merging

| Комбинатор | Тип | Описание | Phase |
|------------|-----|----------|-------|
| `mergeWith` | `(A → A → A) → Event A → Event A → Event A` | Merge с функцией | 🟢 |
| `mergeAll` | `(A → A → A) → A → Event A → Event A` | Свернуть все в такте | 🟢 |
| `alignWith` | `(These A B → C) → Event A → Event B → Event C` | Объединить разные типы | 🟡 |
| `align` | `Event A → Event B → Event (These A B)` | Выровнять события | 🟡 |

```agda
data These A B = This A | That B | Both A B
```

### Пример: mergeWith для приоритетов

```agda
-- Локальные команды приоритетнее удалённых
commands : Event Command
commands = mergeWith (λ local _ → local) localCommands remoteCommands
```

### Пример: alignWith для синхронизации

```agda
data Update = UserOnly User | ProfileOnly Profile | Both User Profile

syncedUpdates : Event Update
syncedUpdates = alignWith toUpdate userUpdates profileUpdates
  where
    toUpdate (This u)   = UserOnly u
    toUpdate (That p)   = ProfileOnly p
    toUpdate (Both u p) = Both u p
```

---

## Accumulators 🟢

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `foldp` | `(A → B → B) → B → Event A → Signal B` | Свёртка в Signal |
| `hold` | `A → Event A → Signal A` | Запомнить последнее |
| `accumE` | `A → Event (A → A) → Event A` | Свёртка в Event |
| `accumB` | `A → Event (A → A) → Signal A` | foldp с функциями |
| `mapAccum` | `(A → S → S × B) → S → Event A → Event B` | Map + accumulate |

### Пример: счётчик кликов

```agda
clicks : Event ⊤
counter : Signal ℕ
counter = foldp (λ _ n → suc n) 0 clicks

-- clicks  = [[], [tt], [], [tt, tt], [], ...]
-- counter = [0,  0,    1,  1,       3,  ...]
```

### Пример: accumE для истории действий

```agda
data Action = Increment | Double | Reset

toFn : Action → ℕ → ℕ
toFn Increment = suc
toFn Double    = λ n → n * 2
toFn Reset     = const 0

counterEvents : Event ℕ
counterEvents = accumE 0 (mapE toFn actions)

-- actions       = [[], [Inc], [Double, Inc], [], [Reset], ...]
-- counterEvents = [[], [1],   [3],           [], [0],     ...]
```

### Пример: mapAccum для нумерации

```agda
numberEvents : Event A → Event (ℕ × A)
numberEvents = mapAccum (λ a n → (suc n, (n, a))) 0

-- events       = [[], [a], [b,c], [], [d], ...]
-- numberEvents = [[], [(0,a)], [(1,b),(2,c)], [], [(3,d)], ...]
```

---

## Deferred 🟢

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `pre` | `A → Signal A → Signal A` | Задержка на такт |
| `delayS` | `ℕ → A → Signal A → Signal A` | Задержка на N тактов |
| `edge` | `Signal Bool → Event ⊤` | Событие на фронте |
| `risingEdge` | `Signal Bool → Event ⊤` | Передний фронт |
| `fallingEdge` | `Signal Bool → Event ⊤` | Задний фронт |

### Пример: разрыв цикла с pre

```agda
-- БЕЗ pre: бесконечный цикл!
-- bad = map f bad

-- С pre: работает
feedback : Signal ℕ
feedback = map suc (pre 0 feedback)
-- feedback = [0, 1, 2, 3, 4, ...]
```

---

## Error Handling 🟢

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `filterOk` | `Event (Result E A) → Event A` | Только успехи |
| `filterErr` | `Event (Result E A) → Event E` | Только ошибки |
| `partitionResult` | `Event (Result E A) → Event A × Event E` | Разделить |
| `catchE` | `Event (Result E A) → (E → A) → Event A` | Обработать ошибку |

### Пример: HTTP с обработкой ошибок

```agda
data HttpError = NetworkError String | Timeout | BadStatus ℕ | ParseError String

events m = case m.status of λ where
  InProgress →
    let response = requestSafe (get "/api/data")
        (oks, errs) = partitionResult response
    in merge
      (mapE (GotData ∘ parse) oks)
      (mapE (GotError ∘ showError) errs)
  _ → never
```

---

## Testing 🟡

| Комбинатор | Тип | Описание |
|------------|-----|----------|
| `interpret` | `(Event A → Event B) → List (List A) → List (List B)` | Тест Event |
| `interpretS` | `(Signal A → Signal B) → List A → List B` | Тест Signal |
| `interpretApp` | `App Msg Model → List (List Msg) → List Model` | Тест App |
| `collectN` | `ℕ → Event A → List (List A)` | Собрать N тактов |

### Примеры тестов

```agda
test_mapE : interpret (mapE suc) [[1,2], [], [3]] ≡ [[2,3], [], [4]]
test_mapE = refl

test_filterE : interpret (filterE (_> 2)) [[1,2,3], [4,1], []] ≡ [[3], [4], []]
test_filterE = refl

test_merge : interpret (λ e → merge e (mapE (*10) e)) [[1], [2]] ≡ [[1,10], [2,20]]
test_merge = refl

test_counter : interpretApp counterApp [[Inc], [Inc], [Inc]] ≡ [1, 2, 3]
test_counter = refl
```

---

## Примечание

`mapE` для Event отличается от `map` для Signal:
- `map : (A → B) → Signal A → Signal B` — применяет к `now`
- `mapE : (A → B) → Event A → Event B` — применяет к каждому элементу списка

Можно было бы унифицировать через Functor instance, но явные имена понятнее.
