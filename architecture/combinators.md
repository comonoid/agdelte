# Combinator Reference

> API reference. For conceptual understanding: [README.md](README.md)
>
> **Note:** This document describes the target API. The current MVP implements a basic subset (`mapE`). Other combinators are reference documentation for future phases.

**Legend:**
- 🟢 MVP — intuitive, included in Phase 1
- 🟡 Phase 2 — requires separate study

## Basic 🟢

| Combinator | Type | Description |
|------------|------|-------------|
| `never` | `Event A` | Never occurs |
| `occur` | `A → Event A` | One event now |
| `merge` | `Event A → Event A → Event A` | Combine streams |
| `mapE` | `(A → B) → Event A → Event B` | Transform |
| `filterE` | `(A → Bool) → Event A → Event A` | Filter |
| `filterMap` | `(A → Maybe B) → Event A → Event B` | Map + filter |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Split by predicate |
| `split` | `Event (Either A B) → Event A × Event B` | Split Either |
| `leftmost` | `List (Event A) → Event A` | First event (priority) |
| `difference` | `Event A → Event A → Event A` | Set difference |

---

## Sampling (Event + Signal) 🟢

| Combinator | Type | Description |
|------------|------|-------------|
| `snapshot` | `(A → B → C) → Event A → Signal B → Event C` | Sample Signal |
| `attach` | `Event A → Signal B → Event (A × B)` | Attach Signal |
| `tag` | `Signal A → Event B → Event A` | Take Signal value |
| `sample` | `Event A → Signal B → Event B` | Synonym for tag |
| `gate` | `Event A → Signal Bool → Event A` | Filter by Signal |
| `changes` | `Signal A → Event A` | Change events |

### Examples

```agda
-- On "Save" click, take current text
saveClicks : Event ⊤
currentText : Signal String

savedText : Event String
savedText = tag currentText saveClicks

-- Collect form on submit
formSubmit : Event FormData
formSubmit = tag (pure mkForm <*> nameSignal <*> emailSignal) submitEvent

-- Clicks only when button is active
activeClicks : Event ⊤
activeClicks = gate rawClicks isEnabled
```

---

## Time-based 🟢

| Combinator | Type | Description |
|------------|------|-------------|
| `debounce` | `ℕ → Event A → Event A` | After N ms pause |
| `throttle` | `ℕ → Event A → Event A` | At most once per N ms |
| `delay` | `ℕ → Event A → Event A` | Delay by N ms |
| `timeout` | `ℕ → Event A → Event ⊤` | Event if silence for N ms |
| `after` | `ℕ → Event A → Event A` | N ms after |

### Debounce semantics

```
Input events:     [a]  []  [b]  []  []  []  [c]  []  []  []  []  []
Time (ms):         0   16   32  48  64  80  96  112 128 144 160 176
                   ↑        ↑                ↑
                   │        │                └─ reset timer
                   │        └─ reset timer
                   └─ start timer

debounce 50:      []  []  []  []  []  []  []  []  []  []  [c]  []
                                                          ↑
                                               50ms after last
```

### Throttle semantics

```
Input events:     [a]  [b]  [c]  []  []  []  [d]  [e]  []  []
Time (ms):         0   16   32  48  64  80  96  112 128 144
                   ↑    ↓    ↓              ↑    ↓
                   │    │    │              │    └─ ignored
                   │    │    │              └─ passes (period expired)
                   │    │    └─ ignored
                   │    └─ ignored
                   └─ passes, start period

throttle 50:      [a]  []  []  []  []  []  [d]  []  []  []
```

### Example: search with debounce

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

| Combinator | Type | Description |
|------------|------|-------------|
| `switchE` | `Event A → Event (Event A) → Event A` | Switch Event |
| `switchS` | `Signal A → Event (Signal A) → Signal A` | Switch Signal |
| `coincidence` | `Event (Event A) → Event A` | Join for Event |

### Example: tabs with different sources

```agda
events m =
  let tabChange = changes (pure m.currentTab)
      switched = switchE
        (currentTabEvents m.currentTab m)
        (mapE (λ tab → currentTabEvents tab m) tabChange)
  in mapE TabMsg switched
```

### Example: WebSocket switching

```agda
currentWs : Signal Url → Event WsEvent
currentWs serverUrl = switchE
  (websocket (serverUrl.now).recv)
  (mapE (λ url → websocket url .recv) (changes serverUrl))
```

---

## Merging

| Combinator | Type | Description | Phase |
|------------|------|-------------|-------|
| `mergeWith` | `(A → A → A) → Event A → Event A → Event A` | Merge with function | 🟢 |
| `mergeAll` | `(A → A → A) → A → Event A → Event A` | Fold all in tick | 🟢 |
| `alignWith` | `(These A B → C) → Event A → Event B → Event C` | Combine different types | 🟡 |
| `align` | `Event A → Event B → Event (These A B)` | Align events | 🟡 |

```agda
data These A B = This A | That B | Both A B
```

### Example: mergeWith for priorities

```agda
-- Local commands have priority over remote
commands : Event Command
commands = mergeWith (λ local _ → local) localCommands remoteCommands
```

### Example: alignWith for synchronization

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

| Combinator | Type | Description |
|------------|------|-------------|
| `foldp` | `(A → B → B) → B → Event A → Signal B` | Fold into Signal |
| `hold` | `A → Event A → Signal A` | Remember last |
| `accumE` | `A → Event (A → A) → Event A` | Fold into Event |
| `accumB` | `A → Event (A → A) → Signal A` | foldp with functions |
| `mapAccum` | `(A → S → S × B) → S → Event A → Event B` | Map + accumulate |

### Example: click counter

```agda
clicks : Event ⊤
counter : Signal ℕ
counter = foldp (λ _ n → suc n) 0 clicks

-- clicks  = [[], [tt], [], [tt, tt], [], ...]
-- counter = [0,  0,    1,  1,       3,  ...]
```

### Example: accumE for action history

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

### Example: mapAccum for numbering

```agda
numberEvents : Event A → Event (ℕ × A)
numberEvents = mapAccum (λ a n → (suc n, (n, a))) 0

-- events       = [[], [a], [b,c], [], [d], ...]
-- numberEvents = [[], [(0,a)], [(1,b),(2,c)], [], [(3,d)], ...]
```

---

## Deferred 🟢

| Combinator | Type | Description |
|------------|------|-------------|
| `pre` | `A → Signal A → Signal A` | Delay by one tick |
| `delayS` | `ℕ → A → Signal A → Signal A` | Delay by N ticks |
| `edge` | `Signal Bool → Event ⊤` | Event on edge |
| `risingEdge` | `Signal Bool → Event ⊤` | Rising edge |
| `fallingEdge` | `Signal Bool → Event ⊤` | Falling edge |

### Example: breaking cycle with pre

```agda
-- WITHOUT pre: infinite loop!
-- bad = map f bad

-- WITH pre: works
feedback : Signal ℕ
feedback = map suc (pre 0 feedback)
-- feedback = [0, 1, 2, 3, 4, ...]
```

---

## Error Handling 🟢

| Combinator | Type | Description |
|------------|------|-------------|
| `filterOk` | `Event (Result E A) → Event A` | Only successes |
| `filterErr` | `Event (Result E A) → Event E` | Only errors |
| `partitionResult` | `Event (Result E A) → Event A × Event E` | Split |
| `catchE` | `Event (Result E A) → (E → A) → Event A` | Handle error |

### Example: HTTP with error handling

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

| Combinator | Type | Description |
|------------|------|-------------|
| `interpret` | `(Event A → Event B) → List (List A) → List (List B)` | Test Event |
| `interpretS` | `(Signal A → Signal B) → List A → List B` | Test Signal |
| `interpretApp` | `App Msg Model → List (List Msg) → List Model` | Test App |
| `collectN` | `ℕ → Event A → List (List A)` | Collect N ticks |

### Test examples

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

## Note

`mapE` for Event differs from `map` for Signal:
- `map : (A → B) → Signal A → Signal B` — applies to `now`
- `mapE : (A → B) → Event A → Event B` — applies to each element in the list

Could be unified through Functor instance, but explicit names are clearer.
