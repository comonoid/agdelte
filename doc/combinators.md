# Combinator Reference

> API reference. For conceptual understanding: [README.md](../README.md)
>
> **Note:** This document describes the full target API. Items marked ✅ are implemented. Others are planned for future phases.

**Legend:**
- ✅ Implemented
- ⬚ Planned

## Basic

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `never` | `Event A` | Never occurs | ✅ |
| `merge` | `Event A → Event A → Event A` | Combine streams | ✅ |
| `mapE` | `(A → B) → Event A → Event B` | Transform | ✅ |
| `filterE` | `(A → Bool) → Event A → Event A` | Filter | ✅ |
| `mapFilterE` | `(B → Maybe A) → Event B → Event A` | Map + filter | ✅ |
| `mergeAll` | `List (Event A) → Event A` | Merge list | ✅ |
| `occur` | `A → Event A` | One event now | ⬚ |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Split by predicate | ⬚ |
| `split` | `Event (Either A B) → Event A × Event B` | Split Either | ⬚ |
| `leftmost` | `List (Event A) → Event A` | First event (priority) | ⬚ |
| `difference` | `Event A → Event A → Event A` | Set difference | ⬚ |

---

## Sampling (Event + Signal)

> In ReactiveApp, `subs : Model → Event Msg` provides model access via closure — `snapshot` is implicit.

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `gate` | `(A → Bool) → Event A → Event A` | Filter by predicate | ✅ |
| `snapshot` | `(A → B → C) → Event A → Signal B → Event C` | Sample Signal | ⬚ (implicit via subs) |
| `attach` | `Event A → Signal B → Event (A × B)` | Attach Signal | ⬚ |
| `tag` | `Signal A → Event B → Event A` | Take Signal value | ⬚ |
| `changes` | `Signal A → Event A` | Change events | ⬚ |

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

## Time-based

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `interval` | `ℕ → A → Event A` | Tick every N ms | ✅ |
| `timeout` | `ℕ → A → Event A` | Single event after N ms | ✅ |
| `debounce` | `ℕ → Event A → Event A` | After N ms pause | ✅ |
| `throttle` | `ℕ → Event A → Event A` | At most once per N ms | ✅ |
| `delay` | `ℕ → Event A → Event A` | Delay by N ms | ⬚ |
| `after` | `ℕ → Event A → Event A` | N ms after | ⬚ |

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

## Switching

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `switchE` | `Event A → Event (Event A) → Event A` | Switch Event | ✅ |
| `switchS` | `Signal A → Event (Signal A) → Signal A` | Switch Signal | ⬚ |
| `coincidence` | `Event (Event A) → Event A` | Join for Event | ⬚ |

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

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `mergeAll` | `List (Event A) → Event A` | Merge list | ✅ |
| `mergeWith` | `(A → A → A) → Event A → Event A → Event A` | Merge with function | ⬚ |
| `alignWith` | `(These A B → C) → Event A → Event B → Event C` | Combine different types | ⬚ |
| `align` | `Event A → Event B → Event (These A B)` | Align events | ⬚ |

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

## Accumulators

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `foldE` | `A → (B → A → A) → Event B → Event A` | Accumulate state across events | ✅ |
| `accumE` | `A → Event (A → A) → Event A` | Apply function events to accumulator | ✅ |
| `mapAccum` | `(B → S → S × A) → S → Event B → Event A` | Map with state | ✅ |
| `foldp` | `(A → B → B) → B → Event A → Signal B` | Fold into Signal | ⬚ (update IS foldp) |
| `hold` | `A → Event A → Signal A` | Remember last | ⬚ |
| `accumB` | `A → Event (A → A) → Signal A` | foldp with functions | ⬚ |

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

## Deferred

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

## Error Handling

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

## Testing (Phase 5) ✅

Implemented in `Agdelte.Test.Interpret`. Uses `SimEvent A = List (List A)` — pure list-based event streams.

| Function | Type | Description | Status |
|----------|------|-------------|--------|
| `simMapE` | `(A → B) → SimEvent A → SimEvent B` | Map | ✅ |
| `simFilterE` | `(A → Bool) → SimEvent A → SimEvent A` | Filter | ✅ |
| `simFoldE` | `A → (B → A → A) → SimEvent B → SimEvent A` | Fold | ✅ |
| `simAccumE` | `A → SimEvent (A → A) → SimEvent A` | Accumulate | ✅ |
| `simMerge` | `SimEvent A → SimEvent A → SimEvent A` | Merge | ✅ |
| `simMapFilterE` | `(A → Maybe B) → SimEvent A → SimEvent B` | Map + filter | ✅ |
| `interpretApp` | `(B → A → A) → A → SimEvent B → List A` | Test update | ✅ |
| `collectN` | `ℕ → SimEvent A → SimEvent A` | Collect N ticks | ✅ |

6 propositional equality proofs (`refl`) type-checked by Agda:

```agda
test-mapE    : simMapE suc (...) ≡ (...)           -- refl
test-filterE : simFilterE (...) ≡ (...)             -- refl
test-foldE   : simFoldE 0 (λ _ n → suc n) (...) ≡ (...)  -- refl
test-accumE  : simAccumE 0 (...) ≡ (...)            -- refl
test-app     : interpretApp (...) ≡ (...)           -- refl
test-merge   : simMerge (...) ≡ (...)               -- refl
```

---

## Note

`mapE` for Event differs from `map` for Signal:
- `map : (A → B) → Signal A → Signal B` — applies to `now`
- `mapE : (A → B) → Event A → Event B` — applies to each element in the list

Could be unified through Functor instance, but explicit names are clearer.
