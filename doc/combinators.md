# Combinator Reference

> API reference. For conceptual understanding: [README.md](../README.md)

All combinators below are implemented. See [architecture note](#why-no-snapshot-attach-tag) for why classic FRP combinators (`snapshot`, `tag`, `hold`, `foldp`) are absent.

## Basic

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `never` | `Event A` | Never occurs | ✅ |
| `merge` | `Event A → Event A → Event A` | Combine streams | ✅ |
| `mapE` | `(A → B) → Event A → Event B` | Transform | ✅ |
| `filterE` | `(A → Bool) → Event A → Event A` | Filter | ✅ |
| `mapFilterE` | `(B → Maybe A) → Event B → Event A` | Map + filter | ✅ |
| `mergeAll` | `List (Event A) → Event A` | Merge list | ✅ |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Split by predicate | ✅ |
| `leftmost` | `List (Event A) → Event A` | First non-empty event (priority merge) | ✅ |

---

## Sampling

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `gate` | `(A → Bool) → Event A → Event A` | Filter by predicate | ✅ |

> **Architecture note:** Classic FRP combinators `snapshot`, `attach`, `tag`, `hold`, `changes` are unnecessary in Agdelte. The TEA architecture provides model access via `subs : Model → List (Event Msg)` — sampling is implicit through closure. For change detection, `Signal.changed` already exists. See [architecture note](#why-no-snapshot-attach-tag) below.

---

## Time-based

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `interval` | `ℕ → A → Event A` | Tick every N ms | ✅ |
| `timeout` | `ℕ → A → Event A` | Single event after N ms | ✅ |
| `debounce` | `ℕ → Event A → Event A` | After N ms pause | ✅ |
| `throttle` | `ℕ → Event A → Event A` | At most once per N ms | ✅ |

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

---

## Switching

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `switchE` | `Event A → Event (Event A) → Event A` | Switch Event source | ✅ |

---

## Merging

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `mergeAll` | `List (Event A) → Event A` | Merge list (concatenation) | ✅ |

> **Note:** `mergeWith` (merge with resolution function) was considered but doesn't fit Agdelte's async runtime — events dispatch independently, never simultaneously. Use `leftmost` for priority semantics.

---

## Accumulators

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `foldE` | `A → (B → A → A) → Event B → Event A` | Accumulate state across events | ✅ |
| `accumE` | `A → Event (A → A) → Event A` | Apply function events to accumulator | ✅ |
| `mapAccum` | `(B → S → S × A) → S → Event B → Event A` | Map with state | ✅ |

> **Architecture note:** Classic FRP combinators `foldp`, `hold`, `accumB` fold events into Signals. In Agdelte, `update : Msg → Model → Model` already IS `foldp` — Model is the Signal. No separate accumulator-to-Signal combinators are needed.

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

## Error Handling

Trivially built from `mapFilterE`, but useful as semantic combinators.

| Combinator | Type | Description | Status |
|------------|------|-------------|--------|
| `filterOk` | `Event (Result E A) → Event A` | Only successes | ✅ |
| `filterErr` | `Event (Result E A) → Event E` | Only errors | ✅ |
| `partitionResult` | `Event (Result E A) → Event A × Event E` | Split | ✅ |

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

---

## Why no snapshot, attach, tag?

Agdelte uses TEA (The Elm Architecture), not classic FRP. The key difference:

**Classic FRP** (Reflex, reactive-banana): Events and Signals/Behaviors are independent first-class streams. To combine them, you need explicit combinators:
```
snapshot : (A → B → C) → Event A → Signal B → Event C
tag      : Signal A → Event B → Event A
hold     : A → Event A → Signal A
foldp    : (A → B → B) → B → Event A → Signal B
```

**Agdelte TEA**: Model IS the Signal. `subs : Model → List (Event Msg)` closes over the current state. Sampling is implicit:
```agda
-- "tag currentText saveClicks" in classic FRP becomes:
subs m = [ mapE (λ _ → SaveText m.currentText) saveClicks ]
--                                 ^^^^^^^^^^^
--                          direct model access, no "tag" needed
```

Similarly, `foldp`/`hold`/`accumB` are unnecessary because `update : Msg → Model → Model` already folds events into the Model signal.

This is not a limitation — it's a simpler architecture that eliminates an entire class of combinators.
