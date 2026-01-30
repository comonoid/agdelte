# Signal — Synchronous Streams

From `Agdelte.Core.Signal`.

## Core Type

```agda
Signal : Set → Set
Signal A = ℕ → A     -- time-indexed stream
```

## Constructors

| Function | Type | Description |
|----------|------|-------------|
| `const` | `A → Signal A` | Constant signal |
| `fromList` | `A → List A → Signal A` | From list with default |

## Combinators

| Function | Type | Description |
|----------|------|-------------|
| `map` | `(A → B) → Signal A → Signal B` | Pointwise transform |
| `zipWith` | `(A → B → C) → Signal A → Signal B → Signal C` | Pointwise combine |
| `merge` | `Signal A → Signal A → Signal A` | Merge (left priority) |
| `pre` | `A → Signal A → Signal A` | Delay by one tick (initial value) |
| `delay` | `A → Signal A → Signal A` | = `pre` |
| `foldl` | `(A → B → A) → A → Signal B → Signal A` | Running fold |
| `scan` | `(A → B → A) → A → Signal B → Signal A` | = foldl |
| `sample` | `Signal A → ℕ → A` | Sample at tick N |
| `take` | `ℕ → Signal A → List A` | First N values |
