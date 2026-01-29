# Concurrency in Agdelte

> **Status:** Planned (Phase 7). This document describes the architecture extension for concurrent computations.
>
> **Extension:** optional extension of the base architecture. See [doc/architecture.md](../doc/architecture.md).
>
> **Prerequisite:** familiarity with ReactiveApp, Event, Cmd. See [doc/api.md](../doc/api.md).
>
> **Key principle:** Worker generates **discrete events**, like all other primitives. No "continuity" — result, progress, cancellation — all are separate discrete events.

---

## When Concurrency is NOT Needed

**Most UI applications don't require this module.**

| Task | Need worker? | Why |
|------|--------------|-----|
| Forms, validation | No | Synchronous, < 1ms |
| Lists, filtering (< 1000 items) | No | Synchronous, < 16ms |
| HTTP requests | No | `request` is already async |
| WebSocket | No | `websocket` is already async |
| Timers, animations | No | `interval` is enough |
| Parsing large JSON (> 1MB) | Yes | Blocks UI |
| Cryptography | Yes | Heavy computation |
| Image processing | Yes | Lots of computation |
| ML inference | Yes | Very heavy |

**Rule:** if operation takes < 16ms — use synchronous code. Worker adds overhead (serialization, transfer, deserialization).

---

## Motivation

Base architecture: all IO is Event. Runtime in main thread, computations are synchronous.

Problem: **heavy** computations block UI.

```agda
-- Bad: blocks rendering
events m = if m.needsCompute
  then map Done (heavyComputation m.data)  -- 5 seconds in main thread
  else never
```

Solution: concurrent computations as Event. Computation goes to worker, result comes as event.

---

## Key Idea

**Worker is another Event primitive.** Just like `request` or `interval`:

```agda
-- Base primitives (all discrete!)
interval       : ℕ → Event ⊤              -- discrete ticks
animationFrame : Event FrameInfo          -- discrete events each frame
request        : Request → Event Response -- discrete response
websocket      : Url → WebSocket          -- discrete messages

-- Concurrency primitive (also discrete)
worker         : WorkerFn A B → A → Event B  -- discrete result
```

**Unified model (everything is discrete events):**

| Primitive | Subscribe | Discrete event | Unsubscribe |
|-----------|-----------|----------------|-------------|
| `interval n` | Start timer | `⊤` (tick) | Stop |
| `request r` | Send HTTP | `Response` (response) | Cancel |
| `worker f x` | Start computation | `B` (result) | Cancel |

Declarative model is preserved:
- Event appeared in `events(model)` → worker starts
- Event disappeared → worker is cancelled (if not yet finished)

**Composition works the same:**

```agda
events m = merge
  (mapE Tick (interval 1000))           -- timer
  (mapE GotData (request (get "/api"))) -- HTTP
  (mapE Done (worker heavy m.input))    -- concurrent computation
```

---

## 1. Basic Worker

### Definition

```agda
-- Function executed in worker
WorkerFn : Set → Set → Set
WorkerFn A B = A → B  -- pure function

-- Run computation in worker
worker : WorkerFn A B → A → Event B
```

### Example: factorization

```agda
-- Heavy function
factorize : ℕ → List ℕ
factorize n = ...  -- may take seconds

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
1. `computing = true` → spawn worker with `factorize`
2. Worker computes in separate thread
3. Result ready → Event `GotFactors`
4. `computing = false` → worker no longer needed

---

## 2. Progress and Cancellation

### Event with progress

```agda
data Progress (A : Set) : Set where
  Running  : ℕ → Progress A      -- discrete event: "now at 50%"
  Done     : A → Progress A       -- discrete event: result
  Cancelled : Progress A          -- discrete event: cancelled
  Failed   : String → Progress A  -- discrete event: error

workerWithProgress : WorkerFn A B → A → Event (Progress B)
```

**Important:** `Running 50` is **one discrete event**, not a "continuous stream of progress". Worker periodically sends discrete `Running n` events, each processed as a separate tick.

### Example: processing large file

```agda
data Msg = Process | Progress ℕ | Done Result | Cancel

app = record
  { ...
  ; update = λ where
      Process m → record m { processing = true; progress = 0 }
      (Progress p) m → record m { progress = p }
      (Done r) m → record m { processing = false; result = Just r }
      Cancel m → record m { processing = false }  -- cancellation

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

**Cancellation:** when user presses Cancel:
1. `update Cancel` sets `processing = false`
2. `events` returns `never`
3. Runtime sees that Event disappeared → cancels worker
4. Worker receives cancellation signal

---

## 3. Parallel Computations

### Combinators

```agda
-- Run in parallel, collect all results
parallel : List (Event A) → Event (List A)

-- Run in parallel, take first result
race : List (Event A) → Event A

-- Run sequentially
sequence : List (Event A) → Event (List A)
```

### Example: parallel chunk processing

```agda
processChunks : List Chunk → Event (List Result)
processChunks chunks = parallel (map (worker processChunk) chunks)

-- 4 chunks → 4 workers in parallel → one Event with list of results
```

### Example: race for timeout

```agda
withTimeout : ℕ → Event A → Event (Maybe A)
withTimeout ms e = map choose (race [map Just e, map (const Nothing) (delay ms)])
  where
    choose : Either A ⊤ → Maybe A
    choose (Left a) = Just a
    choose (Right _) = Nothing
```

### Additional combinators

For completeness — combinators used in examples:

```agda
-- Delay by N ms, then one discrete event
delay : ℕ → Event ⊤
-- Note: implemented via oneshot variant of interval

-- One event now (see combinators.md)
occur : A → Event A

-- Monadic operations for Event (see combinators.md for full list)
_>>=_ : Event A → (A → Event B) → Event B  -- flatMap/bind
_>>_  : Event A → Event B → Event B        -- sequence
e1 >> e2 = e1 >>= const e2

-- Switch to new Event on each event
switchMap : (A → Event B) → Event A → Event B

-- Discrete events of Signal change (see combinators.md)
changes : Signal A → Event A
```

---

## 4. Worker Pool

### Problem

Creating workers is expensive. Many small tasks → overhead.

### Solution: pool

```agda
-- Pool of N workers
WorkerPool : ℕ → Set

-- Create pool (runtime manages lifecycle)
pool : ℕ → WorkerPool

-- Execute in pool
poolWorker : WorkerPool → WorkerFn A B → A → Event B
```

Runtime:
- Pool created on first use
- Tasks distributed to free workers
- Workers are reused
- Pool destroyed when not used

**Pool lifecycle:**

```javascript
// Runtime tracks active pool tasks
poolState = {
  workers: [...],        // created workers
  queue: [...],          // task queue
  activeTasks: 0,        // how many tasks are running
  lastUsed: timestamp    // when last used
}

// Cleanup on timeout
setInterval(() => {
  if (poolState.activeTasks === 0 &&
      Date.now() - poolState.lastUsed > POOL_IDLE_TIMEOUT) {
    poolState.workers.forEach(w => w.terminate())
    poolState.workers = []
  }
}, POOL_CHECK_INTERVAL)
```

**Constants (configurable):**
- `POOL_IDLE_TIMEOUT` = 30000 ms (30 sec without tasks → cleanup)
- `POOL_CHECK_INTERVAL` = 5000 ms

### Example: batch processing

```agda
myPool : WorkerPool
myPool = pool 4  -- 4 workers

processMany : List Item → Event (List Result)
processMany items = parallel (map (poolWorker myPool processItem) items)
-- Up to 4 tasks run in parallel, others wait in queue
```

### Worker identification

How does runtime distinguish "same worker" from "different"?

```agda
-- Is this the same worker or two different ones?
events m = if m.computing
  then worker factorize m.number
  else never
```

**Rule:** structural comparison by (function, arguments).

- `worker factorize 100` == `worker factorize 100` → same (reuse)
- `worker factorize 100` != `worker factorize 200` → different (cancel old, start new)
- `worker factorize 100` != `worker otherFn 100` → different

**On argument change:**
1. Runtime sees: old `worker f x` disappeared, new `worker f y` appeared
2. Cancels old worker
3. Starts new

### Races: result vs cancellation

**Scenario:** worker finished, but Event already removed from `events`.

```
Tick N:   events = worker f x     → worker started
Tick N+1: events = never          → cancellation sent
          [result arrives]        → ???
```

**Behavior:** result is ignored.

Runtime:
1. On unsubscribe marks worker as "cancelled"
2. If result arrives after cancellation — don't call `emit`
3. Guarantee: after `events = never` no events from this worker

```javascript
unsubscribe: (w) => {
  w._cancelled = true  // mark
  w.postMessage({ type: 'cancel' })
  w.terminate()
}

// In subscribe:
w.onmessage = (e) => {
  if (w._cancelled) return  // ignore
  emit([...])
}
```

---

## 5. Structured Concurrency

### Principle

Child tasks don't outlive parents. If parent is cancelled — children too.

### In Agdelte

Naturally follows from declarative model:

```agda
events m =
  if m.parentTask
  then merge
    (worker taskA m.dataA)      -- child task 1
    (worker taskB m.dataB)      -- child task 2
  else never
```

When `parentTask = false`:
- Both Events disappear from `events`
- Runtime cancels both workers
- Structured concurrency without explicit management

### Scope

```agda
-- Explicit scope for task group
scope : (Scope → Event A) → Event A

record Scope : Set where
  field
    -- Launch task in this scope
    launch : Event B → Event B
    -- Check if scope is cancelled
    cancelled : Signal Bool
```

**Semantics:**
- `scope` creates context for task group
- All `launch`-ed Events are bound to scope
- When outer Event disappears from `events` → scope cancelled → all children cancelled

```agda
-- Example: load several resources, cancel all on page leave
events m = if m.onResourcePage
  then scope λ s →
    merge
      (s.launch (worker loadA m.idA))
      (s.launch (worker loadB m.idB))
      (s.launch (worker loadC m.idC))
  else never
-- Leave page → scope cancelled → all three workers cancelled
```

---

## 6. Channels and Streams

### For complex scenarios: bidirectional communication

```agda
-- Channel: send and receive
record Channel (Send : Set) (Recv : Set) : Set where
  send   : Send → Event ⊤           -- send to worker
  recv   : Event Recv               -- receive from worker
  close  : Event ⊤                  -- close channel

-- Create channel to worker
channel : WorkerScript → Event (Channel Send Recv)
```

**Channel semantics:**

- `send` — sends message to worker, returns Event ⊤ when delivered
- `recv` — message stream from worker (may be many per tick)
- `close` — closes channel

**Channel closing:**
1. When Channel disappears from `events` (declaratively) → automatic close
2. Explicit `close` call → send signal to worker
3. Pending messages in queue — lost (fire-and-forget)
4. Worker receives "channel closed" event and should terminate

```javascript
// Worker-side
onmessage = (e) => {
  if (e.data.type === 'close') {
    cleanup()
    self.close()
    return
  }
  // process regular messages
}
```

### Example: data streaming

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
        (ch.recv)                           -- receive chunks
        (if m.needMore then ch.send More else never)  -- request more
  }
```

---

## 7. SharedArrayBuffer

### For heavy data

Regular transfer: copying (slow for large arrays).

SharedArrayBuffer: shared memory (fast, but requires synchronization).

```agda
-- Shared buffer between main thread and worker
SharedBuffer : ℕ → Set

-- Create shared buffer
allocShared : ℕ → Event SharedBuffer

-- Worker with access to shared memory
workerShared : SharedBuffer → WorkerFn A B → A → Event B
```

### Example: image processing

```agda
processImage : App Msg Model
processImage = record
  { ...
  ; events = λ m → case m.phase of λ where
      -- 1. Allocate shared buffer
      Init → map GotBuffer (allocShared (m.width * m.height * 4))

      -- 2. Run worker with shared buffer
      Ready → map Done (workerShared m.buffer processPixels m.params)

      _ → never
  }
```

Worker reads/writes directly to buffer, without copying.

---

## 8. FFI Implementation

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

  // For functions with progress
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

### How Agda function becomes JS

**Problem:** Agda compiles to JS, but worker requires separate script.

**Solution:** compile-time extraction.

```agda
-- In Agda: mark function as worker-compatible
{-# WORKER factorize #-}
factorize : ℕ → List ℕ
factorize n = ...
```

Compiler:
1. Compiles `factorize` to JS as usual
2. Additionally creates `factorize.worker.js` with same logic
3. `worker factorize` in runtime references this file

```javascript
// Generated code
const worker = (fnName) => (input) => ({
  _type: 'worker',
  _args: [fnName, input],

  subscribe: (emit) => {
    // Load specific worker file
    const w = new Worker(`${fnName}.worker.js`)
    // ...
  }
})
```

**WorkerFn constraints:**
- Function must be pure (no side effects)
- Cannot close over external variables (only arguments)
- All dependencies must be available in worker context

---

## 9. Typing Concurrency

### Linear types for resources (future)

Worker is a resource that must be freed. Linear types guarantee this.

**Note:** Agda doesn't have built-in linear types. Implementation options:

**Option A: Emulation via indexed types**

```agda
-- Resource state
data ResourceState : Set where
  Open Closed : ResourceState

-- Indexed handle
data WorkerHandle (A : Set) : ResourceState → Set where
  mkHandle : WorkerId → WorkerHandle A Open

-- Operations change index
await : WorkerHandle A Open → Event (A × WorkerHandle A Closed)
cancel : WorkerHandle A Open → Event (WorkerHandle A Closed)

-- Cannot use Closed handle
-- await : WorkerHandle A Closed → ... -- doesn't typecheck
```

**Option B: Uniqueness types (like in Clean)**

```agda
-- Unique type: compiler tracks uniqueness
data Unique (A : Set) : Set where
  unique : A → Unique A

-- Operations consume and return
useWorker : Unique (WorkerHandle A) → Event (A × Unique Consumed)
```

**Option C: Monad with linear context**

```agda
-- Linear monad tracks resources
data LIO (resources : List ResourceType) (A : Set) : Set where
  ...

spawn : LIO rs (WorkerHandle A) → LIO (Worker ∷ rs) (WorkerHandle A)
await : WorkerHandle A → LIO (Worker ∷ rs) A → LIO rs A
```

**For MVP:** declarative model (`events`) already provides automatic resource management. Linear types are optimization for explicit low-level control.

### Session types for protocols

For complex workers with communication protocol:

```agda
-- Protocol: send Int, receive String, end
Protocol : Session
Protocol = Send ℕ (Recv String End)

-- Worker follows protocol
typedWorker : (s : Session) → WorkerImpl s → SessionChannel s
```

---

## 10. Comparison with Haskell async

### Expressiveness: declarative vs explicit handles

Everything that can be done with explicit handles in Haskell is expressed declaratively:

| Operation | Haskell async | Agdelte |
|-----------|---------------|---------|
| Start | `h <- async task` | `events = worker task x` |
| Wait | `wait h` | Result comes as Event |
| Cancel | `cancel h` | Remove from `events` |
| Check status | `poll h` | Store in Model |
| Pass to component | `passHandle h` | `mapE ChildMsg (child.events)` |
| Conditional cancel | `when cond (cancel h)` | `if cond then never else worker ...` |

**Conclusion:** declarative model is equivalent in expressiveness.

### Agdelte advantages

| Aspect | Haskell async | Agdelte |
|--------|---------------|---------|
| Resource leaks | Possible (forgot cancel) | Impossible by construction |
| Structured concurrency | Needs explicit `withAsync` | Automatic |
| Bracket/cleanup | Manual | Automatic |
| Progress reporting | Build manually | Built-in |
| Unification with IO | Separate API | Unified Event |

### API correspondence

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
-- Agdelte (declaratively through events)
worker   : WorkerFn A B → A → Event B        -- async + wait
-- cancel = remove Event from events
race     : List (Event A) → Event A          -- race
parallel : List (Event A) → Event (List A)   -- concurrently / mapConcurrently
```

### Example: concurrently

```haskell
-- Haskell: load two resources in parallel
main = do
  (users, posts) <- concurrently
    (fetchUsers)
    (fetchPosts)
  print (users, posts)
```

```agda
-- Agdelte: same thing
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
    -- Combinator for pair (specialization of parallel)
    both : Event A → Event B → Event (A × B)
    both ea eb = map toPair (parallel [map Left ea, map Right eb])
      where
        toPair [Left a, Right b] = (a , b)
```

### Example: race with timeout

```haskell
-- Haskell: request with timeout
fetchWithTimeout :: Int -> IO (Maybe Response)
fetchWithTimeout ms = do
  result <- race
    (threadDelay ms >> return Nothing)
    (Just <$> fetchData)
  return (either id id result)
```

```agda
-- Agdelte: same thing
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

### Example: mapConcurrently

```haskell
-- Haskell: process list in parallel
processAll :: [Item] -> IO [Result]
processAll items = mapConcurrently processItem items
```

```agda
-- Agdelte: same thing
data Msg = Process | GotResults (List Result)

app = record
  { ...
  ; events = λ m →
      if m.processing
      then mapE GotResults (parallel (map (worker processItem) m.items))
      else never
  }
-- 10 items → 10 workers in parallel → one Event with list of results
```

### Example: async/await style (sequential dependent computations)

```haskell
-- Haskell: first one, then another (depends on first result)
main = do
  user <- async fetchUser
  userId <- wait user
  posts <- async (fetchPostsFor userId)
  userPosts <- wait posts
  return userPosts
```

```agda
-- Agdelte: state machine for sequence
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

**Pattern:** phase in Model determines which worker is active. Result of one → next phase → next worker.

### Example: withAsync (bracket-style)

```haskell
-- Haskell: guaranteed cancellation on scope exit
withAsync :: IO a -> (Async a -> IO b) -> IO b
withAsync action inner = bracket (async action) cancel inner
```

```agda
-- Agdelte: automatic through declarativeness!
events m =
  if m.pageActive
  then worker longComputation m.data  -- active while on page
  else never                          -- left page → cancellation

-- No explicit bracket needed — cancellation happens automatically
-- when Event disappears from events
```

### Correspondence summary

| Haskell async | Agdelte | Note |
|---------------|---------|------|
| `async action` | `worker fn x` | Returns Event |
| `wait handle` | Subscription through events | Declarative |
| `cancel handle` | Remove from events | Automatic |
| `race a b` | `race [ea, eb]` | Identical |
| `concurrently a b` | `both ea eb` | Via parallel |
| `mapConcurrently f xs` | `parallel (map (worker f) xs)` | Identical |
| `withAsync` | Declarativeness | Automatic cancellation |
| Sequence | State machine | Phases in Model |

**Key difference:** in Haskell management is explicit (handles), in Agdelte — declarative (events). Result is the same, but without manual resource management.

### STM (Software Transactional Memory)

Haskell async has powerful STM integration for coordinating concurrent processes.

**Many STM patterns are already covered in Agdelte:**

| STM pattern | Agdelte analog | Note |
|-------------|----------------|------|
| `TVar` (watch changes) | `changes` on Signal | Signal is discrete stream, not TVar |
| `retry` (wait for condition) | `if cond then worker ... else never` | Declaratively through events |
| `orElse` (alternative) | `race` | First to finish |
| Atomicity | `update` is atomic | One tick = atomic operation |

**When real STM is needed:**
- Complex coordination between many workers
- Shared mutable state between threads
- Patterns hard to express through Event combinators

**Solution for server-side:**

Server part of Agdelte compiles to Haskell and runs on GHC. STM is available directly:

```agda
-- On server: use STM from GHC
postulate
  TVar    : Set → Set
  newTVar : A → IO (TVar A)
  readTVar : TVar A → STM A
  writeTVar : TVar A → A → STM ⊤
  atomically : STM A → IO A

{-# COMPILE GHC TVar = type Control.Concurrent.STM.TVar #-}
{-# COMPILE GHC atomically = Control.Concurrent.STM.atomically #-}
```

**Client-server architecture:**

```
┌─────────────────────────────────────────────────────────────┐
│                        Agdelte                              │
├─────────────────────────────────────────────────────────────┤
│  Client (JS)          │  Server (GHC)                       │
│  ─────────────        │  ────────────                       │
│  Web Workers          │  Green threads (millions)           │
│  Event model          │  Event model + STM                  │
│  SharedArrayBuffer    │  MVar, TVar, Chan                   │
└─────────────────────────────────────────────────────────────┘
```

Client and server use the same Event model. Server additionally has access to STM for complex coordination.

### Haskell async comparison summary

| | Haskell async | Agdelte |
|--|---------------|---------|
| Expressiveness | Yes | Equivalent |
| Safety | Requires discipline | By construction |
| Structured concurrency | Explicit | By default |
| Unification | Separate API | Unified Event |
| STM | Yes | On server (GHC) |

**Conclusion:** Agdelte concurrency matches Haskell async in expressiveness, exceeds in safety and unification, has STM access on server via GHC.

---

### Other patterns

#### Background computation

```agda
-- Simple case: compute in background
background : (A → B) → A → Event B
background = worker
```

#### Debounced worker

```agda
-- Run worker only after input pause
debouncedWorker : ℕ → WorkerFn A B → Signal A → Event B
debouncedWorker ms fn input =
  switchMap (λ a → delay ms >> worker fn a) (changes input)
```

#### Cached worker

```agda
-- Cache results
cachedWorker : Eq A → WorkerFn A B → A → Event B
cachedWorker eq fn a =
  case lookup a cache of
    Just b  → occur b          -- from cache (one discrete event)
    Nothing → map (cache!) (worker fn a)  -- compute and store
```

#### Retry with backoff

```agda
-- Retry on error with exponential backoff
retryWorker : ℕ → WorkerFn A B → A → Event (Either String B)
retryWorker maxRetries fn a = go 0 100
  where
    go : ℕ → ℕ → Event (Either String B)
    go n delayMs =
      if n >= maxRetries
      then occur (Left "Max retries exceeded")  -- one discrete event
      else race
        [ map Right (worker fn a)
        , delay delayMs >> go (n + 1) (delayMs * 2)
        ]
```

---

## 11. Integration with App

### App remains unchanged

Workers integrate through standard `events` — no App extensions required:

```agda
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg
-- Workers integrate via subs : Model → Event Msg (exported separately)
```

### Automatic management

`subs` is enough for all cases:

```agda
subs : Model → Event Msg
subs m = merge
  (if m.computing then worker heavy m.data else never)
  (if m.fetching then request (get "/api") else never)
```

Runtime determines automatically:
- Which workers to start
- Which to reuse from pool
- Which to cancel

---

## Summary

### Concurrency primitives

| Primitive | Type | Description |
|-----------|------|-------------|
| `worker` | `WorkerFn A B → A → Event B` | Computation in separate thread |
| `workerWithProgress` | `WorkerFn A B → A → Event (Progress B)` | With progress reporting |
| `parallel` | `List (Event A) → Event (List A)` | Parallel, collect all |
| `race` | `List (Event A) → Event A` | Parallel, take first |
| `poolWorker` | `Pool → WorkerFn A B → A → Event B` | Through worker pool |
| `channel` | `WorkerScript → Event (Channel S R)` | Bidirectional communication |

### Connection with base architecture

```
README.md (base)                  concurrency.md (extension)
────────────────                  ──────────────────────────
Signal, Event          ◄────────  (used as is)
App, Html, Runtime     ◄────────  (used as is)

interval, request      ◄── same ─► worker, parallel, race
websocket                pattern:   channel, pool
                       discrete
                       events
```

### Key principle

**Worker = another Event primitive generating discrete events.** Concurrency doesn't change architecture — it adds new primitives following the same model:

- **Discreteness:** result, progress, cancellation — separate discrete events
- **Declarativeness:** `events m = if m.computing then worker f x else never`
- **Automatic management:** subscription/unsubscription through runtime
- **Composition:** `merge`, `mapE`, `filterE` work the same
- **Structured concurrency:** follows from declarative model

### When to use

```
┌─────────────────────────────────────────────────────────┐
│                    UI application                        │
├─────────────────────────────────────────────────────────┤
│  95% of code: forms, lists, navigation, HTTP            │
│  ────────────────────────────────────────               │
│  → DOM events + request + interval                      │
│  → Concurrent/ module NOT needed                        │
├─────────────────────────────────────────────────────────┤
│  5% of code: heavy computations                         │
│  ────────────────────────────                           │
│  → worker, parallel                                     │
│  → import Concurrent/ only here                         │
└─────────────────────────────────────────────────────────┘
```

---

## Roadmap

> Concurrency is an **independent track** (see polynomials.md).
> Can be developed in parallel with Widget Lenses.

**Concurrency Phase A: Basic**
- `worker : WorkerFn A B → A → Event B`
- Basic cancellation
- `parallel`, `race`

**Concurrency Phase B: Extended**
- `workerWithProgress`
- Worker pool
- Channels

**Concurrency Phase C: Advanced**
- SharedArrayBuffer
- Linear types for resources
- Session types
- STM integration (server via GHC)
- Distributed workers
- GPU compute (WebGPU)
