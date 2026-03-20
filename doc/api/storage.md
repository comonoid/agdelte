# Agdelte.Storage

Write-ahead log (WAL) with periodic snapshots for durable in-memory state.
All reads hit memory; all writes append to a log file first, then update the
in-memory state. Snapshots allow log truncation and fast recovery.

## Design Principles

1. **Durable** -- every mutation is on disk before it is acknowledged
2. **Fast** -- reads never touch the filesystem
3. **Recoverable** -- `walOpen` replays the log on top of the last snapshot
4. **Thread-safe** -- state is protected by an `MVar`

## Quick Start

```agda
open import Agdelte.Storage.WAL
open import Agdelte.Storage.AppStore

main : IO Unit
main = do
  h <- walOpen (appWalConfig "data/wal.log" "data/snap.json")
  walStep h (AddUser (mkUserRecord "u1" "a@b.com" hash))
  s <- walRead h
  ...
```

## WAL

### WalConfig

Configuration record parameterised over state `S` and operation `Op`.

```agda
record WalConfig (S Op : Set) : Set where
  constructor mkWalConfig
  field
    walLogPath         : String            -- path to WAL log file
    walSnapshotPath    : String            -- path to snapshot file
    walApply           : Op -> S -> S      -- pure state transition
    walSerializeOp     : Op -> String      -- operation -> one line
    walDeserializeOp   : String -> Maybe Op
    walSerializeState  : S -> String
    walDeserializeState : String -> S
    walEmptyState      : S                 -- initial empty state
```

### WalHandle

Mutable, thread-safe handle returned by `walOpen`.

```agda
record WalHandle (S Op : Set) : Set where
  constructor mkWalHandle
  field
    walConfig  : WalConfig S Op
    walState   : MVar S              -- mutex-protected state
    walOpCount : IORef N             -- operations since last snapshot
```

### Core Operations

```agda
-- | Open (or recover) a WAL. Loads snapshot, replays log.
walOpen : WalConfig S Op -> IO (WalHandle S Op)

-- | Apply an operation: append to log, update in-memory state.
-- Returns the new state. Atomic (MVar); restores state on exception.
walStep : WalHandle S Op -> Op -> IO S

-- | Read current state without mutation.
walRead : WalHandle S Op -> IO S

-- | Write a full snapshot, then truncate the log.
-- Snapshot is written to a temp file and renamed (POSIX atomic).
walSnapshot : WalHandle S Op -> IO Unit

-- | walStep + automatic snapshot when op count exceeds threshold.
walStepAutoSnapshot : WalHandle S Op -> N -> Op -> IO S
-- walStepAutoSnapshot handle threshold operation
```

## Recovery

`walOpen` performs the following sequence:

1. If a snapshot file exists, deserialise it into state `s0`;
   otherwise start from `walEmptyState`.
2. If a log file exists, read it and split into lines.
3. Replay each line: deserialise to `Maybe Op`, apply valid ops
   to `s0` via `walApply` (invalid lines are skipped).
4. Store the recovered state in an `MVar` and return the handle.

This means the system tolerates incomplete writes at the end of the log --
a partially written line will fail `walDeserializeOp` and be skipped.

## AppStore

Domain-specific state and operations for a video course platform,
built on top of `WAL`.

### Domain Records

```agda
record UserRecord : Set where
  constructor mkUserRecord
  field urId : String ; urEmail : String ; urPassHash : String

record CourseRecord : Set where
  constructor mkCourseRecord
  field crId : String ; crTitle : String ; crDescription : String ; crPrice : String

record PurchaseRecord : Set where
  constructor mkPurchaseRecord
  field prUserId : String ; prCourseId : String

record ProgressRecord : Set where
  constructor mkProgressRecord
  field pgUserId : String ; pgLessonId : String ; pgPosition : String ; pgCompleted : Bool
```

### AppState and AppOp

```agda
record AppState : Set where
  constructor mkAppState
  field
    asUsers     : List UserRecord
    asCourses   : List CourseRecord
    asPurchases : List PurchaseRecord
    asProgress  : List ProgressRecord

emptyAppState : AppState

data AppOp : Set where
  AddUser     : UserRecord -> AppOp
  AddCourse   : CourseRecord -> AppOp
  AddPurchase : PurchaseRecord -> AppOp
  SetProgress : ProgressRecord -> AppOp
```

### applyOp

```agda
applyOp : AppOp -> AppState -> AppState
```

`AddUser`, `AddCourse`, and `AddPurchase` prepend to the corresponding list.
`SetProgress` upserts by `(userId, lessonId)` -- replaces an existing entry
or appends a new one.

### Query Functions

```agda
findUserByEmail : String -> AppState -> Maybe UserRecord
findUserById    : String -> AppState -> Maybe UserRecord
userHasCourse   : String -> String -> AppState -> Bool
-- userHasCourse userId courseId state

getProgress     : String -> String -> AppState -> Maybe ProgressRecord
-- getProgress userId lessonId state
```

### WAL Config Helper

```agda
-- | Pre-wired WalConfig for AppState / AppOp.
appWalConfig : String -> String -> WalConfig AppState AppOp
-- appWalConfig logPath snapshotPath
```

## Usage Example

```agda
open import Agdelte.Storage.WAL
open import Agdelte.Storage.AppStore

startApp : IO (WalHandle AppState AppOp)
startApp = walOpen (appWalConfig "data/app.log" "data/app.snap")

addUser : WalHandle AppState AppOp -> IO AppState
addUser h = walStepAutoSnapshot h 100
  (AddUser (mkUserRecord "u1" "alice@example.com" hashedPw))

checkAccess : WalHandle AppState AppOp -> String -> String -> IO Bool
checkAccess h uid cid = do
  s <- walRead h
  pure (userHasCourse uid cid s)
```

## Module Structure

```
Agdelte/Storage/
  WAL.agda        -- WalConfig, WalHandle, walOpen, walStep, walRead, walSnapshot
  AppStore.agda   -- AppState, AppOp, applyOp, queries, appWalConfig
```
