# ADR 0001 — Storage engine: WAL + in-memory, typed records (not Postgres)

**Status:** Accepted (2026-06-15). Closes the "WAL/AppStore vs Postgres" open
decision in SPEC §12.

## Context

The CRM ("Ядро услуг") targets **small service providers — one instance per
practitioner** (a solo psychologist with their own clients, a tutor, a master).
That profile is decisive:

- one operator per instance ⇒ multitenancy / RLS is near-pointless;
- tens-to-hundreds of clients ⇒ data fits in RAM (single-digit to ~100 MB);
- **append-mostly, ≤~10% UPDATE/DELETE** (and our soft-delete is itself an UPDATE);
- low write rate, low write concurrency;
- a handful of relations (mostly owned 1:N, a couple of M:N).

The repo already ships a durable WAL + in-memory engine (`Agdelte.Storage.WAL`,
`NatMap`), and `AppStore.agda` demonstrates a near-CRM domain on it (incl. ЮKassa
payments + kopecks). The alternative is PostgreSQL via the pure-Haskell `hpgsql`
driver (Task 0 spike — works).

## Decision

Build the CRM on the **WAL + in-memory engine**, with the domain as **typed Agda
records + `NatMap` (id-keyed tables) + small relation indexes** at aggregate
boundaries; nested ADTs within aggregates. **WAL-only — no runtime snapshots.**
Postgres is retained as the documented **scale-out path** behind the (engine-
agnostic) headless API.

Storage representation principle: **identity / sharing / M:N → id reference;
ownership / no-sharing → nested value.** The CRM data is inherently a graph
(entities with identity + sharing), so id references are unavoidable; the
aggregate boundary keeps them to where sharing is real and nests values elsewhere.

## Rationale — why this wins on this context

1. **No impedance — the program IS the model.** Agda types are the single source
   of truth; the WAL serializes them directly. There is no second relational model
   that the program is an unnatural "view" of (the core objection to Postgres).
   ids are natural domain identity, not a storage artifact.
2. **Transactions nearly free, strongest isolation.** Single-writer + immutable
   state ⇒ **serializable ACID by construction**. A pure function `S → Either Err
   ([Op] × A)` run atomically; rollback is a **no-op** (no undo log, no dead-tuple
   garbage, no VACUUM — cleaner than Postgres MVCC). Multi-step invariant-preserving
   operations (book session, capture payment, consume package) are atomic and
   correct by default — the hardest thing in SQL is the default here.
3. **Types enforce invariants SQL can't** — referential integrity, state machines,
   non-negative balances correct-by-construction via dependent types.
4. **Operational simplicity.** One binary + one WAL file: deploy = scp, backup =
   copy file, recovery = replay. No server, VACUUM, tuning, or RLS. Per-practice
   isolation is **physical** (separate processes) — stronger than RLS, simpler for
   152-ФЗ. Reads in-memory; startup = full WAL replay = O(live data) = ms at scale.

## Consequences / honest limitations

- **Relations are second-class:** explicit index structures at aggregate
  boundaries (a bidirectional `IntMap (IntMap payload)` + reverse index). Bounded
  (few relations, count doesn't grow with data) but it is the main ergonomic cost
  vs a relational DB. Optics make traversal read like nested access but don't
  remove the underlying index maintenance.
- **No ad-hoc queries / joins / reporting** — every query is code. Fine for known
  access patterns; would hurt heavy analytics.
- **Single node, single writer, RAM-bound** — no horizontal scale, no concurrent
  writers; write throughput is fsync-per-commit (group-commit if ever needed).

## When this flips (exit condition)

A **multi-tenant SaaS aggregator** (many practices in one instance) → needs
DB-enforced isolation, scale beyond RAM, ad-hoc reporting ⇒ the **Postgres path**.
The headless API (CRUD by uuid) keeps the engine swappable, so the choice is not
irreversible.

## WAL-only (no snapshots) — sub-decision

At ≤10% churn a snapshot compacts only ~10% and loads no faster than replaying the
WAL; its residual value (a back-compat baseline) is better served by a **one-shot
offline converter** run only when the op format changes. So: use
`walOpen`/`walStep`/`walRead`/`walModify`; never `walSnapshot`/`walStepAutoSnapshot`.
(For a truly clean WAL-only: `walRead` → `readMVar`, drop the op-count bump and the
`loadSnapshot` call — optional cleanup.)

## Notes

- Transparency invariant: the domain stays **pure** (`apply` + queries); only `IO`
  lives at the engine edge (`walStep`/`walOpen`). Any transaction monad is optional
  *pure* sugar, not `IO`.
- Reasoning captured from an extended design discussion (2026-06-15).
