# Task 0 — Postgres spike (walking skeleton)

Proves the main technical unknown from SPEC §12: **a PostgreSQL connection pool,
held in Haskell state, survives across Warp requests through the Agda FFI.**

Verified live: hitting the endpoint three times returns `[{"hits":1}]`,
`[{"hits":2}]`, `[{"hits":3}]` — the pool is created once at startup and reused.

## Pieces

| File | Role |
|---|---|
| `src/Agdelte/FFI/Postgres.agda` | Agda FFI: `Pool`, `newPool`, `queryJson`, `execSql`, `closePool` (postulates; String/Nat boundary) |
| `hs/Agdelte/Postgres.hs` | Haskell impl: MVar pool of `HPgConnection`, backed by **hpgsql** |
| `server/PgSpike.agda` | Entry: pool created before `listen`, each request INSERTs + reads the count |
| `agdelte.cabal`, `cabal.project`, `cabal.project.freeze` | Reproducible server build |

## Scope boundary

Agdelte does **not** provision or manage Postgres. Its only contract is a
**conninfo string** — point it at any running Postgres (system package, a Docker
sidecar, a managed service; doesn't matter) and it connects. DB lifecycle,
backups, HA are the operator's concern. Consequence: conninfo is **config**
(env var / flag), not hardcoded. In this spike it's a literal in `PgSpike.agda`
for brevity; the real server reads it from the environment.

## Driver: hpgsql (pure Haskell, no libpq)

[hpgsql](https://hackage.haskell.org/package/hpgsql) speaks the PostgreSQL wire
protocol directly — **no `libpq`, no C system library**. On Debian there is no
`libpq-dev` to install; the dependency set is pinned by `cabal.project.freeze`
(155 packages, `index-state 2026-06-15`, hpgsql 0.2.0.0).

Gotchas baked into the code/build:
- **`host=127.0.0.1`, not `localhost`** — hpgsql connects to the first resolved
  address and does not iterate the A/AAAA list the way libpq does, so `localhost`
  can land on an unanswered `::1`.
- hpgsql has **no TLS yet** — fine for a same-host DB; cross-host prod needs a
  local proxy (pgbouncer/stunnel) or a future hpgsql release.

## Build (dev, NixOS)

Uses system **GHC 9.10.3 + cabal 3.16** (the ghc-9.10 branch; *not* the flake's
`ghcWithPackages`, which pins an older GHC). hpgsql requires GHC 9.6.7/9.8.4/9.10.3.

```sh
# zlib isn't on NixOS's default linker path (needed by warp); point cabal at it:
export LIBRARY_PATH=$(dirname $(find /nix/store -path '*zlib-*/lib/libz.so' | head -1))

npm run build:pg-spike      # = agda --ghc-dont-call-ghc  +  cabal build pg-spike
```

`build:pg-spike` runs two steps:
1. `gen:pg-spike` — `agda --compile --ghc-dont-call-ghc` emits MAlonzo Haskell to
   `_build/MAlonzo/Code/**` (entry module `MAlonzo.Code.PgSpike`).
2. `cabal build pg-spike` — compiles that closure (41 modules) + `hs/**` + hpgsql.

The exe is `-threaded` (warp + hpgsql's timer manager require it) and
`default-language: GHC2021` (the hand-written `hs/**` uses BangPatterns /
ScopedTypeVariables, which `agda --compile` assumes by default).

## Run + verify (needs a local Postgres)

```sh
# role `agdelte`, db `agdelte`, listening on 127.0.0.1:5432, trust auth.
# e.g. nix-shell -p postgresql, initdb -U agdelte, pg_ctl start, createdb -U agdelte agdelte

export LD_LIBRARY_PATH=$LIBRARY_PATH       # zlib at runtime too
npm run run:pg-spike                        # serves on :3000

curl localhost:3000   # → [{"hits":1}] , then [{"hits":2}] , …  (count climbs ⇒ pool persists)
```

## Production build (deferred until deploy)

Mirror `/home/n/sergey-site`: Docker `debian:trixie` + ghcup (GHC 9.10.3, cabal
3.16) + `cabal build`, versions fixed by `cabal.project.freeze`. On Debian the
`LIBRARY_PATH` zlib hack is **not** needed (zlib is on the standard path), and
hpgsql means **no `libpq-dev`** in the image. Keep the build image around between
runs for fast rebuilds (Docker layer cache). Not written yet — `cabal.project.freeze`
is the artifact it will consume.
