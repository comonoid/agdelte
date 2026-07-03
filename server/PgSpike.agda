{-# OPTIONS --without-K --guardedness #-}

-- PgSpike: Task 0 spike (SPEC §14.1). Proves the PostgreSQL connection pool
-- lives in Haskell state (an MVar) and survives across Warp requests.
--
-- The pool is created ONCE before `listen`; every request borrows a connection,
-- inserts a row, and reads back the running total. If the count keeps growing
-- across requests, the pool persisted (and Postgres state with it).
--
-- Build:  npm run build:pg-spike   (needs the nix devShell: postgresql-simple)
-- Run:    npm run run:pg-spike     (after setting up the DB — see docs/SPEC.md §14)
module PgSpike where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

open import Agdelte.FFI.Server
open import Agdelte.Storage.Postgres

------------------------------------------------------------------------
-- Configuration (libpq conninfo). Adjust to your local DB / role.
------------------------------------------------------------------------

-- NB: 127.0.0.1, not "localhost" — hpgsql connects to the first resolved
-- address and does not fall back across the A/AAAA list the way libpq does, so
-- "localhost" can land on an unanswered ::1. Force IPv4 here.
conninfo : String
conninfo = "host=127.0.0.1 dbname=agdelte user=agdelte"

createTable : String
createTable =
  "create table if not exists spike_hits (id bigserial primary key, at timestamptz not null default now())"

------------------------------------------------------------------------
-- Server: pool created once, reused on every request
------------------------------------------------------------------------

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  newPool conninfo 4 >>= λ pool →
  execSql pool createTable >>= λ _ →
  putStrLn "Agdelte Postgres spike on port 3000" >>
  putStrLn "  any request → insert a hit, return running total (proves pool reuse)" >>
  listen 3000 (λ req → handle pool req)
  where
    handle : Pool → HttpRequest → IO HttpResponse
    handle pool _ =
      execSql pool "insert into spike_hits default values" >>= λ _ →
      queryJson pool "select count(*)::int as hits from spike_hits" >>= λ rows →
      pure (mkResponse 200 rows)
