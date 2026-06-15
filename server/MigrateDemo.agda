{-# OPTIONS --without-K --guardedness #-}

-- MigrateDemo: harness for the migration runner (SPEC §14.2c). Applies the
-- *.sql in `migrationsDir` against the configured DB, then exits. Re-running is
-- a no-op for already-applied migrations.
--
-- Production wires `runMigrations` into server startup with the deploy's path
-- and a conninfo from the environment (see SPEC §5.7 / docs/POSTGRES-SPIKE.md).
module MigrateDemo where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

open import Agdelte.FFI.Server using (_>>=_; _>>_)
open import Agdelte.FFI.Postgres using (Pool; newPool; closePool)
open import Agdelte.Server.Migrate using (runMigrations)

conninfo : String
conninfo = "host=127.0.0.1 dbname=agdelte user=agdelte"

migrationsDir : String
migrationsDir = "app/migrations"

main : IO ⊤
main =
  newPool conninfo 2 >>= λ pool →
  runMigrations pool migrationsDir >>
  closePool pool
