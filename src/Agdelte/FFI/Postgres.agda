{-# OPTIONS --without-K --guardedness #-}

-- PostgreSQL FFI: Haskell-only postulates via MAlonzo (server builds only).
-- Domain-agnostic infrastructure (SPEC §4: the agdelte layer). No domain words.
--
-- Boundary conventions (SPEC §5.6):
--   * everything crossing the FFI is text (Agda String ↔ Haskell Data.Text)
--   * the connection pool is an opaque handle (postulate Pool : Set)
--   * ℕ/Nat ↔ Haskell Integer; sizes are fromInteger'd to Int on the HS side
--   * generic untyped reads come back as JSON text → decode with Agdelte.Json
--
-- Implementation: hs/Agdelte/Postgres.hs (pool lives in an MVar).
module Agdelte.FFI.Postgres where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

{-# FOREIGN GHC import qualified Agdelte.Postgres as PG #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

------------------------------------------------------------------------
-- Connection pool (opaque handle)
------------------------------------------------------------------------

postulate
  Pool : Set
{-# COMPILE GHC Pool = type PG.Pool #-}

-- Create a pool, eagerly opening `size` connections at startup.
-- conninfo is a libpq string, e.g. "host=localhost dbname=agdelte user=agdelte"
-- or a postgresql:// URI.
postulate
  newPool : String → Nat → IO Pool

{-# FOREIGN GHC
  newPoolImpl :: T.Text -> Integer -> IO PG.Pool
  newPoolImpl conninfo size = PG.newPool conninfo (fromInteger size)
  #-}
{-# COMPILE GHC newPool = newPoolImpl #-}

------------------------------------------------------------------------
-- Query layer  (String → IO String at the boundary, SPEC §5.6)
------------------------------------------------------------------------

-- Run a single SELECT (no trailing ';'); result set comes back as a JSON
-- array (text). Empty result → "[]". Decode with Agdelte.Json.
postulate
  queryJson : Pool → String → IO String
{-# COMPILE GHC queryJson = PG.queryJson #-}

-- Run a SELECT whose rows are a single text column; collect the values in
-- order (e.g. applied migration versions). No JSON round-trip.
postulate
  queryCol : Pool → String → IO (List String)
{-# COMPILE GHC queryCol = PG.queryCol #-}

-- Run a non-row statement (INSERT/UPDATE/DELETE/DDL); returns affected rows.
postulate
  execSql : Pool → String → IO Nat
{-# COMPILE GHC execSql = PG.execSql #-}

-- Close all idle connections in the pool.
postulate
  closePool : Pool → IO ⊤
{-# COMPILE GHC closePool = PG.closePool #-}
