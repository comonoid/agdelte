{-# OPTIONS --without-K --guardedness #-}

-- Migration runner (SPEC §4: agdelte layer, §14.2). Domain-agnostic.
--
-- Applies *.sql files from a directory, in ascending filename order, each in a
-- single transaction together with its bookkeeping row, skipping any already
-- recorded in schema_migrations. At-least-once-safe to re-run: applied
-- migrations are not reapplied (the version = the filename).
--
-- Convention: name migrations NNNN_description.sql (zero-padded ⇒ lexical order
-- = apply order). Uses Storage.Postgres (execSql/queryCol) + FFI/FileSystem.
module Agdelte.Server.Migrate where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.String using (_++_; toList; fromList)
open import Data.List using (List; []; _∷_; reverse; dropWhileᵇ)
open import Data.Char using (isSpace)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)

open import Agdelte.FFI.Shared   using (startsWith)
open import Agdelte.Storage.Postgres using (Pool; execSql; queryCol)
open import Agdelte.FFI.FileSystem using (listDirectory; readFileText)
open import Agdelte.FFI.Server using (_>>=_; _>>_; pure; putStrLn)

------------------------------------------------------------------------
-- String helpers
------------------------------------------------------------------------

revStr : String → String
revStr s = fromList (reverse (toList s))

endsWith : String → String → Bool
endsWith suffix s = startsWith (revStr suffix) (revStr s)

member : String → List String → Bool
member _ []       = false
member x (y ∷ ys) = if primStringEquality x y then true else member x ys

-- Trim trailing whitespace.
rstripWS : String → String
rstripWS s = fromList (reverse (dropWhileᵇ isSpace (reverse (toList s))))

-- Guarantee exactly one trailing ';' (no empty statement). hpgsql 0.2.0.0
-- mis-parses an EmptyQueryResponse, so we must never emit a bare ';' between
-- statements — appending a second ';' to an already-terminated body would.
ensureSemicolon : String → String
ensureSemicolon s = let t = rstripWS s in if endsWith ";" t then t else (t ++ ";")

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

migrationsTableDDL : String
migrationsTableDDL =
  "create table if not exists schema_migrations (version text primary key, applied_at timestamptz not null default now())"

-- Apply one migration atomically: its body + the bookkeeping insert run in a
-- single transaction on one connection. The \n;\n guarantees a statement break
-- whether or not the file ends in ';' (a resulting empty statement is harmless).
applyOne : Pool → String → String → IO ⊤
applyOne pool dir name =
  readFileText (dir ++ "/" ++ name) >>= λ body →
  execSql pool ( "begin;\n" ++ ensureSemicolon body
              ++ "\ninsert into schema_migrations(version) values ('" ++ name ++ "');\ncommit"
               ) >>= λ _ →
  putStrLn ("  applied " ++ name)

-- Sequentially apply each pending .sql entry.
applyPending : Pool → String → List String → List String → IO ⊤
applyPending _    _   _       []       = pure tt
applyPending pool dir applied (n ∷ ns) =
  (if endsWith ".sql" n ∧ not (member n applied)
     then applyOne pool dir n
     else pure tt) >>
  applyPending pool dir applied ns

-- Ensure the ledger table, read applied versions, apply the rest in order.
runMigrations : Pool → String → IO ⊤
runMigrations pool dir =
  execSql pool migrationsTableDDL >>= λ _ →
  queryCol pool "select version from schema_migrations" >>= λ applied →
  listDirectory dir >>= λ entries →
  putStrLn ("migrate: scanning " ++ dir) >>
  applyPending pool dir applied entries >>
  putStrLn "migrate: done"
