{-# OPTIONS --without-K --guardedness #-}

-- CRM headless server (Phase 5 entry). Open the WAL (replay), then serve the
-- Crm.Api router (+ the /psych booking pack) on a port. State persists across
-- restarts via the WAL. WAL path = "crm.wal" in cwd.
--
-- Deployment config from env (the coach's real values, no recompile):
--   schedule — PSYCH_DAY_START/END (minutes from midnight), PSYCH_BUFFER,
--              PSYCH_NOTICE_H, PSYCH_CANCEL_H, PSYCH_HORIZON_DAYS, PSYCH_TZ_OFFSET;
--   prices   — PSYCH_PRICE_SINGLE/PATH5/PATH10 (kopecks).
-- Each falls back to the in-code default when unset/unparseable.
module CrmServer where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.FFI.Server using (listenHost; getEnvOr; putStrLn; _>>=_; _>>_; pure)
open import Agdelte.Storage.WAL using (walOpen)
open import Crm.Api using (crmConfig; routeExt)
open import Psych.Api using (tryRoute)
open import Psych.Schedule using (Settings; mkSettings)
open import Psych.Catalog using (Prices; mkPrices)

-- read a ℕ from env (base-10); fall back to `def` when unset or unparseable
envNat : String → ℕ → IO ℕ
envNat key def =
  getEnvOr key (show def) >>= λ s →
  pure (orDef (readMaybe 10 s))
  where
    orDef : Maybe ℕ → ℕ
    orDef (just n) = n
    orDef nothing  = def

-- Config from env (secure defaults): CRM_HOST=127.0.0.1 (loopback-only, H1),
-- CRM_TOKEN="" (open on loopback; set it to require `Authorization: Bearer <token>`).
{-# NON_TERMINATING #-}
main : IO ⊤
main =
  getEnvOr "CRM_HOST" "127.0.0.1" >>= λ host →
  getEnvOr "CRM_TOKEN" "" >>= λ token →
  envNat "PSYCH_DAY_START"    600 >>= λ ds →
  envNat "PSYCH_DAY_END"     1140 >>= λ de →
  envNat "PSYCH_BUFFER"         0 >>= λ bf →
  envNat "PSYCH_NOTICE_H"      12 >>= λ no →
  envNat "PSYCH_CANCEL_H"      24 >>= λ ca →
  envNat "PSYCH_HORIZON_DAYS"  35 >>= λ ho →
  envNat "PSYCH_TZ_OFFSET"    180 >>= λ tz →
  envNat "PSYCH_PRICE_SINGLE"  1500000 >>= λ p1 →
  envNat "PSYCH_PRICE_PATH5"   6750000 >>= λ p5 →
  envNat "PSYCH_PRICE_PATH10" 12000000 >>= λ p10 →
  walOpen (crmConfig "crm.wal") >>= λ h →
  putStrLn "CRM headless on :8137 (WAL: ./crm.wal) + /psych booking" >>
  listenHost host 8137
    (λ req → routeExt (tryRoute (mkSettings ds de bf no ca ho tz) (mkPrices p1 p5 p10) h) token h req)
