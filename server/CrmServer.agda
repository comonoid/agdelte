{-# OPTIONS --without-K --guardedness #-}

-- CRM headless server (Phase 5 entry). Open the WAL (replay), seed the admin user,
-- then serve the Crm.Api router (+ /psych booking pack + /auth login). State persists
-- across restarts via the WAL.
--
-- Deployment config from env (no recompile):
--   schedule — PSYCH_DAY_START/END, PSYCH_BUFFER, PSYCH_NOTICE_H, PSYCH_CANCEL_H,
--              PSYCH_HORIZON_DAYS, PSYCH_TZ_OFFSET; prices — PSYCH_PRICE_SINGLE/PATH5/PATH10;
--   auth    — CRM_JWT_SECRET (token signing), PSYCH_ADMIN_LOGIN/PASSWORD (bootstrap a
--              bcrypt admin on first boot, granted the admin role globally).
module CrmServer where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.String using (toList) renaming (_++_ to _<>_)
open import Data.List using (null)
open import Data.Bool using (not; if_then_else_)
open import Data.Nat using (ℕ)

postulate setLineBuffering : IO ⊤
{-# FOREIGN GHC import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering)) #-}
{-# COMPILE GHC setLineBuffering = hSetBuffering stdout LineBuffering #-}
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.FFI.Server using (listenHost; getEnvOr; putStrLn; _>>=_; _>>_; pure)
open import Agdelte.FFI.Time using (getCurrentTime)
open import Agdelte.FFI.Crypto using (hashPassword)
open import Agdelte.Storage.WAL using (walOpen; walTxn; WalHandle)
open import Crm.Store using (Base; CrmOp)
open import Crm.Txn using (runTxn)
open import Crm.Commands using (ensureAdmin)
open import Crm.Api using (crmConfig; routeExt)
open import Psych.Api using (tryRoute)
open import Psych.Schedule using (Settings; mkSettings)
open import Psych.Catalog using (Prices; mkPrices)

-- read a ℕ from env (base-10); fall back to `def` when unset or unparseable
envNat : String → ℕ → IO ℕ
envNat key def =
  getEnvOr key (show def) >>= λ s → pure (orDef (readMaybe 10 s))
  where
    orDef : Maybe ℕ → ℕ
    orDef (just n) = n
    orDef nothing  = def

-- seed an admin user (bcrypt) + grant the admin role globally, if the login is set
-- and not already present. Hashing is IO; the create+grant is one walTxn.
seedAdmin : WalHandle Base CrmOp → (login pass : String) → IO ⊤
seedAdmin h login pass =
  if not (null (toList login))
  then ( getCurrentTime >>= λ now →
         hashPassword pass >>= λ ph →
         walTxn h (runTxn (ensureAdmin login ph "*" now)) >>= λ _ →
         putStrLn ("admin ensured: " <> login) )
  else putStrLn "(no admin seed — PSYCH_ADMIN_LOGIN unset)"

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  setLineBuffering >>
  getEnvOr "CRM_HOST" "127.0.0.1" >>= λ host →
  getEnvOr "CRM_TOKEN" "" >>= λ token →
  getEnvOr "CRM_JWT_SECRET" "dev-secret-change-me" >>= λ secret →
  getEnvOr "PSYCH_ADMIN_LOGIN" "" >>= λ adminLogin →
  getEnvOr "PSYCH_ADMIN_PASSWORD" "" >>= λ adminPass →
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
  seedAdmin h adminLogin adminPass >>
  putStrLn "CRM headless on :8137 (WAL: ./crm.wal) + /psych + /auth" >>
  listenHost host 8137
    (λ req → routeExt (tryRoute (mkSettings ds de bf no ca ho tz) (mkPrices p1 p5 p10) h)
                      token secret h req)
