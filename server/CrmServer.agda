{-# OPTIONS --without-K --guardedness #-}

-- CRM headless server (Phase 5 entry). Open the WAL (replay), then serve the
-- Crm.Api router on a port. State persists across restarts via the WAL — start,
-- write, restart, read: the replayed state matches. WAL path = "crm.wal" in cwd.
module CrmServer where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

open import Agdelte.FFI.Server using (listenHost; getEnvOr; putStrLn; _>>=_; _>>_)
open import Agdelte.Storage.WAL using (walOpen)
open import Crm.Api using (crmConfig; routeExt)
open import Psych.Api using (tryRoute)
open import Psych.Schedule using (defaultSettings)

-- Config from env (secure defaults): CRM_HOST=127.0.0.1 (loopback-only, H1),
-- CRM_TOKEN="" (open on loopback; set it to require `Authorization: Bearer <token>`).
{-# NON_TERMINATING #-}
main : IO ⊤
main =
  getEnvOr "CRM_HOST" "127.0.0.1" >>= λ host →
  getEnvOr "CRM_TOKEN" "" >>= λ token →
  walOpen (crmConfig "crm.wal") >>= λ h →
  putStrLn "CRM headless on :8137 (WAL: ./crm.wal) + /psych booking" >>
  listenHost host 8137 (λ req → routeExt (tryRoute defaultSettings h) token h req)
