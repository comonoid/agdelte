{-# OPTIONS --without-K --guardedness #-}

-- CRM headless server (Phase 5 entry). Open the WAL (replay), then serve the
-- Crm.Api router on a port. State persists across restarts via the WAL — start,
-- write, restart, read: the replayed state matches. WAL path = "crm.wal" in cwd.
module CrmServer where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)

open import Agdelte.FFI.Server using (listen; putStrLn; _>>=_; _>>_)
open import Agdelte.Storage.WAL using (walOpen)
open import Crm.Api using (crmConfig; route)

{-# NON_TERMINATING #-}
main : IO ⊤
main =
  walOpen (crmConfig "crm.wal") >>= λ h →
  putStrLn "CRM headless on :8137 (WAL: ./crm.wal)" >>
  listen 8137 (λ req → route h req)
