# app

The top layer (SPEC §4): heads (social / crm / b2b-widget), provider adapters &
config, segments, compliance specifics, and `migrations/`. Depends **down** on
everything below.

- `migrations/` — ordered `NNNN_name.sql` files applied by the agdelte migration
  runner (`Agdelte.Server.Migrate`). **⚠️ DEFERRED Postgres scale-out path — the live
  CRM runs on the WAL + in-memory store (ADR 0001), which does NOT execute this SQL.
  The DDL (tenant_id/RLS/uuid) is the documented multi-tenant future, not current.**
