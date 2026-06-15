# app

The top layer (SPEC §4): heads (social / crm / b2b-widget), provider adapters &
config, segments, compliance specifics, and `migrations/`. Depends **down** on
everything below.

- `migrations/` — ordered `NNNN_name.sql` files applied by the agdelte migration
  runner (`Agdelte.Server.Migrate`).
