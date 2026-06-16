-- 0001_identity — identity & multitenancy foundation (SPEC §5.2, §5.4, §5.7, §5.8)
--
-- ⚠️ DEFERRED Postgres scale-out path — NOT the live engine. The running CRM uses
-- the WAL + in-memory store (ADR docs/adr/0001-storage-wal-in-memory.md;
-- services-core/Crm/Store.agda). This DDL (bigserial PKs, tenant_id + RLS,
-- gen_random_uuid) is the documented future for multi-tenant SaaS / SQL reporting /
-- when RAM won't hold the data; it is NOT executed by the WAL engine. Tenancy + uuid
-- here intentionally diverge from the single-operator WAL MVP, which omits both
-- (see services-core/Crm/Identity.agda; memory crm-uuid-dropped).
--
-- Tables: tenant, app_user, party, account, profile, channel_handle, segment,
-- party_segment, consent. Operational tables carry tenant_id + RLS (§5.7).
--
-- Column conventions (§5.4): id bigserial PK (internal, → Agda ℕ); uuid (external
-- API id, → Agda String); FKs are bigint; created_at timestamptz; operational
-- tables get deleted_at for soft-delete (§5.7) and tenant_id for RLS.
--
-- NB (design): v6 gives explicit DDL only for party/engagement/consent; the
-- column sets for app_user/account/profile/channel_handle/segment are designed
-- here from the ER diagram (§5.2) + conventions and are REVIEW-WORTHY (§15.4).
--
-- RLS contract: the application connects as a NON-owner role and sets the active
-- tenant per transaction via  SET LOCAL app.current_tenant = '<id>'  (derived from
-- the JWT, §13). Policies use current_setting('app.current_tenant', true) so an
-- unset tenant denies all rows. Migrations run as the table owner, which bypasses
-- RLS, so this file applies cleanly.

-- == Tenancy root =========================================================
-- The operational organization (solo therapist, clinic, transfer hub). Not
-- itself tenant-scoped.
create table tenant (
  id           bigserial primary key,
  uuid         uuid not null default gen_random_uuid() unique,
  display_name text not null,
  created_at   timestamptz not null default now(),
  deleted_at   timestamptz
);

-- == Staff users (the "кейс"-owner; §5.4 user→app_user) ===================
create table app_user (
  id            bigserial primary key,
  uuid          uuid not null default gen_random_uuid() unique,
  tenant_id     bigint not null references tenant(id),
  email         text not null,
  password_hash text not null,                 -- bcrypt (Agdelte.Auth / FFI.Crypto)
  display_name  text not null,
  role          text not null default 'member',
  created_at    timestamptz not null default now(),
  deleted_at    timestamptz,
  unique (tenant_id, email)
);

-- == Party (person|org; §5.4 explicit DDL + tenant_id) ====================
create table party (
  id           bigserial primary key,
  uuid         uuid not null default gen_random_uuid() unique,
  tenant_id    bigint not null references tenant(id),
  type         text not null check (type in ('person','org')),
  display_name text not null,
  tz           text not null default 'Europe/Moscow',   -- IANA; reminder render
  created_at   timestamptz not null default now(),
  deleted_at   timestamptz                              -- soft-delete (§5.7)
);

-- == Account (login credentials for a party; §5.1 party≠account) ==========
create table account (
  id          bigserial primary key,
  uuid        uuid not null default gen_random_uuid() unique,
  tenant_id   bigint not null references tenant(id),
  party_id    bigint not null references party(id),
  kind        text not null default 'password',          -- 'password'|'oauth'|...
  identifier  text not null,                             -- email/phone/subject
  secret      text,                                      -- hash; null for external idp
  created_at  timestamptz not null default now(),
  deleted_at  timestamptz,
  unique (tenant_id, kind, identifier)
);

-- == Profile (showcase; §5.7 public cross-tenant scope) ===================
create table profile (
  id          bigserial primary key,
  uuid        uuid not null default gen_random_uuid() unique,
  tenant_id   bigint not null references tenant(id),
  party_id    bigint not null references party(id),
  kind        text not null default 'internal'           -- 'public'|'internal'
              check (kind in ('public','internal')),
  is_public   boolean not null default false,            -- read by the public role
  title       text,
  attrs       jsonb not null default '{}',
  created_at  timestamptz not null default now(),
  deleted_at  timestamptz
);

-- == Channel handle (omni resolve channel→party; §8) ======================
create table channel_handle (
  id         bigserial primary key,
  uuid       uuid not null default gen_random_uuid() unique,
  tenant_id  bigint not null references tenant(id),
  party_id   bigint not null references party(id),
  channel    text not null,                              -- 'wa'|'tg'|'email'|...
  address    text not null,
  verified   boolean not null default false,
  created_at timestamptz not null default now()
);
-- §5.4 calls for unique(channel, address); scoped per tenant here so the same
-- phone can belong to a client of two different tenants (REVIEW: confirm scope).
create unique index channel_handle_addr_uq on channel_handle (tenant_id, channel, address);

-- == Segment (taxonomy; §5.7 tenant_id null = global) =====================
create table segment (
  id         bigserial primary key,
  uuid       uuid not null default gen_random_uuid() unique,
  tenant_id  bigint references tenant(id),                -- null ⇒ global dictionary
  code       text not null,
  title      text not null,
  kind       text not null default 'generic',
  created_at timestamptz not null default now()
);

-- == Party↔Segment (join; §5.4 composite PK, no id/uuid) ==================
create table party_segment (
  tenant_id  bigint not null references tenant(id),
  party_id   bigint not null references party(id),
  segment_id bigint not null references segment(id),
  primary key (party_id, segment_id)
);

-- == Consent (152-ФЗ; §5.8 explicit DDL + tenant_id) ======================
create table consent (
  id         bigserial primary key,
  tenant_id  bigint not null references tenant(id),
  party_id   bigint not null references party(id),
  kind       text not null,                  -- 'pd_processing'|'channel_wa'|...
  granted    boolean not null,
  granted_at timestamptz not null default now(),
  source     text
);

-- == Indexes on FKs (§5.4 "все FK") =======================================
create index app_user_tenant_idx       on app_user (tenant_id);
create index party_tenant_idx          on party (tenant_id);
create index account_tenant_idx        on account (tenant_id);
create index account_party_idx         on account (party_id);
create index profile_tenant_idx        on profile (tenant_id);
create index profile_party_idx         on profile (party_id);
create index profile_public_idx        on profile (is_public) where is_public;
create index channel_handle_tenant_idx on channel_handle (tenant_id);
create index channel_handle_party_idx  on channel_handle (party_id);
create index segment_tenant_idx        on segment (tenant_id);
create index party_segment_segment_idx on party_segment (segment_id);
create index consent_tenant_idx        on consent (tenant_id);
create index consent_party_idx         on consent (party_id);

-- == Row-level security (§5.7) ============================================
-- Per-tenant isolation. segment is a shared dictionary: global rows (tenant_id
-- null) are visible to everyone, tenant-owned rows only to that tenant.
alter table app_user       enable row level security;
alter table party          enable row level security;
alter table account        enable row level security;
alter table profile        enable row level security;
alter table channel_handle enable row level security;
alter table party_segment  enable row level security;
alter table consent        enable row level security;
alter table segment        enable row level security;

create policy app_user_tenant_isolation on app_user
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy party_tenant_isolation on party
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy account_tenant_isolation on account
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy profile_tenant_isolation on profile
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy channel_handle_tenant_isolation on channel_handle
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy party_segment_tenant_isolation on party_segment
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy consent_tenant_isolation on consent
  using (tenant_id = current_setting('app.current_tenant', true)::bigint);
create policy segment_tenant_or_global on segment
  using (tenant_id is null
         or tenant_id = current_setting('app.current_tenant', true)::bigint)
