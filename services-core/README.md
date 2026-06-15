# services-core

Neutral service machinery reused across verticals (SPEC §4). Depends **down only**
on the `agdelte` framework — never on `packs/` or `app/`.

**Will hold:** `party` / `subject` / `engagement` / `resource` / `offering`,
money, outbox / event bus, headless API, ACL / authz, payment-gateway
abstraction, omni layer.

**Neutrality guard (CI):** must not name any vertical — no
`psych | vet | transfer | медцентр`. See `scripts/check-neutrality.sh`.

**Extractability:** self-contained directory with its own `.agda-lib`. To lift
into a separate repo, `git mv services-core …`, add `agdelte` to its
`depend:`, and register the agdelte library.
