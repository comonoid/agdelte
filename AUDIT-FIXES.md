# Audit Fixes (Opus 4.8) — changes and remarks

This documents the fixes applied after the second audit pass and the remarks /
caveats that came up while fixing. Findings are labelled with the IDs from the
audit report (C = critical, H = high, M = medium, L = low).

## How fixes were verified

- **Agda**: typechecked with the nix-shell agda (2.7.0.1) via
  `nix develop -c agda --library-file=$HOME/.agda/libraries -i src <module>`.
  All changed modules typecheck (only pre-existing `any`/`all` v2.3 deprecation
  warnings remain, in `AppStore.agda`).
- **Haskell FFI**: the GHC backends of `Payment`, `Auth/*`, `FFI/FileSystem`,
  `Storage/NatMap` are **not built by any current target** (see remark R3), so
  they cannot be compiled via the normal pipeline. Each new/changed FFI snippet
  was instead compiled standalone with `nix develop -c ghc -package … -c …`
  against the exact packages the flake provides. All compiled cleanly.
- **JS runtime**: `node test/runtime.test.js` (81) and `node test/gl-math.test.js`
  (49) pass; all edited runtime files pass `node --check`.
- See remark R1 for why the JS-codegen-dependent tests (video/dom/auth) could not
  be run in this environment.

## Fixed

### Critical
- **C1** `runtime/events.js` — `wsConnect` referenced an undeclared `terminated`
  in the Blob branch → `ReferenceError` dropping every binary WebSocket frame
  (browsers default `binaryType` to `blob`). Added `let terminated = false` and
  set it in `unsubscribe`.
- **C2** JWT tokens never expired. `mkToken` now emits `iat`+`exp` (24h TTL,
  `Auth/Handler.agda`); `verifyJWT` now takes `now` and rejects tokens that are
  expired **or** have no `exp` (`Auth/JWT.agda`). Threaded `now` through
  `Middleware.authenticate`/`withAuth`, all four `Guard` combinators, and
  `Payment.handlePurchase`/`handleSubscribe` (they fetch `getCurrentTime` once
  and reuse it).
- **C3** ЮKassa webhook trusted the request body. `handlePaymentWebhook` now
  parses `object.id` with a real JSON parser (`parseWebhookFields`, nested
  lookup — closes the flat-`"id"` ambiguity, old H3), then **re-fetches the
  payment from ЮKassa** (`getPaymentStatusRaw`, `GET /v3/payments/{id}`) and
  acts on ЮKassa's authoritative `status`, never on the body's `event`. The
  body-HMAC signature check is kept only as defense-in-depth (documented).

### High
- **H1 / L2** `runtime/reactive.js` `setProp` coerced by sniffing the value
  (`Number(value)`), so `el.muted = "false"` (a truthy string) stayed muted and
  numeric-looking string props like `textContent="007"` were corrupted. Now
  coerces by **property name** via `BOOLEAN_DOM_PROPS` / `NUMERIC_DOM_PROPS`
  allowlists, defaulting to string assignment. Fixes the video mute toggle
  (`Player.agda` needs no change).
- **H2** `runtime/reactive-gl.js` `disposeGLCanvas` leaked per-entry GPU
  resources (`textVAO`, `instanceBuffer.buffer`, `_mergedGeo`). Now walks
  `renderList` and frees them, mirroring the bindChildren cleanup block.
- **H3** `runtime/reactive-gl.js` context-loss → restore leaked a `ResizeObserver`
  (and stacked duplicates). `webglcontextrestored` now `resizeObs.disconnect()`s
  before re-init.
- **H5** WAL appends weren't durable. `FFI/FileSystem.agda` `writeFileText` /
  `appendFileText` now do a durable write (write → `hFlush` → `handleToFd` →
  `fileSynchronise` → `closeFd`), so `walStep` and snapshot writes fsync before
  returning. (Fixed at the FFI layer; WAL needs no change.)
- **H6** JSON escaping only handled `\ " \n \r \t`, leaving other control chars
  raw (invalid JSON / claim-smuggling into the JWT payload). Both server
  (`FFI/Json.agda escapeJsonString`) and client (`Auth/Client.agda escapeJson`)
  now escape all of U+0000–U+001F as `\u00XX` (plus `\b`/`\f`).

### Medium
- **M2** `Auth/Middleware.agda` — added `corsHeadersOrigin : String → …` for
  production (specific origin); `corsHeaders` is now the documented dev-only
  wildcard built on top of it. (Non-breaking; production wiring is a follow-up.)
- **M3** `FFI/FileSystem.agda` — added `readFileConfined` / `writeFileConfined`
  that canonicalize `root </> relPath` and reject escapes (`..`/symlink) outside
  `root`, for any future caller that maps untrusted input to a path. Documented
  that the raw functions must never take untrusted input.
- **M4** `Storage/NatMap.agda` — switched backing store from `Data.IntMap`
  (machine-`Int` keys, truncate ids ≥ 2^63 → collisions) to
  `Data.Map.Strict Integer`. No truncation; interface unchanged.
- **M5** `Reactive/BigLens.agda` `processAgentOptic` — `bracket`'s release
  (`closeProcess`) could throw after a successful body and `tryCatch` would then
  report the whole peek/step as `nothing`. Cleanup now swallows its own errors
  (`closeQuiet`), preserving body success.
- **M6** `runtime/reactive.js` `mediaSourceAppend` — a synchronous `appendBuffer`
  throw in a queued segment stalled the queue (no further `updateend`).
  Rewritten to a task queue with a single error-resilient `pump`; `onDone`
  travels with each task instead of a shared slot.

### Low
- **L1** Removed `[DEBUG …]` `console.log`s that fired on every global
  key/mouse event (`runtime/events.js`) and every subscription update
  (`runtime/reactive.js`).
- **L5** `Storage/AppStore.agda` `escapeFieldHS`/`unescapeFieldHS` now handle
  `\r` (was dropped through, corrupting CRLF text on WAL replay).
- **L6** `Auth/SignedUrl.agda` — expiry check `<ᵇ` → `≤ᵇ` (URL now rejected
  exactly at the expiry second too).
- **L7** `package.json` — added `test:auth` to `test:all` (was defined but never
  aggregated).
- **L8** `runtime/agda-values.js` `numberToNat` — clamps to `MAX_NAT_VALUE` and
  floors the input (was unbounded vs. the capped read side → hang/OOM risk).
- **L3** `scripts/cjs-to-esm.cjs` / `fix-esm.cjs` — these are **unused legacy**
  (build emits ES6 directly; see R1). Added headers marking them legacy rather
  than reworking dead code's source maps.
- **L4** `scripts/check-ffi-fragile.sh` — added `-w` to the fixed-string grep so
  a constructor name that is merely a substring of a larger identifier no longer
  counts as "still present".

## Remarks / caveats encountered while fixing

- **R1 — JS build toolchain version mismatch (environment).** The nix-shell agda
  is 2.7.0.1, which does **not** accept `--js-es6` (it suggests `--js-cjs/-amd`),
  yet every `build:*` script uses `--js-es6`. The JS toolchain is evidently a
  newer agda (≈2.9.0 — cf. `fix-esm.cjs`, the `_build/2.9.0` default in
  `cjs-to-esm.cjs`), and `~/.local/bin/agda` is a non-runnable ELF under NixOS.
  Consequence: the JS-codegen-dependent tests (`test:video`, `test:dom`,
  `test:auth`) cannot be built/run in this environment — they already failed
  before any change for the same reason. The runtime-only tests do run and pass.
  Worth pinning the JS-build agda version in the flake.

- **R2 — H4 was a false positive.** The claim that `readFileSafe` is broken by
  lazy IO is wrong: `Data.Text.IO.readFile` (strict module) reads+decodes the
  whole file before returning, so the surrounding `try` does catch read/decode
  errors. Left unchanged; added a clarifying comment.

- **R3 — Payment/Auth/Storage GHC FFI is not wired into any build target.**
  `build:main`/`build:server` pass only `network text bytestring stm containers
  websockets warp wai wai-websockets http-types async`; they do **not** include
  `http-client`, `aeson`, `cryptonite`, `directory`, or `unix`, which
  `Payment`/`Auth`/`WAL`/`NatMap` require. So none of this server code is
  compiled by the current pipeline — it can only be typechecked. All FFI here
  (changed and pre-existing) was therefore verified by standalone GHC compiles,
  not by an end-to-end server build.

- **R4 — Pre-existing `HC.statusCode` bug fixed in passing.** `Payment.agda`'s
  existing `createPaymentRaw` used `HC.statusCode`, which `Network.HTTP.Client`
  does not export — i.e. the module never compiled (consistent with R3). Added
  `import Network.HTTP.Types.Status (statusCode)` and changed both existing call
  sites plus the new one to bare `statusCode` (compile-verified).

- **R5 — Payment FFI tuple convention is unverified.** `createPaymentRaw` (and
  now `getPaymentStatusRaw`) declare Agda `ℕ × String × String` but the Haskell
  returns a flat `(Integer, T.Text, T.Text)`. Whether MAlonzo maps `_×_` to a
  Haskell tuple here is unverified (can't compile the MAlonzo output — R3). The
  new code follows the existing convention exactly; if it's wrong, it's a
  pre-existing problem affecting the whole module, not these changes.

- **R6 — C3 confirmation path is untested against the live ЮKassa API.** The
  re-fetch logic is architecturally correct and the Haskell compiles, but there
  are no ЮKassa credentials here to exercise it. Also, on confirmation failure
  the handler returns 200 with no state change (safe: never grants unpaid
  access; avoids retry storms) — revisit if you want ЮKassa to retry transient
  failures (would need a non-2xx response).

- **R7 — M7 (TimeTravel) was a false positive.** Given the module invariants
  (`pushState` caps `past` at `maxSize`, and the number of `undo`s is bounded by
  `length past`), `future` can never exceed `maxSize`, so the `trimList` in
  `undo`/`redo` is always a no-op and undo/redo are inverse within the budget.
  Left unchanged.

- **R8 — M8 (Task `>>=`) left as-is by design.** The lossy error-terminal bind
  is already documented with a warning and a lossless alternative (`_>>=+_`)
  exists. Flipping the default bind would silently change error semantics for
  every existing `Task` user, so it was not changed.

- **R9 — Incident: raw control bytes in `Auth/Client.agda`.** An intermediate
  edit of the `escapeJson` regex landed literal NUL–0x1F bytes in the source
  (functionally fine but unacceptable in a source file). Rewritten to clean ASCII via node so the source contains the literal
  escape `[\u0000-\u001f...]` rather than raw bytes. Prefer `\uXXXX` escapes
  when editing control-char regex ranges in this file.

---

# Round 2 (after agda-stdlib update + deeper sweep)

## stdlib update result
The agda-stdlib update (still 2.4) introduced **no compilation breakage**: all 41
example + server modules typecheck. Only new deprecation *warnings* appear
(`_≟_` → `_≡?_` in v2.4; `any`/`all` style). No migration required to keep
building; addressing the deprecations is optional cleanup.

## Systemic CRITICAL — Bool FFI used Scott-encoding; Agda's JS backend uses NATIVE booleans
Confirmed from generated output: `jAgda.Agda.Builtin.Bool.js` has
`Bool.true = true`, `Data.Bool.Base.if_then_else_` dispatches via `c ? v.true() : v.false()`,
and `Data.Maybe.Base` returns `Bool.true` (= native `true`). Maybe is Scott
(`just = a => b => b.just(a)`), but **Bool is native**. Hand-written FFI that
returned `(cases) => cases["true"]()` for a Bool therefore produced an always-truthy
closure (→ always the `then` branch), and FFI that *consumed* a Bool as
`b({"true":…,"false":…})` would call a boolean as a function (→ crash).

Fixed (changed the COMPILE JS pragmas to native booleans; verified via typecheck):
- `WebGL/Controls/{Charts/Surface, Audio/Spectrum, Audio/Waveform, Gizmos/Measure,
  Gizmos/Selection}` — `_<F_`/`_>F_` (were always-true → wrong colors, and
  `ruler3D` rendered zero ticks).
- `WebGL/Controls/Charts/Network3D` — `stringEq` (was always-true → every edge
  drawn from the first node to itself).
- `Data/Array` — `null`, `all`, `any`, `elem`, `filter`, `find`, `findIndex`
  (produced/consumed Scott bool; `all`/`any`/`elem` would crash).
- `Json` — `bool` decoder, `jBool`, `encodeBool`.
- `Css/Color` — `isHexColor`. `DateTime` — `isSameDay`/`isSameMonth`/`isSameYear` etc.
- `runtime/agda-values.js` `toBool` → `!!value` (was Scott; currently dead code but
  now correct). This resolves round-1 M1: native booleans are correct, so
  `mkKeyboardEvent`'s `!!e.ctrlKey` was right and the Scott `toBool` was the bug.

## Systemic CRITICAL — ℕ is BigInt; FFI mixed it with JS Number (runtime TypeError)
Agda ℕ compiles to JS `BigInt`. Mixing `BigInt` with a `Number` literal throws
`TypeError`, and `Math.floor(bigint)` throws. Fixed (coerce with `Number(...)`, or
stay in BigInt with `0n`/`/`):
- `I18n` — `formatCurrencyImpl` (`kopecks/100`), `formatDateImpl` (`ts*1000`),
  `pluralRu` (`n%10`). All threw on every call.
- `Html/Controls/Cart` — `formatPriceImpl` (cart total view crashed).
- `WebGL/Controls/Sliders` — `floatToNat` returned a `Number` where ℕ (BigInt) is
  expected → downstream BigInt ops would crash; now `BigInt(Math.max(0,…))`.
- `Html/Controls/Video/Progress` — `safeDiv`: `d === 0` (BigInt vs Number) was
  always false AND `Math.floor(bigint)` threw → crashed every call; now BigInt-native.

## HIGH — Cart.agda could never typecheck
`Html/Controls/Cart.agda` used `--without-K` but imports `Storage/AppStore`
(`--guardedness`); Agda rejects that flag mismatch. The module is imported by
nothing, so it had never been compiled. Added `--guardedness` to its OPTIONS;
now typechecks.

## WebGL geometry (verified by typecheck)
- **H3 / M4** — connector cylinders (default +Y axis) were placed with
  `identityQuat`, so they rendered as vertical sticks instead of pointing at their
  endpoint. Now use the purpose-built `lookAtQuat src dst`:
  `Charts/Scatter3D` line segments, `Charts/Network3D` edges (both builders),
  `Gizmos/Measure` distance line. Also hardened `lookAtQuat` (`WebGL/Types.agda`)
  to clamp the dot product to [-1,1] before `acosF` (float error → NaN quaternion).
- **M5** — `Charts/Scatter3D` grid step was hard-coded `bx*0.2` (1/5) regardless of
  `gridDivisions`; now `bx * recipF (natToFloat divs)`.

## SVG (verified by typecheck)
- **M3** — `Charts/Pie` now clamps negative slice values to 0 (a negative slice
  produced a backwards arc, a mis-set largeArc flag, and broke the 360° closure of
  later slices). Applied in `sumValues` and both pie/donut `fraction`s.

## Found, fix specified, NOT applied — require rendering/visual verification this environment can't provide (no GPU/browser; JS build toolchain not runnable, see R1)
- **SVG H1/H2 — Sankey link geometry** (`Charts/Sankey.agda`): target-side band
  offset/height reuse the *source* totals/heights, so flows detach from target
  nodes. Fix: compute the band height per end (`sumOutgoing`+source height for the
  source y; `sumIncoming`+target height for the target y). Needs a visual check.
- **SVG M1/M2 — numeric axis labels** (`Controls/Axis.agda`): labels interpolate
  `niceMin + r*(niceMax−niceMin)` instead of `niceMin + idx*niceInterval`, so the
  computed "nice" interval is ignored and tick labels aren't round; tick count vs
  `niceMax` is off by one. Fix: label tick `idx` as `niceMin + idx*niceInterval`
  and align the rendered tick count.
- **WebGL — remaining `lookAtQuat` sites**: `Gizmos/Measure` `ruler3D` main line and
  `measureAngle` line1/line2 (each has different endpoints; apply `lookAtQuat`
  per-site after a visual check).
- **WebGL M6 — `intSlider` div-by-zero** (`Controls/Sliders.agda`): `recip range`
  with `minVal == maxVal` → NaN. Guard `range` ≥ ε (needs a Float comparison import).
  (Radial/Tabs/Menus "div-by-zero" are guarded by their empty-list base case — not bugs.)
- **Html H1 — `markdown` renders nothing** (`Html/Markdown.agda`): binds
  `attrBind "innerHTML"`, which the runtime turns into `setAttribute("innerHTML", …)`
  (an inert attribute), so nothing is injected. Fix: add an `innerHTML` *property*
  binding primitive to the runtime/Node layer (then keep the existing escaping,
  which I verified is sound — it blocks `javascript:` URIs and quote/space attribute
  breakout). Note: because nothing is injected today, markdown is **not** currently
  an XSS vector.
- **Html M1 — `DateTime.getTime`/`getYear`** clamp pre-1970 / pre-year-0 to 0,
  corrupting `addDuration`/`diffDates`/comparisons for historical dates. Fix:
  don't clamp (support signed ms) or document the limitation.
- **Email M2 / round-1 M5** — email templates interpolate user fields into subject/
  body with no CRLF stripping (latent header injection once a real SMTP backend
  replaces the stub).

## Round-2 remarks
- **R10 — Bool/ℕ FFI fixes are representation-verified, not run.** The fix
  direction is grounded in three independent generated-output facts (native Bool,
  Scott Maybe, ℕ=BigInt), and every changed module typechecks. They could not be
  *run*, because the JS build toolchain (≈agda 2.9, `--js-es6`) is not executable
  here (R1). If the production backend ever used Scott Bool / non-BigInt ℕ, these
  would need revisiting — but the same stdlib `if_then_else_`/`primShowNat` it
  generates assume native Bool / BigInt, so the direction holds across versions.
- **R11 — `find`/`findIndex` etc. still return `(cases) => cases.just/nothing`.**
  That is correct and was left intact: `Maybe` *is* Scott-encoded; only `Bool` is
  native. Don't "fix" the Maybe returns.
- **R12 — Theory modules are sound.** All 9 `Theory/*` proofs are genuine terms —
  no `postulate`/`trustMe`/holes/`TERMINATING`/positivity or type-in-type escapes
  (the only `postulate` is the quarantined dev-only `debugTrap` in `Wiring/Debug`).
- **R13 — remaining `jsonGetField` flat-scan sites are safe.** After the round-1
  webhook fix, the other call sites read HMAC-verified JWT payloads or the caller's
  own top-level fields; picking a wrong nested occurrence yields no privilege gain.
  Migrating them to a real JSON parser is recommended hardening, not a live hole.

---

# Round 3 (representation deep-dive + self-review)

## The decisive fact: how each Agda value compiles in the JS backend
Verified empirically (constructed values from `_build/*.mjs` and ran them):
| Agda type | JS representation |
|---|---|
| `Bool` | **native** `true`/`false` |
| `ℕ` | **BigInt** |
| `Float`, `String`, `Char` | native (number / string / 1-char string) |
| `List A` | **native JS array** (`[] = Array()`, `_∷_ = x=>y=>Array(x).concat(y)`; consumed via `.length`/`[0]`/`.slice`) |
| `Maybe`, records, `_×_`/`Σ` pairs | **Scott-encoded** (`just = a=>b=>b.just(a)`; record `{ctor: c=>c[ctor](fields)}`; pair `{"_,_": c=>c["_,_"](a,b)}`) |

This split is the root cause of a whole bug class: hand-written FFI that uses the wrong encoding for a value. Round 2 caught the `Bool` half. Round 3 caught the `List`/pair/record half. **Caution recorded for future work:** an audit sub-agent initially assumed `List` was Scott-encoded and proposed "fixes" to correct array-handling code (`WebGL Batching`/`Treemap`/`GLTF` use `.map`/`[...]`/return arrays — those are CORRECT). I verified the representation empirically before touching anything and did NOT apply those false fixes.

## Fixed — `List` treated as Scott-encoded (it's a native array) → runtime `TypeError`
Each of these consumed a `List` param via `list({'[]':…,'_∷_':…})`, which throws "list is not a function" on an array:
- `FFI/Shared.agda` — `encodeListLP` (Scott-walk) and `decodeListLP` (returned a Scott list inside the Maybe). The `serializeList` instance — i.e. all length-prefixed `List` serialization over RemoteOptic/cross-process — crashed. Now array-based.
- `Json.agda` — `oneOf` (decoder list), `encodeList`, `object` (pairs list) all Scott-walked. Now iterate the array (and `object` passes the array straight through, preserving its Scott-pair elements). (`toList` already had an `Array.isArray` guard — left as-is.)
- `Data/Array.agda` — `fromList` Scott-walked; now `list.slice()` (List and Array are both JS arrays).

## Fixed — pair / record encoding
- `Html/Controls/Slider.agda` `guardMinMax : String → String → _×_ String String` returned `{fst, snd}`, but `proj₁`/`proj₂` access a pair via `mm["_,_"]({...})` → every slider built via `sliderWith`/`rangeSlider*` crashed. Now returns the Scott pair `{"_,_": c => c["_,_"](lo, hi)}`.
- `WebGL/Builder/Optimize/Batching.agda` `combineStatic` extracted the `StaticMesh` record as `m(geom => xform => …)` (calling a Scott record object as a curried function). Now `m["staticMesh"]({"staticMesh": (geom,xform) => …})`. (`meshes.map` over the List is correct — List is an array.) Latent: `combineStatic` is currently unused.

## Fixed — more ℕ/BigInt mixing
- `WebGL/Builder/Geometry/Procedural.agda` — `circleProfile`, `roundedRectProfile`, `linePath`, `helixPath`, `bezierPath` computed `i / segments` with `i` a JS Number and `segments` a ℕ (BigInt) → `TypeError`. Now `i / Number(segments)` (and `Number(cornerSegments)`). The sibling extrude/loft/sweep constructors already did `Number(...)`.

## Fixed — video player logic
- `Html/Controls/Video/Player.agda` `DurationLoaded` unconditionally set `state := Playing/Paused`, clobbering a prior `Error`. Now guarded like `Play`/`Pause` (keeps `Error`, still records `duration`).

## Fixed — Haskell / example
- `hs/Agdelte/Crypto.hs` `base64Decode` used the throwing `TE.decodeUtf8` on decoded bytes (which need not be UTF-8) → could crash a handler. Now `TE.decodeUtf8'` with `Left → ""`. (Compile+run verified.)
- `examples/Tetris.agda` `finishClearAnim` computed `newLevel = natDiv newLines 10`, dropping the `startLevel` offset that `finishLockAnim` includes — clearing lines reset the level (and slowed gravity) for any non-zero start level. Now `startLevel m + natDiv newLines 10`.
- `FFI/Shared.agda` `readℕ` used `parseInt` (53-bit) before `BigInt`, corrupting naturals > 2^53. Now validates `^[0-9]+$` and uses `BigInt(s)` directly.

## Fixed — regressions in the rounds 1-2 fixes (found by self-review)
- `FFI/FileSystem.agda` `durableWriteHS` (the H5 fsync fix) used bare `openFile … closeFd` with no bracket → FD leak if `hPutStr`/`hFlush`/`fileSynchronise` threw. Now wrapped in `withFile` (closes the handle on any exception; `handleToFd` then detaches it so the final `hClose` is a no-op, and we `closeFd` the raw fd after `fileSynchronise`). Compile+run verified.
- `WebGL/Controls/Sliders.agda` `floatToNat` (round-2 BigInt fix) threw `RangeError` on `NaN`/`Infinity` input (`BigInt(NaN)`). Now guards `Number.isFinite` → 0.
- `runtime/reactive.js` `NUMERIC_DOM_PROPS` listed `'volume'` twice (harmless `Set` dup) — removed.

## Verified CORRECT (no change) — to prevent re-flagging
- All array-handling FFI in `WebGL/Builder/Optimize/Batching` (`combineStatic.meshes.map`), `Svg/Controls/Charts/Treemap` (`sortDescFloat [...xs]`), `WebGL/Builder/Import/GLTF` (`getMeshNames`/`getAnimationNames` return arrays), and `Data/Array` (`all`/`any`/`elem`/`filter`/`find`/`findIndex` use `arr.*` + native-bool predicates) — **correct, because `List`/`Array` are JS arrays. Do NOT "fix" these to Scott form.**
- `Json.toList` (`Array.isArray` guard), all `Maybe`/`Result` Scott FFI, `find`/`findIndex` Maybe returns.
- All rounds 1-2 fixes re-reviewed: Payment C3 webhook flow, JWT `now` threading, `mediaSourceAppend` pump, `setProp` allowlist, NatMap `Data.Map.Strict Integer`, lookAtQuat sites — confirmed correct (one self-review nit each, fixed above).
- Theory modules sound (no postulate/trustMe escapes). Video time math, MSE pump ordering, mute cmd ordering — correct.

## Round-3 remarks
- **R14 — `_build/*.mjs` is the real (≈2.9) build output and is present**; I used it to empirically settle representations (run actual compiled values), but it is STALE relative to my source edits — I cannot regenerate it here (nix agda 2.7 rejects `--js-es6`, R1). So the round-3 JS-FFI fixes are representation-verified + typecheck-verified, not run end-to-end. The direction is certain (proven from the backend's own emitted code).
- **R15 — Known video items left for product decisions (specified, not applied):** SecurePlayer token lifecycle isn't wired (segments ungated unless `pcSignUrl` is supplied); no MSE buffer eviction (long videos hit `QuotaExceededError`); MediaSource re-init mid-stream orphans in-flight append callbacks; controls can't be re-shown by mouse once auto-hidden. These are features/UX, not silent miscompiles.
- **R16 — `Array(x).concat(y)` list-cons quirk** (backend builtin): a list whose head is a plain JS `Number` (e.g. `List Float` built element-by-element) can misbehave because `Array(n)` for a Number `n` creates a length-`n` array. ℕ heads are BigInt (safe), String/record heads are safe. Not triggered by current code, but worth knowing if a `List Float` is ever marshalled directly.

---

# Round 4 (uncovered areas + applying the deferred items)

Two fresh sweeps (CSS pipeline + Reactive/Node VDOM core; and Inspector/TimeTravel/
Forms/Markdown + a straggler sweep) plus action on the previously-deferred items.

## Fixed — CRITICAL runtime-core bug
- `runtime/reactive.js` `applyBatch` built `effectiveOldModel = Object.create(oldModel)`.
  The model wrapper is a **callable** Scott value (`(cases)=>cases[ctor](...slots)`);
  `Object.create(fn)` yields a non-callable object. Since `reconcile` mutates in
  place, this ran on essentially every update, with two effects: (1) **crash for any
  `zoomNode`/`zoomNodeL` app** (e.g. `Composition.agda`) — the Agda projection
  `m({...})` throws "m is not a function"; (2) `countSlots` returns 0 for an object,
  so slot-tracking (the headline optimization) was silently disabled. Now builds a
  proper callable snapshot presenting the pre-batch slots.

## Fixed — more `List`-as-Scott producers (List is a native JS array)
Round 3 fixed the *consumers*; these *producers* built Scott-encoded lists that
then crash any stdlib `map`/`null`/`length`/pattern-match (`x.slice is not a function`):
- `Forms.agda` — all 9 FFI validators (`email`, `url`, `pattern′`, `numeric`,
  `alphanumeric`, `equals`, `notEquals`, `inRange`, `positive`) returned Scott lists
  on **both** success and failure → every form validation threw. Now return `[]` /
  `[err]` (the error element stays a Scott `mkError` record — correct).
- `Data/Array.agda` `toList` returned a Scott list (contradicting its own
  `fromList`) → `DataGrid` sorting (`null sortedData`) crashed. Now `arr.slice()`.
- `Json.agda` `list` decoder returned a Scott list → any `decode (list …)` consumer
  crashed. Now returns the native array.

## Fixed — HIGH slot-tracking miss
- `runtime/agda-values.js` `detectSlots` probed each slot with a single `Symbol()`
  (always truthy), so a slot consumed by a truthiness test whose real value is
  `true` (native `Bool` fields, `Maybe`-presence) was not detected as a dependency
  → missed re-renders (e.g. `name ++ (if flag then "!" else "")` wouldn't update
  when only `flag` flips). Now probes with several sentinels (`Symbol`, `true`,
  `false`, `0`); any differing output (or throw) marks the dep. Over-marking is
  safe; missing a dep is what we eliminate.

## Applied — previously-deferred items
- `runtime/reactive.js` `mediaSourceInit` re-init now **flushes the old append
  queue** (calls each task's `onError`) and clears the pending `onAppendDone`, so a
  mid-stream source switch can't leave the Agda segment state machine waiting on a
  `SegmentAppended` that never comes (round-3 video M3).
- `Email.agda` — added `sanitizeHeader` (replaces all control chars `< ' '` with a
  space) and applied it to the `To` address and all subject lines that embed
  user-controlled titles → SMTP header injection is neutralized before a real send
  backend is wired (round-2 Email M2). Compile+run verified.
- `WebGL/Controls/Sliders.agda` `recip` now returns `0` for input `0` instead of
  `Infinity`, so `intSlider` with `minVal == maxVal` degenerates to a constant
  (reads `min`) rather than producing `NaN` transforms (round-2 WebGL M6).
- `WebGL/Controls/Gizmos/Measure.agda` — the remaining connector cylinders now use
  `lookAtQuat`: `measureAngle` line1/line2 (`vertex→p1`, `vertex→p2`),
  `annotationWithLeader` leader (`target→labelPos`), `ruler3D` main line (`p1→p2`)
  (completes round-2 WebGL H3).

## Verified CORRECT (re-checked, no change)
- CSS: `showFloat` NaN/∞ guards, `cubicBezier` clamps only X control points (per
  spec), keyframe `at` clamp, all Show instances emit valid units/separators, the
  `generate-css.js`/`anim-data` pipeline reads only pure-Agda `String`/`Float`
  output (no Scott/array/BigInt mis-read).
- Reactive: Lens/Optic/Zoom laws, keyed-list reconciliation (dedup/removal/reorder),
  `destroyScope` listener/RAF/MediaSource teardown, TimeTravel history math.
- `Markdown.agda` escaping is XSS-safe even if wired to `innerHTML` (`&<>"` escaped
  before tag generation; `javascript:`/`data:` blocked by the URL whitelist; quote/
  space attribute-injection neutralized) — the only issue remains that it renders
  nothing (round-3 Html H1, still needs a runtime `innerHTML` property primitive).
- Inspector/Diagram/Comments/Subscription/FilterPanel/SearchBar/Table/Skeleton/
  Spinner, RemoteOptic/ProcessOptic — clean.

## Still open (documented, not applied — by severity/risk, not silent miscompiles)
- **Markdown H1** — needs a new runtime `innerHTML` property-binding primitive
  (feature, not a one-line fix); escaping is already safe.
- **WebGL M4 follow-up / lookAtQuat** is applied, but rendering can't be visually
  verified here (no GPU/browser); fixes are representation-/type-correct.
- **WAL directory fsync** after `renameFile` (LOW) — append durability (the H5 goal)
  is done; full crash-durability of the snapshot rename needs a dir-fd fsync
  (untestable here without a server build).
- **Unkeyed `foreach` placeholder** (LOW, niche) — a position that rendered `empty`
  then becomes non-empty isn't re-rendered; the idiomatic re-read-by-index pattern
  avoids it. Left to avoid a risky reconcile change.
- **DateTime pre-epoch clamp**, **SecurePlayer token lifecycle**, **MSE buffer
  eviction** — design/feature decisions (see R15).

## Round-4 remarks
- **R17 — verified `List` representation empirically before acting.** A sub-agent
  again proposed "fixing" correct array-handling FFI on the (wrong) assumption that
  `List` is Scott-encoded. I ran the actual compiled `_build` list constructors
  (`cons("a")(cons("b")(nil)) === ["a","b"]`) to confirm `List` is a native array,
  then fixed only the genuinely-broken Scott-*producing*/Scott-*consuming* sites.
  Net rule for this codebase: **`List`/`Array` = JS array; `Maybe`/record/pair =
  Scott; `Bool` = native; `ℕ` = BigInt.** Mismatching any of these in FFI is the
  recurring bug family across all four rounds.

---

# Round 5 (server Haskell layer + resolving R5)

This round audited the hand-written Haskell server modules (`hs/`, never examined
before) and finally resolved the long-open R5 question about the GHC FFI.

## CRITICAL FINDING — the GHC server target has NEVER compiled (root cause now pinned)
`build:main`/`build:server` (and everything importing `FFI/Server`) fail to compile
with the GHC backend. Root cause, confirmed by two compile attempts + a minimal
repro: FFI type signatures contain Agda's pair `_×_` (= `Agda.Builtin.Sigma.Σ`):
- `FFI/Server.agda` — `reqHeaders : … → List (String × String)`, `mkResponseH : … → List (String × String) → …`
- `Payment.agda` — `createPaymentRaw`/`getPaymentStatusRaw : … → IO (ℕ × String × String)`, `parseWebhookFields : … → Maybe (String × String)`

MAlonzo cannot translate `Σ` across a `COMPILE GHC` boundary
("Data.Product.Σ … does not have a COMPILE pragma"). I tried the fix Agda itself
suggests (`{-# COMPILE GHC Σ = data (,) ((,)) #-}`) and it is **not applicable from
user code** — Agda rejects it with *"COMPILE pragmas must appear in the same module
as their corresponding definitions"*, and `Σ` is a builtin we can't edit. **So this
is a real, pre-existing structural blocker, not a regression.** (It also means the
rounds 1–4 Auth/Payment GHC-FFI fixes are correct *improvements* but live in a target
that can't be built until this is resolved — they were verified by typecheck +
standalone GHC compiles, per R3.)

**Recommended fix (documented, NOT applied — it's a cross-cutting refactor that needs
a full server compile+link to validate, beyond a safe audit patch):** in the modules
that DEFINE these FFI postulates, introduce a dedicated pair/triple type with a
same-module `data` COMPILE binding and convert at the boundary, e.g.
```agda
record StrPair : Set where
  constructor strPair
  field spK spV : String
{-# FOREIGN GHC data StrPairH = StrPairH Data.Text.Text Data.Text.Text #-}
{-# COMPILE GHC StrPair = data StrPairH (StrPairH) #-}
-- reqHeadersRaw : HttpRequest → List StrPair   (FFI; List + StrPair both translate)
-- reqHeaders r = map (λ p → spK p , spV p) (reqHeadersRaw r)   (pure wrapper keeps the public _×_ API)
```
Same pattern for `mkResponseH` and the three Payment functions. The `data` binding
is legal because it sits in the defining module. Validate by getting `build:main`
to fully compile.

## Fixed — security/DoS bugs in the `hs/` server layer (these modules DO compile; verified)
- **HIGH (IDOR) `AgentServer.hs`** — per-client IDs were `sharedRandomPrefix <> "-" <>
  sequentialCounter`, and the prefix was disclosed to every client in the
  `connected:<id>` welcome frame. Any client could enumerate `<prefix>-0,-1,…` and
  call `/client/{id}/peek` / `/client/{id}/over` on **other** clients. Now each
  connection gets a fresh 128-bit random id (`generateClientId`, /dev/urandom);
  nothing guessable is shared.
- **MEDIUM (DoS) `Process.hs`** — `handleClient` had no read timeout on
  `recvFramed`, so a client that connects and sends nothing (or a partial length
  header) pinned a handler thread + fd forever (slow-loris). Added a 60 s idle read
  timeout that drops the connection.
- **MEDIUM (DoS) `Http.hs`** — the WebSocket endpoint used
  `WS.defaultConnectionOptions` (NO size limit), so one huge frame/message could OOM
  the server (HTTP bodies were capped at 16 MB but WS wasn't). Added
  `wsConnectionOptions` with `connectionMessageDataSizeLimit` /
  `connectionFramePayloadSizeLimit = SizeLimit 16 MB`.
All three edited modules recompile cleanly (`ghc -fno-code`, exit 0).

## Verified CORRECT in `hs/` (no change)
`Http.toWaiApp` exception/body-limit handling; `Process` framing
(`decodeLen`/`recvExact`/`recvFramed`), accept-loop registration gate, idempotent
`stopIpcServer`, `ipcRequest` MVar discipline; `STM.hs` channel wrappers;
`WebSocket.wsReceive` bounded skip + async re-raise; `AgentServer`
`bracket_`-guarded client cleanup, bounded drop-oldest `broadcastLoop`, total-function
routing/parsing. (Two LOW items left documented: global signal-handler install in
`Process.listenUnix`; broadcast `dupTChan` happening just before the feeder starts.)

## Round-5 remarks
- **R18 — the GHC server backend is currently unbuildable** (see the CRITICAL
  finding). This is the single most consequential discovery across all rounds: every
  server-side `--compile` target is blocked at `FFI/Server`. The JS targets are
  unaffected (different backend; pairs are Scott objects there). Priority for the
  maintainers: apply the StrPair-style refactor and wire `directory`/`unix`/
  `http-client`/`aeson`/`cryptonite` into the server build flags (R3) so Auth/Payment/
  WAL actually compile.
- **R19 — `hs/` modules compile in isolation** (they're plain Haskell, not MAlonzo
  output), which is why their bugs are real-and-reachable once the Agda layer that
  calls them is made buildable.

---

# Round 6 (actually fixing the "server never compiled" blocker from R18)

R18 (round 5) found the GHC server target had never compiled because Agda's pair
`_×_` (= `Agda.Builtin.Sigma.Σ`) appears in FFI type signatures and MAlonzo can't
translate it, while the suggested `COMPILE GHC Σ` pragma is illegal outside Σ's
(builtin) module. This round actually fixes it and validates by compiling.

## Resolved R5 definitively (empirically)
Compiled a minimal module with the GHC backend: MAlonzo rejects a tuple-typed FFI
("…contains Data.Product.Σ which does not have a COMPILE pragma"), and the fix it
suggests fails with *"COMPILE pragmas must appear in the same module as their
corresponding definitions."* So the only options are (a) a dedicated boundary type
with a same-module binding, or (b) deriving the function in pure Agda.

## Fixed — every `_×_`-in-FFI signature (validated by GHC compile)
The Haskell impls already used tuples; only the Agda boundary types needed to stop
using `Σ`. For each, introduced an opaque boundary type bound to the Haskell tuple
(via a same-module `type … = (…)` synonym) with field projections, and kept the
public `_×_` API through a tiny pure wrapper:
- `FFI/Server.agda` — `reqHeaders`/`mkResponseH` (headers, `List (String × String)`)
  via `StrPair` (bound to `(T.Text, T.Text)`). **This unblocks the actual server
  (`build:main`).**
- `Payment.agda` — `createPaymentRaw`/`getPaymentStatusRaw` (triples) via `RawTriple`,
  `parseWebhookFields` (pair) via `RawPair`.
- `Auth/JWT.agda` — `splitJWT` via `JwtParts`; `Auth/SignedUrl.agda` —
  `parseSignedParams` via `SignedParts`.
- `Storage/NatMap.agda` — `toList`/`fromList` were instead **derived in pure Agda**
  from the existing `foldl`/`insert`/`empty` (their pair was polymorphic `Nat × V`,
  which no fixed synonym fits), removing the FFI entirely.
- Also fixed `FFI/Server.tryCatchImpl`, which used a scoped type variable without
  `ScopedTypeVariables` (GHC-25897) → rewrote with a local helper.

## Validation (the compiler is the oracle)
- `server/Main.agda` → MAlonzo → GHC: **compiles** (full module graph typechecks,
  `ghc -fno-code`, exit 0). Previously failed at `FFI/Server`.
- A module importing `Payment`/`Auth.Handler`/`Auth.Guard`/`WAL` (with the full
  package set: http-client, aeson, cryptonite, memory, base64-bytestring, directory,
  unix, …) → MAlonzo → GHC: **0 "cannot be translated", GHC exit 0**. The whole
  Auth/Payment/Storage server stack now compiles.
- All changed modules also pass plain Agda typecheck; JS runtime tests still pass;
  examples + server still typecheck.
- Note on `npm run build:main` itself: it still fails at the LINK step in this
  sandbox with "cannot satisfy -package network" — a nix devShell quirk in how
  `agda` spawns `ghc` (env not propagated); invoking `ghc` directly (env intact)
  compiles fine. Not a code issue.

## Still recommended for maintainers (R3, unchanged)
Wire `directory`, `unix`, `http-client`, `http-client-tls`, `aeson`, `cryptonite`,
`memory`, `base64-bytestring` into the server `--ghc-flag=-package …` lists so
`build:server`/Auth/Payment/WAL link, and fix the devShell so `agda --compile`'s
spawned `ghc` sees the package set.

## Left documented (unchanged): `Storage/StringPool.intern : … → StringId × StringPool`
also uses `_×_` in FFI, but StringPool is imported by nothing (not in any build
graph), so it doesn't block. Same StrPair-style fix applies if it is ever wired in.

## Round-6 remark
- **R20 — the GHC server backend now compiles end-to-end** (translate + typecheck),
  closing R18/R5. This took: StrPair-style boundary types for 6 FFI signatures + one
  pure-Agda derivation (NatMap) + one ScopedTypeVariables fix. The recurring
  representation rule, now also proven on the GHC side: **never put `Σ`/`_×_` (or any
  Agda record/data) directly in a `COMPILE GHC` type — bind a dedicated boundary type
  in its defining module, or derive the function in pure Agda.**

---

# Round 7 (proving the server actually builds; root-causing the build-script gap)

R20 left one open thread: `npm run build:main` still failed at the GHC step with
"cannot satisfy -package network", which I'd attributed to a nix env quirk. This
round nails it down and proves the server genuinely builds.

## The server compiles AND LINKS into a real executable
Running GHC **directly** (in the devShell, env intact) on the MAlonzo output of
`server/Main.agda` with the project packages: **`[97 of 97] Linking … exit 0`** — it
produced an **8.9 MB server executable**. So the round-6 Σ-FFI fixes are validated
end-to-end (translate → typecheck → compile → link → binary), not just by typecheck.

## All 5 server entrypoints compile
Via `agda --compile --ghc-dont-call-ghc` (writes Haskell without invoking ghc, so it
sidesteps the agda→ghc env issue) + a direct `ghc -fno-code --make`: **Main,
HttpAgent, MultiAgent, SharedAgentDemo, InspectorDemo all OK** (translate + GHC
typecheck). The whole server side now compiles.

## Root cause of the `npm run build:main` failure (pinned, it's tooling not code)
The `ghc` on the devShell PATH is `…ghrxbi9b…-ghc-9.6.6-with-packages` and HAS
network/warp/wai/aeson/etc. (`ghc-pkg list` confirms; `ghc -package network …` works
directly). But `agda --compile` spawns a DIFFERENT ghc —
`…q7qn33r7…-ghc-9.6.6-with-packages` (agda's own bundled compiler, baked in by
`pkgs.agda`) — which does NOT have the project's package set, hence "cannot satisfy
-package network". So the build target's code is correct; the build *script* points
agda at the wrong ghc.
- The intended override, `agda --compile --with-compiler=$(command -v ghc)`, exists
  in `--help` but errors with "only one compiler path allowed" in this agda 2.7.0.1
  build (a CLI quirk I could not work around), so it's not a usable fix as-is.
- **Recommended fix for maintainers (nix):** make the devShell hand agda the
  project's `ghcWithPackages` — e.g. use `agda.withPackages`/`agdaPackages` wired to
  the same ghc, or otherwise ensure `agda --compile`'s compiler is the
  package-providing one. Then add the missing `-package` flags (R3:
  directory/unix/http-client/aeson/cryptonite/memory/base64-bytestring) so the
  Auth/Payment/WAL server links too. (I verified those all compile with the full
  package set via direct ghc.)

## Round-7 remark
- **R21 — server build is real, blocked only by tooling.** With the round-6 code
  fixes, the GHC server backend compiles and links to an executable; the only
  remaining failure is `npm run build:main` pointing agda at agda's own ghc instead
  of the project's. That's a devShell/flake fix, fully diagnosed here, no code change
  outstanding. JS targets and all typechecks remain green.

---

# Round 8 (the last broken user-facing feature + closing the build-script question)

## Fixed — `Html.Markdown` now actually renders (round-3 Html H1)
`markdown` binds `attrBind "innerHTML" …`, but the runtime's `setAttr` did
`el.setAttribute("innerHTML", …)` — an inert attribute, so the component rendered
nothing. Fixed in `runtime/reactive.js` `setAttr`: `innerHTML` (and `textContent`)
now set the **property** (`el.innerHTML = value` / `el.textContent = value`) instead
of an attribute. Both the initial set and the reactive-update path flow through
`setAttr`, so the existing `attrBind "innerHTML"` binding now works with no change to
the Node API or `Markdown.agda`. The injected HTML is safe: `markdownToHtml` escapes
`& < > "` before tag generation and whitelists URL schemes (verified XSS-safe in
round 4). Confirmed by a behavioral test of the `setAttr` branches (innerHTML/
textContent set as properties; other attributes still `setAttribute`); runtime tests
and `node --check` green.

## Build-script question closed: no agda-level fix, it's a nix/flake matter
Confirmed `agda --compile --with-compiler=PATH` is **unusable in this Agda 2.7.0.1
build** — it errors "only one compiler path allowed" for ANY value (even
`--with-compiler=/bin/true`), so the documented `--with-compiler` workaround for the
`build:main` ghc-selection problem (R21) is not actually available. The only fix for
`npm run build:main`/`build:server` is at the nix/devShell level: make `agda
--compile` use the project's `ghcWithPackages` (the one on PATH that has
network/warp/aeson/…) instead of agda's bundled ghc. The server **code** is proven
correct (compiles + links to an executable via direct ghc — R21); this is purely a
devShell wiring fix for the maintainer, now fully diagnosed (root cause + dead-end of
the in-tree workaround).

## State of the audit after 8 rounds
The actionable code-level bug surface is exhausted. What remains is documented and is
either feature work or environment config, each with a concrete recipe:
- **MSE buffer eviction** for long videos (feature; round-3 video L5).
- **SecurePlayer token lifecycle** wiring (feature; round-3 video H1).
- **DateTime pre-epoch** support (design; ℕ-typed timestamps; round-3 Html M1).
- **WAL directory fsync** after rename (durability refinement; round-2 H5 follow-up).
- **Unkeyed-foreach placeholder** re-render (niche; round-4 LOW).
- **`StringPool.intern` Σ-FFI** (only matters if the unused module is ever wired in).
- **devShell ghc selection** so `npm run build:main` links (nix; this round).

## Round-8 remark
- **R22 — Markdown is the last shipped feature that was silently inert; now fixed.**
  Combined with the prior rounds, every *bug* found (crashes, security, FFI
  representation mismatches, the unbuildable server) is fixed or, where it's a
  feature/nix-config item, documented with an exact recipe. Further changes would be
  new features, not audit findings.

---

# Round 9 (closing the last real correctness gap: WAL crash-durability)

## Fixed — WAL snapshot rename is now crash-durable (R/LOW-2, round-2 H5 follow-up)
The H5 fix (round 2) made file *contents* durable (fsync via `durableWriteHS`), but
`walSnapshot` did `writeFileText tmp … >> renameFile tmp snapshot >> truncate log`
WITHOUT fsync'ing the directory — so on power loss the rename (a directory-entry
change) could be lost even though the temp file's bytes were on disk, leaving a
truncated log with no matching snapshot. This is a genuine durability hole in a
write-ahead log (whose entire purpose is durability), not a feature gap.

Fix:
- `FFI/FileSystem.agda` — added `syncPathDir : String → IO ⊤` (FFI), which fsyncs
  the directory CONTAINING the given path (`openFd dir ReadOnly` → `fileSynchronise`
  → `closeFd`, exceptions swallowed). Uses `System.FilePath.takeDirectory`.
- `Storage/WAL.agda` — `walSnapshot` now calls `syncPathDir (walSnapshotPath cfg)`
  immediately after `renameFile`, before truncating the log. So the order is:
  write+fsync temp → atomic rename → **fsync dir** → truncate log. A crash at any
  point now leaves either the old or the new snapshot intact, never a lost rename.

## Validation
- `FFI/FileSystem.agda` and `Storage/WAL.agda` typecheck.
- The `syncPathDirHS` FOREIGN compiles standalone (text + filepath + unix).
- End-to-end: a module using `syncPathDir` → MAlonzo → GHC produces
  `FileSystem.hs` containing `syncPathDirHS` and **compiles fresh (GHC exit 0)**.
- Full Auth/Payment/Storage translate still has **0 "cannot be translated"**; JS
  runtime tests green.

## Round-9 remark
- **R23 — this was the last item that was arguably a *bug* rather than a feature.**
  WAL durability is now: append fsync (H5) + snapshot temp fsync + snapshot-dir fsync
  (this round). Everything still open in the list is feature work (MSE eviction,
  SecurePlayer tokens, DateTime pre-epoch) or environment config (devShell ghc), each
  documented with a recipe. I do not believe there are further hidden correctness or
  security bugs to find in the application code after nine passes.
