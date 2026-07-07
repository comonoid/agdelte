# Project Notes

## Agdelte — фреймворк и экосистема

Этот репозиторий — **чистый фреймворк** `agdelte`: reactive UI (без Virtual DOM), `FFI.*`
(Server/Json/Time/Crypto/HttpClient/FileSystem), `I18n`, `Email`, HTTP-сервер. Импортирует домена
ноль. Домены/приложения — в отдельных репозиториях (раскладка ниже). *(CRM удалён — вся его
функциональность перенесена в CXM; несколько аудитов подтвердили.)*

**Хранилище (для генерик-стора `agdelte-store`) — POSTGRES-ONLY (2026-07-07).** Стор — типизированный
**EDSL, компилирующийся в SQL**: схема → DDL/INSERT/UPSERT/DELETE/SELECT (`Storage.SQL`), команды —
freer-монада `Storage.Free` (`Tx`), исполнение `Storage.FreeIO` (BEGIN→fold→COMMIT) через Conn-шов
`Storage.PgConn` над драйвером `Storage.Postgres` (hpgsql); JSON-декод `Storage.JsonRow`, миграции-
как-термы `Storage.Migration`, query-EDSL `Storage.Query`. Есть нативный эталонный интерпретатор
(чистый, без БД) — он же чекер lock-дисциплины и тест-дубль. **WAL + in-memory движок
(`IndexedMap`/`NatMap`/`WAL`/`Txn`) — УДАЛЁН** как неудачный эксперимент (был отложенным путём, стал
единственным — но Postgres-only победил). Перед работой над хранилищем читать:
- **`~/cxm-core/docs/pg-store-plan.md`** — решения, контракты (READ COMMITTED навсегда, lock-дисциплина
  lockRoot/lockKey, Conn-скоуп-контракт, миграции-EDSL, аудиты, milestones);
- **`~/cxm-core/docs/edsl-intro.md`** — как устроен 3-слойный стор-EDSL и почему им легко пользоваться;
- **`docs/POSTGRES-SPIKE.md`** — GHC-грабли живьём (zlib `LIBRARY_PATH`, `-threaded`, устаревший
  `.agdai`-кэш). `docs/adr/0001` + `storage-model.md`/`declarative-storage.md` — ИСТОРИЯ (WAL-эра).

**Раскладка репозиториев (2026-07-03).** Либа = каталог + `.agda-lib` (`name/include/depend`);
реестр `~/.agda/libraries` резолвит по имени. Граф (вниз):
- **`agdelte`** (ЭТОТ репо: `src/`+`hs/`+`server/`+build harness `agdelte.cabal`/`package.json`) —
  фреймворк. depend: stdlib + `agdelte-store`. Сюда же входит сборка PG-бинарей CXM
  (`cxm-server-pg`/`pg-diff`/`pg-bench`).
- **`agdelte-store`** (`~/agdelte-addons/agdelte-store`, depend: stdlib) — генерик стор-EDSL
  `Agdelte.Storage.{Schema,SQL,Free,FreeIO,JsonRow,PgConn,Migration,Query,FFI,Postgres}` (Postgres-only;
  WAL-движок NatMap/IndexedMap/WAL/Txn удалён 2026-07-07).
- **`agdelte-auth`** (`~/agdelte-addons/agdelte-auth`, depend: stdlib+agdelte) — `Agdelte.Auth.*`.
- **`agdelte-payments`** (`~/agdelte-addons/agdelte-payments`, depend: stdlib) — `Agdelte.Payment.YooKassa`.
- **`cxm` + `cxm-pack-psych`** (`~/cxm-core`, depend: stdlib+agdelte+store+auth+payments[+cxm]) —
  движок CXM + психо-пак (`Cxm.*`/`PsychCxm.*`); PG-сервер `~/cxm-core/server/CxmServerPg.agda`
  (+ `PgDiff`/`PgBench`) там же (build-харнесс — в этом репо).
- **Архив** `~/.agda/_archive/`: `agdelte-courses` (легаси видео) + до-переносные git-оригиналы
  store/auth/payments. `agdelte-crm` и легаси pack-psych — УДАЛЕНЫ.

**Страж нейтральности** (`scripts/check-neutrality.sh`): в `agdelte/` (`src/`, `hs/`) нет доменных
слов (`party|engagement|услуг…`) — фреймворк домена не называет.

## Environment

- OS: NixOS. Do not assume standard binaries are available (e.g. python3, pip, dpkg, apt).
  Use `nix-shell -p <package>` or check availability before running commands.
- Target platform: Linux only. Windows is not a supported target — POSIX-specific code (signals, Unix sockets) is fine.

## Generated files — DO NOT EDIT

The following paths contain files generated from Agda sources. **Never edit them directly** —
changes will be silently overwritten on the next build. Fix the Agda source instead.

| Generated path | Source | Build command |
|---|---|---|
| `_build/jAgda.*.mjs` | `src/**/*.agda`, `examples/*.agda` | `npm run build:<name>` |
| `examples_html/generated/examples.css` | `examples/Styles.agda` (`examplesCSS`) | `npm run css:examples` |
| `examples_html/generated/css-demo.css` | `examples/CssDemo.agda` (`appCSS`) | `npm run css:demo` |
| `examples_html/generated/css-full-demo.css` | `examples/CssFullDemo.agda` (`appCSS`) | `npm run css:full-demo` |
| `examples_html/generated/controls-demo.css` | `examples/ControlsDemo.agda` (`appCSS`) | `npm run css:controls-demo` |
| `examples_html/generated/agdelte-controls.css` | `src/Agdelte/Css/Controls.agda` (`controlsCSS`) | `npm run css:controls` |
| `examples_html/generated/index.css` | `examples/IndexStyles.agda` (`indexCSS`) | `npm run css:index` |
| `examples_html/generated/anim-demo.json` | `examples/AnimDemo.agda` | `npm run css:anim-data` |

Pipeline: `agda --js` → `_build/jAgda.*.mjs` → `node scripts/generate-css.js` → `.css`/`.json`.

If a generated CSS file has wrong colors/styles, edit the corresponding Agda source
(e.g., `hex "#abc"` → `var "agdelte-primary"` in `Styles.agda`).

**This also applies to code review and recommendations:** when analysing generated CSS,
attribute issues to the Agda source or the generation pipeline — never suggest editing
the generated `.css`/`.json` files directly.
