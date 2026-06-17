# Project Notes

## CRM («Ядро услуг») — спецификация и протокол

Мы строим домен-нейтральное «ядро услуг» (CRM-платформу) поверх фреймворка agdelte.
Полная спека — **`docs/SPEC.md`**. Перед работой над CRM прочитать:
- **раздел 4** — слои (`app → packs → services-core → agdelte`, зависимость только вниз) и два grep-стража;
- **раздел 5.6** — маппинг типов SQL↔Agda и три границы FFI;
- **раздел 13** — контракт headless-API;
- **раздел 14** — порядок задач Ф0 (текущая задача — одна за сессию);
- **раздел 15** — протокол сессий (идиомы копировать из исходников, не изобретать).

**⚠️ ВАЖНО — текущее решение по хранилищу (ЗАМЕНЯЕТ SQL-части SPEC §14).**
По итогам аудита выбран движок **WAL + in-memory, типизированные записи (НЕ Postgres)**.
Поэтому SQL-ориентированные §5.6/§14.3/§14.4 SPEC — это **запасной Postgres-путь**, а не
текущая ветка. Перед работой над хранилищем/доменом читать **в этом порядке**:
- **`docs/adr/0001-storage-wal-in-memory.md`** — решение и обоснование (закрывает §12 SPEC);
- **`docs/concepts/storage-model.md`** — полный дизайн + механика рантайма (типы+индексы,
  `IndexedMap`, `Op`, монада `Txn`, транзакции, разрешимость, Часть V — как крутится);
- **`docs/concepts/declarative-storage.md`** — дизайн-вектор: хранилище как реактивный UI
  (схема-`template` → кодек/индексы/SQL/пейджинг выводятся интерпретаторами); partial-RAM ≡ SQL ≡
  смена backend. Фундамент будущей эволюции (SQL/масштаб), реализуется инкрементально;
- **`docs/plan-crm-core.md`** — исполняемый чеклист; **следующий шаг — Фаза 0: `IndexedMap`**.

Postgres-путь (hpgsql, раннер миграций, схема §5/§14.3) — scale-out за headless-API;
рецепт GHC-сборки и грабли (zlib `LIBRARY_PATH`, `-threaded`, устаревший `.agdai`-кэш) —
в **`docs/POSTGRES-SPIKE.md`**.

**Раскладка слоёв — ДЕКОМПОЗИЦИЯ ЗАВЕРШЕНА (2026-06-16).** Монолит разрезан на отдельные
**зарегистрированные Agda-библиотеки** в `~/.agda/` (каждая — свой каталог + git-репо;
реестр `~/.agda/libraries`; `.agda-lib` с `name/include/depend`). Имена модулей сохранены
(`Agdelte.*`; CRM — `Crm.*`), поэтому строки import у потребителей не менялись. Граф (вниз):
- **`agdelte-store`** (`~/.agda/agdelte-store`, depend: stdlib) — генерик-стор: `Agdelte.Storage.`
  `{NatMap,IndexedMap,Wire,WAL,Txn,FFI}` (встроенный event-sourced стор + самодостаточный FFI);
- **`agdelte-payments`** (depend: stdlib) — `Agdelte.Payment.YooKassa` (ЮKassa-клиент, свой http-client);
- **`agdelte`** (этот репо, `src/`+`hs/`) — **чистый фреймворк**: reactive UI, `FFI.*` (вкл.
  `FFI.Crypto`), `I18n`, `Email`, HTTP-сервер. Импортирует домена ноль; Auth НЕ содержит;
- **`agdelte-auth`** (`~/.agda/agdelte-auth`, depend: stdlib+agdelte) — генерик-безопасность:
  `Agdelte.Auth.{JWT,Middleware,Role,SignedUrl,Client}` (на `FFI.Crypto/Server/Time` + `Core.Cmd`);
- **`agdelte-crm`** (`~/.agda/agdelte-crm`, depend: stdlib+store+agdelte) — `Crm.*` + `ServicesCore`;
- **`agdelte-courses`** (depend: stdlib+store+agdelte+**auth**+payments) — легаси видео-платформа
  (`Storage.AppStore`, `Payment` хендлеры, `Auth.{Guard,Handler}`, `Html/Controls/{Cart,…}`).
- **`agdelte-pack-psych`** (depend: stdlib+store+agdelte+crm) — вертикаль брони/коучинга.
- **app-слой остался в этом репо:** `server/` (CrmServer + тесты), `agdelte.cabal`, `package.json`
  gen-скрипты (резолвят либы через `-i ~/.agda/agdelte-{store,crm,courses}`), `docs/`. `app/`/`packs/` —
  скелеты (README/SQL). Postgres-FFI/пул/раннер миграций — генерик-инфра, остаются в `agdelte`.

**Два grep-стража нейтральности** (`scripts/check-neutrality.sh`):
- в `agdelte/` (`src/`, `hs/`) нет слов `party|engagement|услуг…`;
- в CRM-ядре (`~/.agda/agdelte-crm/Crm`, через `$AGDELTE_CRM_DIR`) нет `psych|vet|transfer|медцентр…`.

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
