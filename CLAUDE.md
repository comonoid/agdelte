# Project Notes

## CRM («Ядро услуг») — спецификация и протокол

Мы строим домен-нейтральное «ядро услуг» (CRM-платформу) поверх фреймворка agdelte.
Полная спека — **`docs/SPEC.md`**. Перед работой над CRM прочитать:
- **раздел 4** — слои (`app → packs → services-core → agdelte`, зависимость только вниз) и два grep-стража;
- **раздел 5.6** — маппинг типов SQL↔Agda и три границы FFI;
- **раздел 13** — контракт headless-API;
- **раздел 14** — порядок задач Ф0 (текущая задача — одна за сессию);
- **раздел 15** — протокол сессий (идиомы копировать из исходников, не изобретать).

**Раскладка слоёв и извлекаемость.** CRM должен оставаться извлекаемым в отдельный репозиторий:
- инфраструктура фреймворка (Postgres-FFI, пул, jobs, раннер миграций) — в `agdelte` (`src/Agdelte/**`,
  `hs/Agdelte/**`), домен-агностично;
- CRM-специфика — в отдельных top-level каталогах `services-core/`, `packs/`, `app/`, каждый со своим
  `.agda-lib` (`depend: agdelte, standard-library`), чтобы поднять их одним `git mv` в новый репозиторий.

**Два grep-стража нейтральности (раздел 4):**
- в `agdelte/` (т.е. `src/`, `hs/`) нет слов `party|engagement|услуг…`;
- в `services-core/` нет слов `psych|vet|transfer|медцентр…`.

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
