# Project Notes

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
