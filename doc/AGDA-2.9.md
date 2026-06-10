# Custom Agda 2.9 toolchain

agdelte's JS build (`agda --js --js-es6 …`) requires Agda **2.9**; the nix
`pkgs.agda` (2.7.0.1) lacks `--js-es6`. The 2.9 compiler is built from the local
checkout at **`/home/n/agda`** (Agda 2.9.0, `master`) and installed to
`~/.local/bin/agda`.

## Build / rebuild

```sh
bash scripts/build-agda.sh            # builds from /home/n/agda, installs to ~/.local/bin
bash scripts/build-agda.sh /path/to/agda-src   # alternate checkout
```

This runs `cabal install exe:agda` with the **system ghc (9.10.3)** — plain cabal,
*not* the checkout's `nix develop` (its `Agda-dev-shell` pulls texlive and is far
heavier than needed just to build the compiler). Incremental after the first build.

Re-run it:
- after you patch Agda (e.g. the tagged-representation work), and
- after a `nixos-rebuild` (see GC note).

## Why ~/.local/bin/agda sometimes "stops running"

A `cabal install` binary on NixOS links the system glibc/gmp/etc. from the nix
store. Those paths are **not** GC roots, so `nix-collect-garbage` after a
`nixos-rebuild` can delete them, leaving `agda` with a dangling ELF interpreter
("no such file or directory"). `scripts/build-agda.sh` mitigates this by pinning the
binary's store dependencies as **indirect GC roots** under
`~/.local/state/agda-gcroots/`. If it ever breaks anyway, just re-run the script —
the fresh build links the current (live) glibc.

## stdlib

Uses `~/.agda/agda-stdlib` (standard-library 2.4), registered in
`~/.agda/libraries`. The cabal-built 2.9 reads `~/.agda/libraries` **by default**
(no `--library-file` needed), so `package.json`'s bare `agda …` invocations work.
agda 2.9 + stdlib 2.4 typechecks the whole agdelte codebase with no breakage
(verified on Core/SVG/WebGL/Tetris/server/Payment).

## Toolchain split (current)

| Task | agda used | notes |
|---|---|---|
| JS build (`build:*`) | `~/.local/bin/agda` 2.9 | bare `agda` on PATH; emits `_build/jAgda.*.mjs` |
| GHC server build (`build:main`/`build:server`) | nix `pkgs.agda`… | see the server-FFI notes; agda's ghc-selection caveat |
| my audit typechecks | nix `agda --library-file=…` 2.7 | historical; 2.9 also typechecks cleanly |

To unify on 2.9 everywhere, point `scripts/typecheck-all.sh` and the GHC build at
`~/.local/bin/agda` too. (Not yet done — the JS path, which needed 2.9, is the one
that was broken and is now fixed.)

## IMPORTANT — tagged representation ⇄ the JS runtime/FFI

The in-progress **tagged representation** changes how Agda values compile to JS.
Today's encodings (established during the FFI audit, see `AUDIT-FIXES.md`):
`Bool`→native JS boolean, `ℕ`→BigInt, `List`→native JS array, `Maybe`/records/
`_×_` pairs→Scott-encoded. When tagged representation lands, **two coupled layers
must move with it**:
1. `runtime/agda-values.js` — `listToArray`/`arrayToList`, `natToNumber`/`numberToNat`,
   `fromBool`/`toBool`, Scott probing, `detectSlots`.
2. Every `{-# COMPILE JS #-}` pragma in `src/` that hand-encodes a value
   (Data/Array, Json, Css/Color, DateTime, WebGL `_<F_`/`stringEq`, Forms,
   Html/Controls/Slider `guardMinMax`, Markdown, …).

Recommend a **representation-conformance test**: round-trip a few Agda values
(Bool/ℕ/List/Maybe/record/pair) Agda→JS→JS-consumer and assert the shape, so a
representation change is caught automatically instead of as scattered runtime
crashes (the bug class that dominated the audit).

## Full rebuild under 2.9 — results & gotchas (first run)

Doing a clean `npm run clean && npm run build:all` with the freshly-built 2.9:

- **Browser examples (Agda → JS): all 36 build ✓.** All 384 generated `_build/jAgda.*.mjs`
  parse cleanly (`node --check`).

- **GOTCHA — no `//` line comments inside `{-# COMPILE JS #-}`.** Agda 2.9's JS
  backend collapses a short COMPILE-JS body onto ONE line, so a `//` comment
  swallows the rest of the line — including the actual code and closing braces —
  producing a syntactically broken `.mjs` (the parse error surfaces on the trailing
  `;export default exports;`). `agda` typecheck does NOT validate JS inside COMPILE
  pragmas, so this is invisible until the JS build runs. Fixed all such comments in
  the project to `/* … */` block comments (Data/Array, FFI/Shared, Html/Controls/
  Slider — which actually broke — plus Forms, Json defensively). **Convention: only
  `/* */` comments in COMPILE JS bodies.**

- **CSS generation was `O(2ⁿ)` — `with` on a recursive call, NOT list `O(n²)`.**
  The large stylesheets (`css:examples`, `css:controls`) did not finish in ~5 h at
  100 % CPU. The cause is **not** the `List` representation. `renderStylesheet` /
  `renderRulesAt` used `with renderStylesheet rs` (the recursive call as scrutinee),
  and the JS backend compiles a `with`-scrutinee as a **non-memoised thunk that is
  forced twice** per clause → `O(2ⁿ)`. Full analysis + minimal repro:
  `doc/agda-with-scrutinee-bug.md` (reproduces identically in 2.8.0 and 2.9.0, so it
  is not a 2.9 regression either).

  **Workaround landed (no Agda patch needed):** `src/Agdelte/Css/Stylesheet.agda`
  was rewritten to avoid `with` on the recursion — render rules into a `List String`,
  drop empties, then `intercalateS "\n\n"`. The recursive result is consumed exactly
  once, so it is linear. Measured after the fix:

  | target | before | after |
  |---|---|---|
  | `css:examples` (38 KB) | did not finish in 5 h | **0.38 s** |
  | `css:all` (all 7, incl. 59 KB `agdelte-controls.css`) | — | **≈ 3 s** |

  The committed `examples_html/generated/*.css` are regenerated and current.
  Tagged representation would still help list `O(n²)` separately, but it would **not**
  have fixed this — the `with` thunk is the dominant cost. Avoid `with` on a recursive
  call (or any expensive scrutinee used in >1 branch) in JS-backend code until the
  backend memoises with-scrutinees.

- **Server builds (Agda → GHC) still fail** at the `agda --compile` step — `agda`
  spawns its own bundled ghc (lacking the project's haskell packages) rather than the
  package-providing one. Separate from the JS path; see the server-FFI notes /
  `AUDIT-FIXES.md` R20–R21. (The server *code* compiles + links via direct ghc.)

### Why this matters for tagged-representation
The O(n²) `List` cons is a concrete, measurable motivation for the tagged
representation: a representation with O(1) cons (proper cons-cells or a tagged list)
would turn the ~30 min `css:examples` render into sub-second. When the tagged
representation lands, re-run the representation-conformance checks: both
`runtime/agda-values.js` and every `{-# COMPILE JS #-}` pragma assume today's
encodings (Bool→native, ℕ→BigInt, List→array, Maybe/record/pair→Scott) and will need
to move with it.
