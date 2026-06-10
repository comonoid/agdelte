# JS backend: `with`-scrutinees are compiled as non-memoised thunks and
# re-evaluated per clause → exponential blow-up

**Agda versions:** reproduces in **2.8.0** (nix `pkgs.agda`) and **2.9.0** (built
from source). The generated `f`-body is **byte-identical** between the two — so this
is *not* a 2.9 regression but a long-standing JS-backend behaviour (at least since
2.8.0).
**Backend:** JavaScript (`--js`, observed with and without `--js-es6` / `--js-optimize`)
**Severity:** performance correctness — a function that is linear in the source
becomes `O(2ⁿ)` in the generated JS.

## Summary

The JS backend compiles a `with`-abstraction so that the **with-scrutinee is a
non-memoised thunk** (`() => scrutinee`), and the compiled clause tree **forces that
thunk more than once** — once to select the clause, and again where the
with-bound variable is used in the chosen clause body. When the scrutinee is a
**recursive call**, this turns `T(n)` into `T(n) = 2·T(n-1) + O(1) = O(2ⁿ)`.

This contradicts the backend's intended strict semantics (which is sound for Agda
by strong normalisation): a strict compilation would evaluate the scrutinee **once**
and the function would run in `O(n)`.

## Minimal reproduction (only `Agda.Builtin`)

```agda
module WithExp where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

f : Nat → String
f zero    = "x"
f (suc n) with f n           -- scrutinee is the recursive call
... | ""  = "x"
... | s   = primStringAppend s "y"
```

```
agda --js WithExp.agda
```

`f` is obviously linear in `n` (it just walks `n` down to `0`). The generated JS
runs in `O(2ⁿ)`.

## Generated code (the bug is visible)

`_build/jAgda.WithExp.mjs`, function `f`:

```js
exports["f"] = a => (a === 0n) ? "x" : (
    (c => (d => ("" === c()) ? "x" : d())(          // (1) force c() to choose the clause
          () => primStringAppend(c())("y"))          // (2) force c() AGAIN in the body
    )(() => exports["f"](n))                          // c = () => f n   ← THUNK, not a value
);
// (n is itself a thunk () => a - 1n)
```

`c` is bound to the thunk `() => f n`, **not** to the evaluated value of `f n`. The
clause tree forces `c()` at point (1) to test the first clause (`| ""`), then forces
`c()` again at point (2) inside `primStringAppend (c()) "y"`. So `f n` is evaluated
twice per call. Recursively: `O(2ⁿ)`.

### Version coverage (not a 2.9 regression)

The identical thunk pattern is emitted by **both** Agda 2.8.0 and 2.9.0:

```sh
agda --no-libraries --js --compile-dir=out28 WithExp.agda   # 2.8.0
agda --js --compile-dir=out29 WithExp.agda                   # 2.9.0
diff <(grep -A10 '"f"' out28/jAgda.WithExp.js) \
     <(grep -A10 '"f"' out29/jAgda.WithExp.js)               # → no differences
```

The `f`-body is byte-identical, so this is a stable property of the JS backend, not
something introduced in 2.9.

(The recursive *argument* `a - 1n` is likewise a thunk `() => …`; the aux function
that `with` desugars to is being applied by-name, not strictly.)

## Measured (Agda 2.9.0, Node v22)

| `n` | `f(n)` runtime | ratio per +2 |
|----:|---------------:|-------------:|
| 18  | 88.7 ms        | –            |
| 20  | 296.6 ms       | ×3.35        |
| 22  | 1 131 ms       | ×3.81        |
| 24  | 4 516 ms       | ×3.99        |
| 26  | 17 949 ms      | ×3.97        |
| 28  | 73 510 ms      | ×4.10        |

≈ ×4 per `+2` ⇒ `O(2ⁿ)`. `f(28)` takes **73 s** for 28 steps of work.

## Expected behaviour

`with f x` desugars to an auxiliary function applied to `f x`; under strict
evaluation (sound here by strong normalisation, and what the JS backend otherwise
assumes) `f x` is evaluated **once** and passed as a value. Modelling both
compilations of the same recursion in plain JS:

```
            same input n
  n   "by-name" (current)   "strict / shared"
  18    14.7 ms              0.062 ms
  20    32.6 ms              0.003 ms
  22   114.8 ms              0.003 ms
  24   421.7 ms              0.003 ms
  26  1623.1 ms              0.004 ms        (strict: n=5000 → 0.45 ms)
```

The strict/shared compilation is `O(n)` (microseconds); the current one is `O(2ⁿ)`.

## Suggested fix

Compile a `with`-scrutinee (and, generally, the argument(s) of the desugared
`with`-auxiliary function) by **evaluating it once into a strict binding**, then let
the clause tree read that binding:

```js
// instead of:
(c => <clause-tree using c() … c()>)(() => scrutinee)
// emit:
const c = scrutinee;            // evaluate once (strict)
<clause-tree using c … c>
```

This matches the backend's strict semantics and the operational meaning of `with`
(the scrutinee is an argument of the aux function, evaluated by the caller). It is a
local change to the code generator for `with` / multi-scrutinee `case`, and fixes the
whole class: any `with`/shared binding over an expensive or recursive expression that
is used in more than one branch.

## Real-world impact

This is not a contrived case. A declarative, type-checked CSS layer (CSS as Agda
data, rendered by a `renderStylesheet : List Rule → String`) uses exactly this
pattern:

```agda
renderStylesheet (r ∷ rs) with renderRule r | renderStylesheet rs
... | "" | rest = rest
... | s  | ""   = s ++ "\n"
... | s  | rest = s ++ "\n\n" ++ rest
```

`renderStylesheet rs` (the recursive scrutinee) is forced twice per rule ⇒ `O(2ⁿ)`.
Rendering a real ~320-rule stylesheet did **not finish in ~5 hours at 100 % CPU**
(growing to ~0.8 GB RSS), whereas every individual rule renders in well under a
millisecond (sum of all 322 ≈ 7 ms). With the strict/shared compilation it would be
a few milliseconds.

## Repro files

- `WithExp.agda` above (8 lines).
- Build: `agda --js WithExp.agda`; inspect `_build/jAgda.WithExp.mjs` function `f`;
  time `f(BigInt(28))` from the emitted module.
