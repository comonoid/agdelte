# Code Analysis & Recommendations

Remaining issues that require design decisions.
Each item includes context, options, and recommendation.

---

## 9. `SessionDual.agda` — get and put share no state

**File:** `examples/SessionDual.agda:59-74`

**Problem:** `kvServer` uses `mkOffer getAgent putAgent`, which under the hood calls
`_&_` from Wiring. This creates state type `KVState × KVState` — two independent
copies. `putAgent` writes to its copy, `getAgent` reads from its own. The KV store
demo can never retrieve a value that was previously stored.

**Decision:** How should `offer`-composed agents share state?

- **A. Single state with projections.** Change `mkOffer` to accept a single state type
  and two `AgentLens`es into it. `kvServer` would have state `KVState` (one copy), with
  get and put both operating on it. Breaks `mkOffer` API: instead of two independent
  agents it now requires a shared-state agent factory.

- **B. Fix only the example.** Keep `mkOffer` as-is (independent state is fine for
  the general case). Rewrite `kvServer` to use a single custom agent that handles
  `offer` input/output directly, without `mkOffer`. The example becomes more verbose
  but accurate.

- **C. Add `mkOfferShared` as a variant.** Keep existing `mkOffer` for independent
  agents, add `mkOfferShared : ... → S → (S → ...) → (S → ...) → SessionAgent ...`
  that takes one shared state.

**My take:** B. This is an example file. The general `mkOffer`/`_&_` combinator is
correct — independent state is the right default for external choice (each branch is
a separate service). The KV store example should just be rewritten to use a single
agent with manual case-split on `inj₁`/`inj₂`.

---

## 17. `Json.agda` — `encodeNat`/`encodeInt` precision loss

**File:** `src/Agdelte/Json.agda:412-413`

**Problem:** `{ encode: (n) => Number(n) }` converts Agda's BigInt-backed `ℕ`/`ℤ`
to JS `Number`, silently losing precision beyond 2^53. E.g. `encodeNat 9007199254740993`
encodes as `9007199254740992`.

**Decision:** What to encode large numbers as?

- **A. String for all.** `n.toString()` — preserves precision, but JSON consumers get
  `"123"` instead of `123`. Breaking change.

- **B. Number with overflow check.** `Number(n) if n <= 2^53, else throw` — fails loudly.
  Correct but harsh.

- **C. Conditional: number or string.** `Number(n)` when safe, `n.toString()` when large.
  JSON output type becomes inconsistent (sometimes number, sometimes string).

- **D. Leave as is.** Agda's `ℕ` is rarely used with values > 2^53 in browser contexts.
  Document the limitation.

**My take:** D. This is a real limitation but affects almost no practical use case in
a browser UI framework. The fix (any variant) would either break JSON consumers or add
complexity. Better to document it and fix only when someone actually hits it.

---

## 18. `Browser.agda` — impure functions declared as pure

**File:** `src/Agdelte/FFI/Browser.agda`

**Problem:** `consoleLog : String → ⊤`, `querySelector : String → Maybe Element`,
`setTimeout : ℕ → (⊤ → ⊤) → TimerHandle`, etc. are postulated as pure functions.
Agda's type system says the compiler can CSE, reorder, or eliminate calls. The JS
backend currently doesn't optimize, so it works in practice.

**Decision:** Make them `IO` or leave as is?

- **A. Wrap in IO.** `consoleLog : String → IO ⊤`, etc. Semantically correct. But
  these are documented as "low-level, use Event/Cmd instead" — actual apps use the
  AST-based API. Adding IO changes the types for every call site and requires
  importing IO infrastructure in a browser-only module.

- **B. Leave as is with documentation.** The JS backend doesn't optimize. These are
  escape-hatch primitives, not the primary API. Add a comment explaining the trade-off.

- **C. Remove the module.** If everything should go through Event/Cmd AST, these
  postulates are unnecessary. But they serve as documentation of what the runtime
  can do.

**My take:** B. These are explicitly documented as low-level escape hatches. The
primary API (Event/Cmd AST) is already pure and safe. Making these IO would add
complexity for no practical benefit — the JS backend doesn't optimize pure
postulates away, and no one should be using these directly anyway.

---

## 20. Pervasive `{-# TERMINATING #-}` and `{-# NO_UNIVERSE_CHECK #-}`

**Files:** `Event.agda`, `Node.agda`, `CoSession.agda`, `Session.agda`, `Obligation.agda`

**Problem:**
- `TERMINATING` on `mapE`, `filterE`, `zoomNode'` — these operate on coinductive
  `Event` streams. Agda's termination checker can't see they're productive.
- `NO_UNIVERSE_CHECK` on `Session` (Set₁ → Set₁), `CoSession`, `Obligation` — these
  use `Set` as a field/argument in ways that violate universe stratification.

**Decision:** Accept as technical debt or restructure?

- **A. Accept and document.** These are fundamental to the framework's design. `Event`
  is coinductive and must be mapped over; `Session` stores types as data. Both patterns
  require pragmas in Agda. No realistic alternative without completely different
  encoding.

- **B. Use sized types for TERMINATING.** Agda's `Size` system can sometimes prove
  productivity. But sized types in Agda are fragile and partially deprecated.

- **C. Universe-polymorphic Session.** `Session : Set (suc ℓ)` — technically possible
  but infects every module that uses Session with level arguments, adding significant
  boilerplate.

**My take:** A. These pragmas are the standard way to handle coinductive streams and
universe-polymorphic data in Agda. Sized types are not reliably supported. This is
known Agda technical debt, not a framework bug.

---

## 23. `ProcessOpticLinear.agda` — linearity not enforced

**File:** `src/Agdelte/Concurrent/ProcessOpticLinear.agda`

**Problem:** `IpcHandleL` is indexed by `ConnState` (`Connected`/`Disconnected`),
preventing `query` on a closed handle. But `close` returns `IO ⊤` instead of
`IO (IpcHandleL Disconnected)`, so there's no proof that the protocol completed.
Also nothing prevents using a `Connected` handle twice (Agda has no linear types).

**Decision:** How much protocol safety to enforce?

- **A. Return phantom proof from close.** `close : IpcHandleL Connected → IO (IpcHandleL Disconnected)`.
  Doesn't prevent aliasing (using the Connected handle after close), but at least the
  caller must acknowledge the transition.

- **B. Leave as is.** The `Obligation` module (`withIpc`) already provides the scoping
  guarantee: the handle only exists inside the callback, ensuring it's closed. The
  indexed type prevents misuse (query after close). This is defense in depth, not
  a single mechanism.

- **C. CPS-only API.** Remove the raw `connect`/`close` exports, expose only
  `withIpc`. Then linearity is enforced by scoping, not types.

**My take:** A is trivial (change return type of `close`), but the real safety comes
from `withIpc` in Obligation.agda. I'd do A (one-line change) and leave the rest.
True linear types can't be expressed in Agda.

---

## 24. `Optic.agda` — `fromTraversal` loses data

**File:** `src/Agdelte/Reactive/Optic.agda:143-149`

**Problem:** `fromTraversal` converts a `Traversal S A` (which targets multiple `A`
values inside `S`) into an `Optic S A`. But `Optic.peek` returns `Maybe A` (one
value), so `fromTraversal` takes only the first element via `head`. A traversal
over a 5-element list silently becomes an optic into the first element only.
`over` still modifies all elements correctly — it's only `peek` that loses data.

**Decision:** How should multi-target traversals work with single-target Optic?

- **A. Don't provide `fromTraversal`.** Remove it. Traversals and Optics are
  different abstractions; don't pretend one is the other. Users must use
  `Traversal.toList` explicitly.

- **B. Add `peekAll : Optic S A → S → List A`.** Keep `fromTraversal` but add
  a way to peek all targets. The existing `peek` remains as "peek first".

- **C. Document the limitation.** Add a comment: "`peek` on a traversal-derived
  optic returns only the first target." Leave the code as is.

**My take:** C. The `over` works correctly on all targets. The `peek` taking the
first element is a reasonable default. The code is used in `OpticDynamic.agda`
where `fromTraversal allItemsTraversal` is only used with `over` (ResetAll), never
with `peek`. So the limitation doesn't manifest in practice.

---

## 25. `SharedAgent.agda` — names are misleading

**File:** `src/Agdelte/Concurrent/SharedAgent.agda`

**Problem:** `SharedAgent` and `LinearAgent` are both `record { {S} : Set ; agent : Agent S I O }` — structurally identical to `SomeAgent`. The names imply runtime
guarantees (shared mutable state, one-shot consumption) that don't exist.
`stepShared` returns a *new* `SharedAgent` (purely functional update), not a
mutation visible to other clients. `useLinear` doesn't enforce that the agent is
never used again.

**Decision:** Rename or add semantics?

- **A. Rename to match what they do.** `SharedAgent` → `PackedAgent` or
  `WrappedAgent`. `LinearAgent` → `OneShotAgent` (documentation-level intent, not
  enforced). Drop the linear-logic framing from the module comment.

- **B. Add actual semantics.** For `SharedAgent`: store state in `IORef`, make
  `stepShared` do `modifyIORef`. For `LinearAgent`: use a `once : Bool` flag.
  Major rework, mixes IO into a currently pure module.

- **C. Leave as is.** The types are honest (record with an agent inside). The names
  are aspirational, from research context (module header says "Research §3"). Users
  of the module (SharedAgentDemo) understand the pure semantics.

**My take:** C. The module header clearly says "Research §3: ! (Bang)." These are
research prototypes exploring the concept. The demo works correctly with pure
semantics. Renaming doesn't add value; adding IORef changes the module's purpose.

---

## 27. `Obligation.agda` — `run` doesn't use bracket/finally

**File:** `src/Agdelte/Concurrent/Obligation.agda:50-54`

**Problem:** `run (withIpcS path f)` does `connect >>= f >>= close`. If `f` throws
an IO exception (Haskell `throwIO`), `close` is never called. The resource leaks.

**Decision:** Add exception safety or document the limitation?

- **A. Add `bracket` FFI.** Postulate `bracket : IO A → (A → IO ⊤) → (A → IO B) → IO B`
  in Server.agda, compiled to Haskell's `Control.Exception.bracket`. Use it in `run`:
  `bracket (connect path) close (λ h → run (f h))`. Solves the problem properly.

- **B. Use `finally`.** Simpler: `postulate finally : IO A → IO ⊤ → IO A`. Then
  `run (f h) `finally` close h`. Same effect, simpler type.

- **C. Document.** The module is research code, not production server infrastructure.
  IO exceptions in Agda's Haskell backend are edge cases. Add a comment.

**My take:** A. `bracket` is the standard Haskell solution, it's one postulate and one
COMPILE pragma. The `run` function already does `connect → use → close`, so `bracket`
is exactly the right pattern. Minimal change, maximum correctness.

---

## 28. Server modules — TOCTOU race on IORef

**Files:** `server/HttpAgent.agda:40-51`, `server/MultiAgent.agda:56-65`

**Problem:** Both do `readIORef ref >>= λ agent → ... writeIORef ref agent'`.
Two concurrent HTTP requests can both read the same state, step independently,
and the second write silently overwrites the first's result.

**Decision:** How to make agent state updates atomic?

- **A. `atomicModifyIORef`.** Postulate `atomicModifyIORef : IORef A → (A → A × B) → IO B`
  in Server.agda. The step becomes a single atomic read-modify-write. Standard Haskell
  solution.

- **B. Use MVar/TMVar.** Postulate a lock primitive. More complex, heavier.

- **C. Document.** For single-user demos and development servers, races are unlikely.
  These are example servers, not production code.

**My take:** A. `atomicModifyIORef` is one postulate, one pragma, and a small refactor
of two call sites. It's the idiomatic Haskell solution and eliminates the race
completely. Worth doing even for demo code — races cause confusing bugs.

---

## 29. Remaining code duplication across controls

**Files:** `Accordion.agda`, `Breadcrumb.agda`

**Problem:**
- `Accordion.agda` has three nearly identical `renderItem` functions (for `accordion`,
  `accordionMulti`, `collapsible`). They differ only in the predicate that checks
  whether an item is open: `eqStr (selected m)` vs `isOpen id m` vs `isExpanded m`.
- `Breadcrumb.agda` has three `renderItem`/`renderItems` functions differing in item
  type (`String` vs `BreadcrumbItem` vs custom) and separator.

**Decision:** Deduplicate or leave?

- **A. Extract shared helper.** Pass the predicate/renderer as a parameter. For
  accordion: `renderItem : (String → M → Bool) → ...`. For breadcrumb:
  `renderItem : (item → Node M A) → (item → String) → ...`. Agda's where-block
  scoping makes this slightly awkward but doable.

- **B. Leave as is.** Three copies of ~15 lines each. The control APIs are stable,
  and the duplication is local (within one module). Extracting a helper adds
  indirection without reducing total code much.

**My take:** B. The duplication is contained within single modules, the functions
are stable, and Agda's lack of type classes makes generic helpers verbose. The
cure would be worse than the disease.

---

## 30. Name conflicts between Progress/Spinner/Skeleton

**Files:** `Controls.agda`, `Progress.agda`, `Spinner.agda`, `Skeleton.agda`

**Problem:** `spinner`, `spinnerWithText`, `skeletonText`, `skeletonCircle` etc.
are defined in multiple modules with different signatures. `Controls.agda`
re-exports them using `hiding`/`renaming` to avoid ambiguity, but adding a new
similarly-named export requires updating the hiding list.

**Decision:** Namespace strategy?

- **A. Prefix names.** `progressSpinner`, `skeletonText`, `progressBar`. Verbose but
  unambiguous. Breaking change to all call sites.

- **B. Leave as is.** The `Controls.agda` facade module already handles conflicts.
  Users who import individual modules pick what they need. This is a standard
  Agda pattern.

- **C. Qualified re-exports.** `Controls.agda` re-exports as `Spinner.spinner`,
  `Skeleton.skeletonText`. But Agda doesn't support qualified re-exports natively.

**My take:** B. The current `hiding`/`renaming` in Controls.agda works. This is how
Agda modules are designed to be used. The "maintenance hazard" is minor — it's one
line to update when adding a new export.

---

## 31. `TreeView.agda` — `nodeData` field never used in rendering

**File:** `src/Agdelte/Html/Controls/TreeView.agda`

**Problem:** `TreeNode A` has `nodeData : Maybe A`, but `simpleTree` and
`collapsibleTree` only pass `nodeId : String` to click handlers. The typed data
associated with each node is inaccessible from the UI.

**Decision:** API change for click handlers?

- **A. Extend handler to receive data.** `onNodeClick : String → Maybe A → Msg`.
  Breaking change but gives access to associated data. Both `simpleTree` and
  `collapsibleTree` pass `nodeData node` alongside `nodeId node`.

- **B. Remove `nodeData` field.** If it's not used, don't store it. Users who need
  data can maintain a separate `Map String A` and look up by `nodeId`. Simplifies
  `TreeNode`.

- **C. Leave as is.** The field exists for user-side lookups. Users can build
  `Map String A` from the tree and look up `nodeId` in their update function.
  The field is useful structurally even if not rendered.

**My take:** A. The `nodeData` field exists specifically to associate data with nodes.
Not passing it to the handler defeats the purpose. Changing the handler type from
`String → Msg` to `String → Maybe A → Msg` is a small breaking change with clear
benefit.

---

## 47. `PolySignal.agda` — round-trip proof missing

**File:** `src/Agdelte/Theory/PolySignal.agda:89-90`

**Problem:** Comment says "coalgToSignal (signalToCoalg s) ≡ s (requires bisimilarity)"
but no proof or even a formal statement exists. This is a theory module, so incomplete
proofs reduce its value.

**Decision:** Prove or remove claim?

- **A. Prove with bisimilarity.** Define bisimilarity on `Signal`, prove the round-trip.
  Requires coinductive proofs (Agda's `codata` or `record` with guardedness).

- **B. Remove the comment.** The isomorphism is clear from the definitions. No need
  for the comment if there's no proof.

**My take:** B. The isomorphism is structurally obvious — both `Signal` and `Coalg`
are `(head : A, tail : self)`. The comment adds nothing without a proof. Remove it.

---

## 48. `SessionDualProof.agda` — informal claim not proven

**File:** `src/Agdelte/Theory/SessionDualProof.agda:36-42`

**Problem:** Comment claims `SessionI (dual s) ≡ SessionO s` and vice versa, but
no proof is given. The comment says "hold definitionally by reduction."

**Decision:** Prove or leave?

- **A. Add proof.** `dualI : (s : Session) → SessionI (dual s) ≡ SessionO s`.
  By induction on `s`. Should be straightforward since it holds definitionally.

- **B. Leave as is.** "Hold definitionally" means Agda can verify it with `refl` in
  specific cases (and `SessionDual.agda` does: `_ : SessionO GetProto ≡ SessionI (dual GetProto); _ = refl`).
  A general proof by induction is nice but not necessary — the definitional equality
  already gives the guarantee.

**My take:** A, but it's low priority. The proof should be easy (induction on Session,
each case is `refl` or `cong`). It would make the theory module complete and honest.
But since the property holds definitionally, the lack of a general proof has zero
practical impact.
