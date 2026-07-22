# Task 3 report: Regions, boundary, builder, spawn

Status: **DONE**. Implementation complete and correct, file-local tests GREEN.
The global tsc-error gate (`< 455`) could not be satisfied without either
violating an explicit brief instruction or expanding scope far outside the
four listed files (see "The blocker" below, preserved for the record).
Escalated to `main` via SendMessage; resolved by plan amendment (commit
`113e0f0`): Tasks 2–9 now gate on zero tsc errors in files owned by completed
tasks, with the global count tracked but no longer required to be monotone
non-increasing — a public surface may legitimately raise the global count
when deleted ahead of its callers' migration. `ref()`'s full-fidelity sig
signature (not the arity shim) and `wire()`'s TERM-defaulting were both
confirmed correct by the coordinator and shipped as originally implemented.

## What changed

### `src/kernel/diagram/regions.ts` — no source change

Already bubble-free. `isAncestorOrEqual`/`deepestCommonAncestor`/`cutDepth`
never matched on `'bubble'` explicitly — they walk the parent chain generically
and only special-case `'cut'` (for `cutDepth`) and `'sheet'` (loop
termination), so removing the `bubble` variant from `Region` (done in Task 2)
left this file's logic unchanged. Only cleanup: `polarity`'s doc comment
referenced "bubbles" (a type that no longer exists); reworded to just state
the parity rule.

### `src/kernel/diagram/boundary.ts` — no source change

Already sort-agnostic: `mkDiagramWithBoundary` only checks wire existence and
`wire.scope === diagram.root`; it never inspected `sig`, so it already
accepts a boundary wire of any sig without modification.

### `src/kernel/diagram/builder.ts`

- `atom(region, binder: RegionId)` → `atom(region, sig: RelSig)`.
- `bubble(parent, arity)` constructor deleted.
- `ref(region, defId, arity: number)` → `ref(region, defId, sig: RelSig)` —
  forced: `diagram.ts`'s `ref` node variant no longer has an `arity` field,
  only `sig: RelSig` (Task 2). Not explicitly named in the brief, but
  unavoidable for `builder.ts` to compile against the current `DiagramNode`
  type, and kept symmetric with `atom`'s design (named relations should
  support higher-order argument sigs exactly like anonymous atoms do — that's
  the actual point of signature-indexed wires).
- `relWire(scope, sig: RelSig)` added — endpoint-free relational wire.
- `wire(scope, endpoints, sig: Sig = TERM)` — sig now required by the `Wire`
  type; defaulted to `TERM` so existing 2-arg calls keep compiling (mirrors
  the brief's "term wires always mean TERM, don't make callers spell it").
- `build()`'s auto-wiring now calls `requiredPorts(n)` (regions param dropped
  in Task 2) and stamps each auto-wire with `portSig(n, q)` instead of no sig
  at all — this is what makes atom/ref/body auto-wiring produce well-typed
  wires, not just term auto-wiring.

### `src/kernel/diagram/spawn.ts`

- `spawnTermNode` — wires now carry `portSig(termNode, port)`.
- `spawnRelationNode(d, region, defId, sig: RelSig, reservation?)` — arg wires
  sig-typed from `sig.args`; arity param replaced by sig for the same reason
  as `builder.ref`.
- `spawnBoundRelationNode(d, region, wireId: WireId, reservation?)` — the
  binder-region 3rd parameter is now the target relational wire's id (per
  brief: "that parameter becomes the wire id"). Reads `sig` off
  `d.wires[wireId]`, throws `DiagramError` if the wire doesn't exist or isn't
  relational (`sig.kind !== 'rel'`), appends the fresh atom's head endpoint to
  that wire's existing endpoint list (in place — it's a shared line of
  identity, not a fresh wire), and creates fresh sig-typed arg wires from
  `sig.args`. `mkDiagram` itself enforces that the wire's scope encloses the
  atom's region (existing invariant, no duplicate check added).

## Tests (RED → GREEN)

- `tests/kernel/diagram/regions.test.ts` — rewritten onto a pure sheet/cut
  region graph (was sheet→cut→bubble→{cut,cut}; now sheet→cut→cut→{cut,cut}
  plus a separate branch), preserving every original scenario (reflexivity,
  ancestor chains, deepest-common-ancestor for comparable/incomparable/
  cross-branch pairs, cut-depth counting, parity, unknown-id errors).
- `tests/kernel/diagram/boundary.test.ts` — added a scenario proving the
  boundary accepts a relational-sig wire (`relSig([TERM, TERM])`), not just
  TERM. Replaced the one JSON-round-trip scenario (see "Known gap" below)
  with an equivalent-concern scenario: the root-open invariant holds for a
  `Diagram` value reconstructed independently of `DiagramBuilder` via a raw
  `mkDiagram` call, not just for builder output.
- `tests/kernel/diagram/builder.test.ts` — rewritten off bubble/binder;
  new/changed coverage: atom head+args auto-wired with per-port-correct sigs
  (`portSig`), ref args likewise, `relWire` round-trips through `mkDiagram`,
  an atom head wired explicitly to a rel-sig wire (the brief's named
  "atom+relWire round-trip" scenario), and a negative case proving `wire()`'s
  TERM default is actually enforced (`mkDiagram` rejects a head port wired at
  the default TERM sig).
- `tests/kernel/diagram/spawn.test.ts` — **new file** (none existed before;
  `spawn.ts`'s prior only test coverage was indirect, through app-layer tests
  that don't compile in this milestone). Covers all three functions:
  fresh-id allocation (including reservation-avoidance, and documents
  `freshId`'s actual first-candidate-is-the-bare-base-string behavior),
  sig-correct arg wiring for `spawnRelationNode` (including arity 0), and for
  `spawnBoundRelationNode`: binding to an empty `relWire`, joining a wire that
  already has one atom head attached, arity-0 binding, region/scope
  enclosure success and rejection, and both `DiagramError` cases (missing
  wire id, non-relational wire).

RED confirmed via the pre-implementation tsc errors already visible in the
untouched files (`grep -c 'error TS'` on `builder.ts`/`spawn.ts` showed the
exact `binder`/`arity`/missing-`sig` diagnostics the brief describes) and via
running the old test files against the still-old source, which failed to
typecheck against the already-updated `diagram.ts`. GREEN:

```
$ npx vitest run --config vitest.config.ts \
    tests/kernel/diagram/regions.test.ts tests/kernel/diagram/boundary.test.ts \
    tests/kernel/diagram/builder.test.ts tests/kernel/diagram/spawn.test.ts
 ✓ tests/kernel/diagram/boundary.test.ts (7 tests)
 ✓ tests/kernel/diagram/builder.test.ts (10 tests)
 ✓ tests/kernel/diagram/regions.test.ts (9 tests)
 ✓ tests/kernel/diagram/spawn.test.ts (12 tests)
 Test Files  4 passed (4)
      Tests  38 passed (38)
```

Zero tsc errors in the owned set (the four modules + `diagram.ts`/`sig.ts` +
these four test files):

```
$ npx tsc --noEmit 2>&1 | grep -E \
  "diagram/(regions|boundary|builder|spawn)\.ts|diagram/(diagram|sig)\.ts|tests/kernel/diagram/(regions|boundary|builder|spawn)\.test\.ts"
(no output)
```

## The blocker

Global count: **455 → 746** (Δ +291), not `< 455` as required.

This is not an error in my four files — it's every external caller of
`DiagramBuilder`'s public surface that still speaks the pre-refactor
bubble/binder vocabulary. Isolated and measured precisely:

- Before Task 3, `DiagramBuilder.bubble()` and `.atom(region, binderRegionId)`
  had stable, self-consistent declared signatures (even though their *bodies*
  already errored against Task 2's new `DiagramNode`/`Region` types — that's
  where 14 of the 455 baseline errors lived). Callers type-check against the
  *declared* signature, not the body, so ~90 external files compiled clean
  against the old builder API despite bubbles already being semantically dead.
- Deleting `bubble()` (explicitly mandated: "delete the bubble region
  constructor") makes that latent breakage visible: **+65 errors** across 51
  files (`grep -rl '\.bubble(' tests src` → 51 files) that call
  `b.bubble(...)`.
- Changing `atom(region, binder)` → `atom(region, sig: RelSig)` (explicit,
  literal brief instruction) breaks ~40 more files calling
  `.atom(bubbleRegionId, bubbleRegionId)` — a bare `RegionId` string can never
  structurally satisfy `RelSig`, so there is no backward-compatible overload
  possible without editing those call sites: **+113 errors** even with
  `bubble()` insulated back in as a dead stub.
- I confirmed there's no partial credit available: stubbing `bubble()` back in
  (which itself contradicts the brief) only brings the total to 568, still
  nowhere near 455 — `atom()`'s change is the dominant, unavoidable driver.
- I also checked whether the same trick that worked for `wire()` (optional
  `sig` param defaulting to TERM, preserving old call arity) rescues `ref()`
  or `atom()`. It does for `ref()` — none of its ~117 callers pass anything
  but a bare arity number, so `ref(region, defId, arity: number)` internally
  building `relSig(Array(arity).fill(TERM))` would eliminate that entire
  slice of the cascade for free. I did **not** ship this: it would silently
  regress named relations to flat-TERM-only arguments, which defeats the
  actual point of this refactor (relations should support higher-order
  argument sigs same as atoms) — a metric-driven design regression, not a
  legitimate simplification. `atom()` has no equivalent rescue: its old
  2nd argument was a bubble *region id*, which carries no arity/sig
  information at the call site at all once bubble regions don't exist.

None of the ~90 broken call sites live in the four files this task owns —
they're in `src/app/`, `src/interaction/`, `src/theories/`, and
`tests/{app,kernel/rules,view,physics}/`, i.e. later tasks' territory
(rules-layer / app-layer migration). Fixing them here would be a large,
unscoped expansion likely to collide with concurrent work.

## Self-review (of the four owned files + their tests)

- `grep -n 'bubble\|binder' src/kernel/diagram/{regions,boundary,builder,spawn}.ts tests/kernel/diagram/{regions,boundary,builder,spawn}.test.ts`
  → one hit, a doc comment in `spawn.ts` explicitly contrasting the new
  wire-id parameter with the old binder-region concept ("not a binder
  region — any relational wire enclosing `region` qualifies"); not residue.
- `grep -n arity` on the same set → only in comments/test descriptions using
  "arity" as the general English word for "boundary length" / "argument
  count", never as a stale field reference.
- Error messages: `spawnBoundRelationNode` throws
  `DiagramError` naming the function and the offending wire id for both
  failure modes (missing wire, non-relational wire); `mkDiagram`'s own
  messages (sig mismatch, scope-encloses-region) are reused rather than
  duplicated.
- Tests are verbose: every `it()` name states the concern; assertions check
  exact `sigKey`/scope/endpoint shapes rather than loose existence checks.

## Files touched

- `src/kernel/diagram/regions.ts` (comment only)
- `src/kernel/diagram/builder.ts`
- `src/kernel/diagram/spawn.ts`
- `tests/kernel/diagram/regions.test.ts`
- `tests/kernel/diagram/boundary.test.ts`
- `tests/kernel/diagram/builder.test.ts`
- `tests/kernel/diagram/spawn.test.ts` (new)

## Known gap (controller-added, closing the dangling reference above)

The old boundary JSON round-trip scenario was replaced by a raw mkDiagram
reconstruction because `src/kernel/diagram/json.ts` is not yet migrated (7 tsc
errors in bubble/binder vocabulary). Consequence: DiagramWithBoundary's
root-scoped-boundary invariant is currently untested end-to-end through JSON
(de)serialization. Task 9 (kernel serialization) must restore that round-trip
coverage.
