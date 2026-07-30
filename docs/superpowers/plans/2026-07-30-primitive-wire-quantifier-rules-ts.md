# Primitive Wire-Quantifier Rules — TypeScript Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the monolithic relation sever/join with the primitive rule
set, the content compiler, derived identity substitution, and the rebuilt
interaction layer, per
`docs/superpowers/specs/2026-07-29-primitive-wire-quantifier-rules-design.md`.
TypeScript only — the spec's Lean strategy section is a separate later plan.

**Architecture:** The kernel gains small per-wire rules (generalized
sever/join in `wire-quantifier.ts`, plus new `wire-content.ts` and
`wire-args.ts`). An authoring-layer compiler
(`src/kernel/proof/compile-content.ts`) folds monolithic join/sever inputs
into primitive step lists by structural induction on the content diagram.
Theories and `examples/frege.json` migrate through the compiler *before* the
monolith is deleted, so replay equality against the monolith is the
acceptance test. The interaction layer is rebuilt around the two gesture
families with the keyboard/palette conformance fixes.

**Tech stack:** TypeScript, vitest (`npm test`), `npm run typecheck`,
Playwright (`npm run e2e`). Theories are emitted via `npm run emit:theories`.

## Global Constraints

- Every new primitive acts on **all** endpoints of the acted-on wire in one
  step. Per-end variants are unsound and must not exist.
- Content primitives require every endpoint of the acted-on wire to be an
  atom-head endpoint (`port.kind === 'head'`); merge alone tolerates any
  endpoint kind.
- Every rule takes `orientation: 'forward' | 'backward'`. Gates:
  sever-family positive-forward, join-family negative-forward, flipped by
  orientation (existing scheme). Equivalence rules have no polarity gate.
- No rule input encodes user selection order: inputs are wire ids, endpoint
  sets, port indices, region ids, or unordered pair sets.
- New step kinds are registered in `src/kernel/proof/step.ts`,
  `src/kernel/proof/json.ts`, and covered in
  `tests/kernel/rules/error-vocabulary.test.ts`.
- `npm test` and `npm run typecheck` green at every commit; frege and
  arithmetic replays stay green from their migration task onward.
- No `legacy`/compatibility code: the monolith and its input shapes are
  deleted, not wrapped.

---

### Task 1: Generalize wire sever/join (any signature + sever scope parameter)

**Files:**
- Modify: `src/kernel/rules/wire-quantifier.ts` (`applyIotaSever`,
  `applyIotaJoin`, `WireSeverInput`/`WireJoinInput` iota variants)
- Test: `tests/kernel/rules/wire-join.test.ts`,
  `tests/kernel/rules/wire-quantifier.test.ts`,
  `tests/kernel/rules/polarity-matrix.test.ts`

**Interfaces:**
- Produces: iota-variant inputs accept any sig; sever input gains
  `scope?: RegionId`. (Kind tags stay until Task 9 flattens them.)

**Semantics:**
- Sever: delete both `requireIota` calls. Fresh wire scope =
  `input.scope ?? selected.scope`. Validate `input.scope` is
  descendant-or-equal of `selected.scope` and every **moved** endpoint's
  node region is descendant-or-equal of `input.scope` (use
  `isAncestorOrEqual`). Gate: polarity of the fresh wire's scope
  (`input.scope ?? selected.scope`) — positive forward, negative backward.
- Join: delete `requireIota`; add explicit
  `sigEquals(a.sig, b.sig)` check with refusal
  `joining wires requires equal signatures; '<a>' has '<sig>' but '<b>' has '<sig>'`.
  Everything else (comparable scopes, inner-scope gate) unchanged.

- [ ] **Step 1: Failing tests** — rel-sig join merges two 1-ary wires'
  endpoint sets under a negative inner scope and refuses on sig mismatch;
  rel-sig sever partitions endpoints; scope-parameter sever: endpoints
  inside a cut sever onto a wire scoped at the cut, gate follows the cut's
  polarity (matrix rows), an endpoint outside the chosen scope refuses, a
  chosen scope not enclosed by the old scope refuses.
- [ ] **Step 2: Run — expect failures** (`npm test -- wire-join wire-quantifier polarity-matrix`)
- [ ] **Step 3: Implement** per semantics above.
- [ ] **Step 4: Full `npm test` + `npm run typecheck` green.**
- [ ] **Step 5: Commit** `feat: generalize wire sever/join to all signatures with sever scope parameter`

### Task 2: One-point extension of identity normalization Rule 2

**Files:**
- Modify: `src/kernel/diagram/canonical/identity.ts`
  (`normalizeOneIdentity` co-scoped loop; `collapseIdentity` gains a
  `survivor: WireId` parameter)
- Test: the existing identity-normalization suite (locate via
  `grep -rl normalizeIdentities tests/`); add cases there.

**Semantics:** For each identity node, let
`outer = incident.filter(w => wires[w].scope !== node.region)`. Collapse
when `outer.length <= 1` (was: `outer.length === 0`), with
`survivor = outer[0] ?? incident[0]` and all other incident wires absorbed
(their non-node endpoints re-attach to the survivor; absorbed wires and the
node are deleted; `redirectImage` maps absorbed → survivor). Two or more
outer wires still decline. Soundness: the one-point rule
`∃x@R(x = t ∧ Φx) ≡ Φt`, valid at any polarity.

- [ ] **Step 1: Failing tests** — (a) node at R attached to outer wire `b`
  and R-scoped wire `x` carrying an atom endpoint: normalizes to the atom
  endpoint on `b`, node and `x` gone, wire image maps `x → b`; (b) node
  attached to two outer wires persists; (c) all-co-scoped behavior
  unchanged (existing tests stay green as-is).
- [ ] **Step 2: Run — expect (a) to fail.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite green** (this validates no existing fixture
  contained a one-outer node whose collapse changes replay results; if one
  does, the fixture's expected form updates — the collapse is an
  equivalence).
- [ ] **Step 5: Commit** `feat: extend identity collapse to the one-outer-wire one-point rule`

**Findings (2026-07-30, first attempt) — RESEQUENCED, see below.** The
eager trigger is confirmed by ruling ("it should self-reduce; the identity
node should exist only in places where they actually change semantics") and
its unit tests were written and passed, but enabling it before the theory
migration broke 22 theory-replay tests. Observed mechanics, all preserved
as landed infrastructure:

- Theory scripts capture wire ids across steps; normalization renames
  invalidate them. Fixed permanently: `StepReceipt` gained `transport` — a
  total every-scope wire image (the old `interface` transport filters to
  root wires) — and `PrimitiveStepRecorder` now resolves recorded steps
  through accumulated transports (`mapStepIds` with a defaulting map view).
  A minted id invalidates any stale rename keyed by it (`freshId` recycles
  the names of deleted wires — this produced a real corrupted-resolution
  bug, caught by probe).
- Steps that degenerate after resolution because normalization already
  merged their wires (self-join; identity insertion below two distinct
  wires) are elided by the recorder — the diagram already satisfies them.
- The remaining breakage sits in shapes produced by the *monolithic*
  relation join's splices (specialization scaffolding, deiteration
  exactness against spliced schema instances). Tasks 7–9 rebuild exactly
  those constructions through the compiler, so repairing them against the
  monolith's output would be done twice. **Resequencing: the eager trigger
  and Task 3 land after Task 7**, in one script-fixing pass against the
  migrated theories. The unit tests for the trigger are recorded in this
  task and get re-applied then.

### Task 3: Delete retargets; identity substitution becomes the derivation

**Files:**
- Modify: `src/kernel/rules/iteration.ts` (delete `IdentityRetarget`,
  `retargetAttachments`, the `retargets` parameters),
  `src/kernel/proof/step.ts` (drop `retargets` from iteration/deiteration
  steps), `src/kernel/proof/json.ts`, `src/app/copy-planner.ts`,
  `src/app/interact/moves.ts` (the two `retargets: []` sites),
  `src/theories/arithmetic-comm-carrier.ts` (two retargeted sites,
  ~lines 1761 and 2609 → iterate + sever sequences)
- Test: `tests/kernel/rules/identity.test.ts` (retarget tests replaced by
  derivation tests), `tests/kernel/rules/iteration.test.ts`

**Interfaces:**
- Consumes: Task 1's sever scope parameter, Task 2's one-point collapse.
- Produces: `applyIteration(diagram, selection, targetRegion, reservation?)`
  and `applyDeiteration(...)` without retarget parameters.

**The derivation (also the shape of the migrated theory steps):** with
id(a,b) at r and endpoint P(a) at q ⊆ r: (1) iterate the identity node into
q; (2) sever wire `a` keeping everything except the P-endpoint and the
copied node's a-port, with `scope: q`. Eager one-point collapse lands the
endpoint on `b`.

- [ ] **Step 1: Failing tests** — the two-step derivation produces the
  canonical form of P(b) from P(a) in both orientations; iteration and
  deiteration signatures no longer accept retargets (type-level: the
  parameter is gone).
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement deletions + migrate the two theory sites.**
- [ ] **Step 4: Full suite green — arithmetic replay equality is the
  adequacy proof for the migration.**
- [ ] **Step 5: Commit** `refactor: replace iteration retargets with the sever-based substitution derivation`

### Task 4: Content primitives (cut-wrap/absorb, parallel split/fuse, ends delete/spawn)

**Files:**
- Create: `src/kernel/rules/wire-content.ts`
- Modify: `src/kernel/rules/index.ts`, `src/kernel/proof/step.ts`,
  `src/kernel/proof/json.ts`
- Test: `tests/kernel/rules/wire-content.test.ts`,
  `tests/kernel/rules/error-vocabulary.test.ts`,
  `tests/kernel/rules/polarity-matrix.test.ts` (endsDelete/endsSpawn rows)

**Interfaces (all return `Diagram`; `reservation?: IdReservation`):**
- `applyCutWrap(d, wire: WireId, reservation?)` — equivalence. Every
  endpoint must be an atom head. One fresh wire W′ (same sig, same scope).
  Per end (atom n at region q with args ā): fresh cut c with parent q,
  fresh atom in c with head→W′ and args→ā; delete n. Delete the old wire.
- `applyCutAbsorb(d, wire: WireId, reservation?)` — inverse. Every endpoint
  an atom head whose region is a cut containing exactly that atom and
  nothing else (no other nodes, subregions, or wires scoped there). Per
  end: fresh atom at the cut's parent (head→fresh W, args unchanged);
  delete cut + atom. Delete the old wire.
- `applyParallelSplit(d, wire: WireId, reservation?)` — equivalence. Two
  fresh wires, same sig and scope; each end becomes two side-by-side atoms
  in the same region with identical args.
- `applyParallelFuse(d, a: WireId, b: WireId, reservation?)` — inverse.
  `sigEquals(a.sig, b.sig)`; all endpoints of both are atom heads; the
  multiset of (region, args-tuple) of a's ends must equal b's exactly —
  pair them by that key (no order input); each pair becomes one atom on a
  fresh wire.
- `applyEndsDelete(d, wire: WireId, orientation)` — gated
  negative-forward on `wire`'s scope polarity (join family: W := ⊤).
  Every endpoint an atom head; delete all end atoms; the wire survives
  endpoint-free (vacuous elim is a separate step).
- `applyEndsSpawn(d, wire: WireId, sites: readonly { region: RegionId; args: readonly WireId[] }[], orientation, reservation?)`
  — gated positive-forward on `wire`'s scope polarity (sever family).
  Requires the wire currently endpoint-free; per site spawns an atom
  head→wire, args→the given wires (visibility + sig checked). `args: []`
  for 0-ary.
- Step kinds: `cutWrap`, `cutAbsorb`, `parallelSplit`, `parallelFuse`,
  `endsDelete`, `endsSpawn`.

- [ ] **Step 1: Failing tests** — per rule: happy path against a hand-built
  expected diagram via `exploreForm` equality; round-trips (wrap→absorb,
  split→fuse, delete→spawn each reproduce the original canonical form);
  refusals: non-applied endpoint (each content rule), absorb with extra cut
  content, fuse with mismatched arg multisets, spawn on a wire with
  endpoints, sig-mismatched fuse; polarity matrix rows for
  endsDelete/endsSpawn in both orientations.
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `feat: content primitives — cut wrap/absorb, parallel split/fuse, ends delete/spawn`

### Task 5: Argument primitives (arity shift, plumbing, apply-formal, identity leaf)

**Files:**
- Create: `src/kernel/rules/wire-args.ts`
- Modify: `src/kernel/rules/index.ts`, `src/kernel/proof/step.ts`,
  `src/kernel/proof/json.ts`
- Test: `tests/kernel/rules/wire-args.test.ts`,
  `tests/kernel/rules/error-vocabulary.test.ts`,
  `tests/kernel/rules/polarity-matrix.test.ts` (gated rows)

**Interfaces (every rule requires all endpoints of the acted-on wire to be atom heads; each replaces the wire with a fresh wire of the adjusted sig):**
- `applyArityShift(d, wire, newArgSig: Sig, reservation?)` — equivalence.
  New last argument position of sig `newArgSig`; per end at region q: fresh
  wire y (scope q, sig `newArgSig`) attached as the new argument.
- `applyArityUnshift(d, wire, position: number)` — inverse. At every end
  the argument at `position` attaches to a wire whose scope is the end's
  region and whose only endpoint is that attachment; drop the position and
  those wires.
- `applyArgPermute(d, wire, permutation: readonly number[])` — equivalence;
  permutes sig args and per-end attachments.
- `applyArgDuplicate(d, wire, position)` — equivalence; inserts a copy of
  `position` directly after it, attached to the same wire at every end.
- `applyArgContract(d, wire, position)` — inverse of duplicate; requires
  positions `position` and `position + 1` to attach to the same wire at
  every end; drops `position + 1`.
- `applyArgDrop(d, wire, position, orientation)` — gated negative-forward
  (join family); drops the position, per-end attached wires lose that
  endpoint.
- `applyArgExtend(d, wire, position, attachments: ReadonlyMap<NodeId, WireId>, newArgSig, orientation)`
  — gated positive-forward (sever family); inserts a position at `position`
  attached per end (keyed by end node id — an unordered map covering every
  end exactly once) to a visible wire of sig `newArgSig`.
- `applyApplyFormal(d, wire, position, orientation, reservation?)` — gated
  negative-forward. Requires the sig at `position` to equal
  `relSig(<the other argument sigs in order>)`. Per end: new atom of that
  sig with head→the wire attached at `position`, args→the remaining
  attachments in order; delete old atoms and the wire.
- `applyAbstractFormal(d, ends: readonly NodeId[], scope: RegionId, orientation, reservation?)`
  — inverse. `ends` are atom nodes of one shared sig σ (head wires may
  differ); fresh wire of sig `relSig([σ, ...σ.args])` at `scope` (must
  enclose every end and be enclosed by every head/arg wire's scope); each
  atom becomes an application of the fresh wire with its old head as first
  argument. Gate positive-forward on `scope`.
- `applyIdentityLeaf(d, wire, orientation)` — gated negative-forward.
  Requires all argument sigs equal; each end becomes an identity node
  (that sig, that arity) over its argument wires; delete atoms and wire.
- `applyIdentityAbstract(d, nodes: readonly NodeId[], scope: RegionId, orientation, reservation?)`
  — inverse; identity nodes of one sig and arity become ends of a fresh
  wire at `scope`. Gate positive-forward on `scope`.
- Step kinds: `arityShift`, `arityUnshift`, `argPermute`, `argDuplicate`,
  `argContract`, `argDrop`, `argExtend`, `applyFormal`, `abstractFormal`,
  `identityLeaf`, `identityAbstract`.

- [ ] **Step 1: Failing tests** — round-trips (shift→unshift,
  duplicate→contract, permute→inverse-permute, drop→extend,
  applyFormal→abstractFormal, identityLeaf→identityAbstract each restore
  the canonical form); refusals: unshift when a per-end wire has extra
  endpoints or wrong scope, contract on differing wires, applyFormal on a
  sig mismatch, extend map not covering every end; gate rows for the gated
  rules in both orientations.
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `feat: argument primitives — arity shift, plumbing, apply-formal, identity leaf`

### Task 6: The content compiler

**Files:**
- Create: `src/kernel/proof/compile-content.ts`
- Test: `tests/kernel/proof/compile-content.test.ts`

**Interfaces:**
- `compileRelationJoin(diagram: Diagram, wire: WireId, content: DiagramWithBoundary, parameters: readonly WireId[], definitions: ReadonlyMap<string, DiagramWithBoundary>, orientation): ProofStep[]`
- `compileRelationSever(diagram: Diagram, scope: RegionId, pattern: DiagramWithBoundary, occurrences: <the monolith's occurrence data shape>, orientation): ProofStep[]`
- Consumes every rule from Tasks 1, 4, 5 plus `vacuousIntro`/`vacuousElim`,
  `unfold`/`fold`.

**Algorithm (the spec's induction, on live-wire residuals):**
1. residual has an internal wire scoped at its root → `arityShift` (the
   shifted wire becomes a formal).
2. root has ≥2 items and no root-scoped internal wire → `parallelSplit`
   (both halves keep all formals).
3. root is a single cut → `cutWrap`.
4. empty residual → `endsDelete` + `vacuousElim`.
5. leaf node → plumbing (`argPermute`/`argDuplicate`/`argDrop`/`argExtend`
   with parameters as extend targets) then: fixed-wire end → `wireJoin`
   (merge); formal application → `applyFormal`; identity node →
   `identityLeaf`; ref node → recurse into the stored definition body, then
   `fold` each site.

Sever compiles as the join plan of the inverse instance, reversed, each
step replaced by its inverse partner with flipped orientation.

- [ ] **Step 1: Failing tests** — for every relation-kind fixture in
  `tests/kernel/rules/wire-quantifier.test.ts` and `wire-join.test.ts`:
  replaying the compiled step list produces an `exploreForm`-equal diagram
  to the monolith's output (the monolith still exists — this is the
  redundancy check); dedicated cases: content `∃y.(P(x,y) ∧ ¬Q(y))`
  (quantifier + shared formal), applied-formal content, identity-node
  content, ref-node content, empty content, parameter-using content;
  sever direction against the monolithic sever on the same fixtures.
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `feat: content compiler — monolithic join/sever as primitive step sequences`

### Task 7: Theory migration

**Files:**
- Modify (every `kind: 'relation'` sever/join construction → compiler
  splice): `src/theories/arithmetic-base.ts`, `arithmetic-naturals.ts`,
  `arithmetic-one.ts`, `arithmetic-right.ts`, `arithmetic-right-carrier.ts`,
  `arithmetic-shift.ts`, `arithmetic-shift-carrier.ts`,
  `arithmetic-assoc.ts`, `arithmetic-assoc-base.ts`,
  `arithmetic-assoc-carrier.ts`, `arithmetic-comm.ts`,
  `arithmetic-comm-carrier.ts`, `reification.ts` (34 sites total)

- [ ] **Step 1:** Swap each relation-kind step construction for the
  compiled sequence (`...compileRelationJoin(...)` spliced into the step
  list at the same point; the diagram passed is the replay state before
  that step — thread it with the existing per-script replay helpers).
- [ ] **Step 2: Full suite green** — frege and arithmetic replay equality
  is the acceptance test.
- [ ] **Step 3: Commit** `refactor: theories emit primitive steps via the content compiler`

### Task 8: Convert `examples/frege.json`

**Files:**
- Create (temporary): `scripts/convert-frege-primitives.ts`
- Modify: `examples/frege.json`

- [ ] **Step 1:** Script: load the proof, replay step by step; at each
  relation-kind `wireSever`/`wireJoin`, call the compiler against the
  current diagram and splice the primitive steps; serialize back. Run with
  `npx tsx scripts/convert-frege-primitives.ts`.
- [ ] **Step 2:** Frege replay tests green against the converted file; grep
  confirms zero `"kind":"relation"` entries remain.
- [ ] **Step 3:** Delete the conversion script (one-shot tool; the diff is
  its record) and commit `refactor: frege proof replays through primitive steps`.

### Task 9: Delete the monolith

**Files:**
- Modify: `src/kernel/rules/wire-quantifier.ts` (delete `ContentOccurrence`,
  `PreparedContent`, `PreparedOccurrence`, `RelationApplication`, the
  relation halves of `applyWireSever`/`applyWireJoin`, relation error
  members; flatten inputs to
  `WireSeverInput = { wire, keep, scope? }`,
  `WireJoinInput = { a, b }` — kind tags gone),
  `src/kernel/proof/step.ts`, `src/kernel/proof/json.ts`,
  `src/kernel/proof/compose.ts`, `src/kernel/rules/index.ts`,
  `src/app/edit.ts`, all theory files (mechanical `kind: 'iota'` input
  updates), `examples/frege.json` (mechanical tag-field rewrite by a jq
  one-liner recorded in the commit message)
- Test: `tests/kernel/rules/wire-quantifier.test.ts` (relation cases
  become compiler tests already ported in Task 6 — delete the monolith
  cases), `error-vocabulary.test.ts`

- [ ] **Step 1:** Delete + flatten; update every reference (`grep -rn
  "ContentOccurrence\|kind: 'relation'\|kind: 'iota'" src tests` must end
  empty).
- [ ] **Step 2: Full suite + typecheck green.**
- [ ] **Step 3: Commit** `refactor: delete monolithic relation sever/join`

### Task 10: Interaction — deletions and Family 1 (the drawing gesture)

**Files:**
- Modify: `src/app/interact/connection.ts` (delete the occurrence
  designation flow — `PreparedOccurrence`, `PendingRelationState`'s
  occurrence fields, `prepareSelectedOccurrences`,
  `RelationSelectionAuthority`; replace with typed-contact accumulation),
  `src/app/interact/moves.ts` (delete `relationJoin`/`relationSever`
  gesture cases), `src/app/actions.ts` (no change yet)
- Test: `tests/app/connection.test.ts` (rewrite)

**Dispatch (contact classification of accumulated contacts, dispatched at
loose-end drop; drop region = scope/region input):**

| Contact set | Committed step |
|---|---|
| region blank spots | `endsSpawn` on a fresh vacuous wire (`vacuousIntro` + `endsSpawn`, 0-ary) |
| atom-head ends of one wire | `wireSever` (keep = complement, scope = drop region) |
| atom ends of different wires | `abstractFormal` (scope = drop region) |
| identity nodes | `identityAbstract` (scope = drop region) |
| wire strands (≥2) | `identityInsert` at the drop region, wires in canonical structural order |
| none | `vacuousIntro` (arity prompt for sig) |

- [ ] **Step 1: Failing tests** — one per dispatch row (commit emits the
  right step; kernel refusal springs back); mixed contact types refuse
  with a named error; the identity-insertion row commits structurally
  identical diagrams for permuted contact orders (the canonical-order pin).
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `feat: drawing gesture — typed contacts dispatch the comprehension-direction primitives`

### Task 11: Interaction — Family 2 (object-typed drags)

**Files:**
- Create: `src/app/interact/wire-ops.ts` (drag controller: hit model for
  wire strands, atom end nodes, argument ports, cut boundaries; dispatch
  table; one-site-demonstration overlay previewing every end during the
  drag; spring-back refusal via the existing `refuse` sink)
- Modify: `src/app/interact/moves.ts` (mount the controller),
  `src/app/index.ts` (wiring)
- Test: `tests/app/wire-ops.test.ts`

**Dispatch (grab object → drop object → step):** strand→strand `wireJoin`;
end→co-located parallel end `parallelFuse`; end→blank beside itself
`parallelSplit`; end rim→blank `arityShift` (arity prompt for the new
sig); port→blank off the node `arityUnshift` if its side condition holds
else `argDrop`; port→past sibling port `argPermute` (adjacent
transposition); port→sibling port on the same wire `argContract`;
port→beside itself `argDuplicate`; port→its own end's center
`applyFormal`; end→one of its own argument ports `identityLeaf`;
strand→end of another wire `argExtend` (uniform target; per-site variant
accumulates (end, wire) contacts before one commit); lasso around one end
`cutWrap`; cut boundary→its enclosed end `cutAbsorb`; Delete on a wire
`endsDelete` (endpoint-free: `vacuousElim` — extends the existing
contextual-Delete precedence).

- [ ] **Step 1: Failing tests** — one per dispatch row: synthesized
  pointer sequences commit the expected step kind with the expected
  inputs; the unshift-else-drop choice is exercised both ways; refusal
  springs back leaving diagram and history unchanged.
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `feat: object-typed drags — instantiation-direction primitives`

### Task 12: Keyboard and palette conformance

**Files:**
- Modify: `src/app/interact/moves.ts` (W with empty selection →
  `doubleCutIntro` with an empty selection at the region under the
  pointer; delete the `i`/`I` identity branch; palette opens only on a
  still right-click), `src/app/actions.ts` (delete the `erase`,
  `doubleCutWrap`, `doubleCutElim`, `vacuousElim`, `identityInsert`,
  `iterate`, `deiterate` action descriptors — rows with dedicated
  gestures; `relUnfold`, `relFold`, `citeTheorem` remain)
- Test: `tests/app/moves.test.ts`,
  `tests/app/viewport-proof-moves.test.ts`

- [ ] **Step 1: Failing tests** — W over a region with nothing selected
  commits `doubleCutIntro` there (today it refuses "select something
  first"); W with a selection wraps it unchanged; plain click over a hit
  no longer opens the palette; right-click does; removed descriptors are
  absent from `applicableActions` output; `i` does nothing.
- [ ] **Step 2: Run — expect failures.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Full suite + typecheck green.**
- [ ] **Step 5: Commit** `fix: keyboard and palette conform to the approved interaction design`

### Task 13: Browser tests and final validation

**Files:**
- Create/modify: `e2e/` specs — one flow per Family 1 dispatch row and per
  Family 2 dispatch row (commit + spring-back), the identity uniqueness
  shape (equality drawn inside a cut the wires do not enter), the
  substitution derivation flow (iterate identity + sever endpoint), W
  empty-selection spawn, right-click-only palette.

- [ ] **Step 1:** Write and run the e2e specs (`npm run e2e`).
- [ ] **Step 2:** Full validation: `npm test`, `npm run test:all`,
  `npm run typecheck`, `npm run e2e`, `npm run formal:size`.
- [ ] **Step 3:** Commit `test: end-to-end coverage for primitive rule gestures`

## Self-review notes

- Spec coverage: kernel changes (Tasks 1, 4, 5, 9), compiler (6),
  migration (7, 8), identity substitution derived (2, 3), interaction
  deletions + families + conformance (10, 11, 12), testing (every task +
  13). Lean section deliberately excluded (separate plan). Out-of-scope
  items excluded.
- The monolith survives until Task 9 so Tasks 6–8 can test compiled output
  against it; nothing after Task 9 references it.
- Type names used across tasks: step kinds listed in Tasks 4–5 are the
  ones Tasks 6, 10, 11 dispatch.
