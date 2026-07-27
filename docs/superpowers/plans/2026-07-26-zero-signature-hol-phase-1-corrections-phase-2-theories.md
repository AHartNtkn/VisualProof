# Zero-Signature HOL Phase 1 Corrections + Phase 2 Theories Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for the 2026-07-26 correction barrier.

**Goal:** Complete the authorized Phase-1 corrections—including the
strongest-sound wire-quantifier pair—and only then rebuild the self-contained
relational Frege theory as Phase 2.

**Architecture:** A wire is a quantifier. At relation sorts, severing abstracts
exact drawn content to a fresh relation wire and `wireJoin` grounds a relation
wire to exact drawn content; at `iota`, the existing atomic wire forms remain
the strongest grammatical cases. Reification
`Exists P. forall x. P(x) <-> S(x)` is derived through that pair and reused by
ordinary theorem citation. No ref receives a polarity bypass, and the definition
store has no reification recognizer.

A `Theory` contains only interpreted `relations` and kernel-verified `theorems`.
Arithmetic primitives are universally quantified relation wires and their
properties are inline theorem hypotheses. There is no axiom store, import
system, macro layer, lambda/computation layer, comprehension, extensionality
rule, or primitive second-order-instantiation rule.

**Tech Stack:** TypeScript, Vitest, Playwright, existing exact matcher/splicer,
diagram/proof kernel, stable theory JSON.

## Global Constraints

- Tasks 4A–4E are a strict correction barrier: complete and validate all five
  before any further work on Task 5 or later.
- Phase-2 kernel changes are prohibited. Tasks 4A–4E are the complete authorized
  Phase-1 correction scope.
- Severing and `wireJoin` are one sort-aware quantifier rule pair, each stated at
  the strongest form sound in full models.
- At relation sorts, use only exact occurrence matching, ordered boundary pins,
  explicit ambient parameters, and the existing splicer. Relation `wireJoin`
  carries one self-contained `DiagramWithBoundary` as its grammatical `G`
  operand; do not add a macro, tactic, definition-store recognizer, or separate
  primitive-instantiation authority.
- At `iota`, preserve the existing atomic join/sever semantics and polarity
  matrix.
- Every ref obeys ordinary polarity. Delete the exact-reification spawn
  exception and its recognizer.
- Reification and `existsProp` are recorded theorems derived through corrected
  severing, never spawned through special definition authority.
- Identity ports remain semantically orderless in matching, canonicalization,
  labeling, serialization, and rendering.
- Follow TDD, explicit-path staging, and one focused-test-validated commit per
  task. Tasks 4B–4D are one compile migration barrier: Task 4B's sole durable
  step shapes intentionally invalidate the app and theorem consumers owned by
  Tasks 4C and 4D, so `tsc` is barrier-wide and must return green at Task 4D.
  Do not add a compatibility shape, cast, alias, or temporary authority to make
  an intermediate commit typecheck. Preserve all user scratch/stash material.
- Phase 3 Lean semantics and Phase 4 expressiveness remain out of scope.

---

### Task 1: Correct the authoritative specifications

**Files:**

- Modify: `docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md`
- Modify: `docs/superpowers/specs/2026-07-25-identity-node-design.md`

**Requirements:**

- Update both changelogs and every current normative passage.
- Replace claims that relation handles arise through comprehension with:
  `S' := Exists P. forall x. P(x) <-> S(x)`.
- State that extensionality is not grammatical, rather than describing it as an
  omitted axiom.
- Replace the umbrella specification's `Exists P. True` plus “constrain it equal”
  shorthand with the actual reification construction.
- Describe five surviving identity transformations. Former Rule 6 is ordinary
  logical inconsistency, not an identity rule, certificate, or oracle.
- Add `existsProp : Exists X : rel(). X` as the minimal higher-order substitution
  demonstration.
- Leave historical superseded plans unchanged.

**Validation:**

```bash
rg -n "comprehension|extensionality axiom|six identity|distinctness oracle|∃P.⊤" \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
```

Any remaining occurrence must explicitly describe rejected or historical material.

**Commit:**

```bash
git add -- \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
git commit -m "docs: define relation reification without extensionality"
```

### Task 2: Remove specialized identity-contradiction authority

**Files:**

- Modify: `src/kernel/rules/identity.ts`
- Modify: `src/kernel/rules/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `tests/kernel/rules/identity.test.ts`
- Modify: `tests/kernel/proof/step.test.ts`
- Modify: `tests/kernel/proof/json.test.ts`
- Modify: `tests/kernel/proof/compose.test.ts`
- Modify: `tests/app/actions.test.ts`

**RED:**

- Require absence of `IdentityContradictionEvidence`, its finder and application
  function, the `identityContradiction` proof step, codec, composer branch,
  application action, and interactive move.
- Require legacy JSON containing the rule to be rejected.
- Demonstrate equality plus cut-contained disequality using only ordinary cut,
  iteration/deiteration, identity, and structural rules.

**GREEN:**

- Delete the specialized authority across every listed layer.
- Do not replace it with a certificate, oracle, convenience rule, or hidden tactic.
- Record an ordinary closed contradiction theorem that replays through
  `checkTheorem` and is reused only through normal theorem citation.

**Validation:**

```bash
npx vitest run \
  tests/kernel/rules/identity.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/app/actions.test.ts
rg -n "identityContradiction|IdentityContradiction|distinctness.*(oracle|certificate)" src tests
npm run typecheck
```

**Commit:**

```bash
git add -- \
  src/kernel/rules/identity.ts src/kernel/rules/index.ts \
  src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts \
  src/app/actions.ts src/app/interact/moves.ts \
  tests/kernel/rules/identity.test.ts tests/kernel/proof/step.test.ts \
  tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts \
  tests/app/actions.test.ts
git commit -m "fix: dissolve identity contradiction into ordinary logic"
```

### Task 3: Build the non-macro reification foundation

> **Correction status:** The pure graph constructors and recorder from this task
> remain useful. Its former checked-definition spawn contract is superseded by
> Tasks 4A–4D. No later task may treat these diagrams as kernel-recognized spawn
> authority.

**Files:**

- Add focused modules under `src/theories/`.
- Add: `tests/theories/reification.test.ts`

**Public interface:**

```ts
export function buildFregeTheory(): Theory
export function natRelation(): DiagramWithBoundary
```

**RED:**

- Test deterministic graph construction and canonical JSON.
- Test reification at arities zero, one, and two.
- Require a fresh homogeneous `rel(sig...)` witness and the exact graph
  `forall x. P(x) <-> S(x)`.
- Establish the exact structural shape later recorded reification theorems reach
  by corrected severing. The kernel must not recognize this shape specially.
- Forbid comprehension, extensionality, term/body, beta-eta, or primitive
  instantiation steps and any exported composite proof API.

**GREEN:**

- Add pure constructors for implication, biconditional, quantifier scope, atoms,
  refs, and identities.
- Add a thin recorder accepting only a label and one ordinary `ProofStep`; it
  applies the step immediately and records the action.
- Add deterministic new-node/new-wire/new-cut lookup with cardinality checks.
- Handwrite explicit reified definitions for:
  - the empty sheet/Truth with `P : rel()`;
  - right-identity induction;
  - associativity induction;
  - successor-shift induction;
  - commutativity induction.
- The fresh `P` is a relation-typed boundary argument followed only by captured
  relation or individual wires needed by `S`.
- Treat these as explicit syntax fixtures and theorem endpoints, not relations
  with exceptional spawn permission.
- Do not add a macro, tactic, comprehension rule, automatic theorem synthesizer,
  or proof-step shortcut.

**Validation:**

```bash
npx vitest run tests/theories/reification.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories/reification.test.ts
git commit -m "feat: add explicit relation reification constructions"
```

### Task 4: Prove the minimal higher-order substitution theorem

This interim task landed before umbrella correction-log item 10.

Retain:

- forward-only erasure;
- forward-negative/backward-positive identity insertion;
- ordinary equality/disequality contradiction;
- the requirement that `existsProp : Exists X : rel(). X` be a replayable,
  closed theorem.

Displace in Tasks 4A–4D:

- `src/kernel/rules/reification.ts`;
- exact-reification recognition in the definition store;
- any-scope reification `refSpawn`;
- the ref/unfold/identity-retargeted derivation of `existsProp`.

Do not execute or preserve an interim authority merely because its committed
tests pass. Tasks 4A–4D are the complete current implementation contract.

## Phase-1 correction barrier — must precede all remaining theory work

### Task 4A: Synchronize both authoritative specifications

**Files:**

- Modify:
  `docs/superpowers/specs/2026-07-25-identity-node-design.md`
- Modify this plan only if implementation evidence requires a factual path or
  interface correction; do not change the selected semantics.

**Interfaces:**

- Consumes: umbrella-spec correction-log item 10 and its strongest-sound
  sever/join definitions.
- Produces: two mutually consistent authoritative specifications with no current
  definition-store reification-spawn authority.

- [ ] **Step 1: Write the documentation RED check**

Run:

```bash
rg -n \
  "spawn at every scope|spawnable at every scope|checked reification ref|definition store recognizes" \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
```

Expected: current normative matches in correction-log item 5 and the homogeneous
relation-handle passage.

- [ ] **Step 2: Replace the stale authority in the identity specification**

Add a correction-log item explicitly governed by umbrella correction-log item
10. Replace every current normative claim with:

```text
Relation handles remain wires of one homogeneous rel sort. A handle for content
G is derived by strongest-form severing as Exists P. forall x. P(x) <-> G(x).
No ref has special spawn authority; every ref obeys ordinary polarity.
```

Do not change identity orderlessness, normalization, insertion/erasure, or
substitution.

- [ ] **Step 3: Validate specification consistency**

Run:

```bash
rg -n \
  "spawn at every scope|spawnable at every scope|checked reification ref|definition store recognizes" \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
```

Expected: any remaining match occurs only inside explicitly superseded
correction-log history.

- [ ] **Step 4: Commit**

```bash
git add -- \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
git commit -m "docs: align identity handles with wire quantifiers"
```

### Task 4B: Rebuild severing and wireJoin as one sort-aware quantifier pair

**Files:**

- Create: `src/kernel/rules/wire-quantifier.ts`
- Delete: `src/kernel/rules/wire-join.ts`
- Modify: `src/kernel/rules/erasure.ts`
- Modify: `src/kernel/rules/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/kernel/proof/action.ts`
- Test: `tests/kernel/rules/wire-join.test.ts`
- Test: `tests/kernel/rules/erasure.test.ts`
- Add: `tests/kernel/rules/wire-quantifier.test.ts`
- Modify: `tests/kernel/proof/step.test.ts`
- Modify: `tests/kernel/proof/json.test.ts`
- Modify: `tests/kernel/proof/compose.test.ts`
- Modify: `tests/kernel/proof/action.test.ts`
- Modify: `tests/kernel/proof/theorem.test.ts`

**Interfaces:**

- Consumes:
  `SubgraphSelection`, `extractSubgraph`, `selectionContents`,
  `spliceSubgraphMapped`, `removeSubgraph`, `exploreForm`, `polarity`,
  `isAncestorOrEqual`, `relSig`, and `IdReservation`.
- Produces:

```ts
export type ContentOccurrence = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

export type WireSeverInput =
  | {
      readonly kind: 'iota'
      readonly wire: WireId
      readonly keep: readonly Endpoint[]
    }
  | {
      readonly kind: 'relation'
      readonly scope: RegionId
      readonly occurrences: readonly ContentOccurrence[]
    }

export type WireJoinInput =
  | {
      readonly kind: 'iota'
      readonly a: WireId
      readonly b: WireId
    }
  | {
      readonly kind: 'relation'
      readonly wire: WireId
      readonly content: DiagramWithBoundary
      readonly parameters: readonly WireId[]
    }

export function applyWireSever(
  diagram: Diagram,
  input: WireSeverInput,
  orientation?: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram

export function applyWireJoin(
  diagram: Diagram,
  input: WireJoinInput,
  orientation?: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram
```

The `iota` variants are the current atomic semantics, restricted to `IOTA`.
Relation-wire splitting/merging must use the `relation` variants; there is no
second relation authority.

The sole durable proof-step shapes are:

```ts
| { readonly rule: 'wireJoin'; readonly input: WireJoinInput }
| { readonly rule: 'wireSever'; readonly input: WireSeverInput }
```

JSON uses the same `input.kind` discriminant. The old top-level `a`/`b` and
`wire`/`keep` shapes are rejected rather than accepted as aliases.

- [ ] **Step 1: Write RED tests for strongest-form relation severing**

In `tests/kernel/rules/wire-quantifier.test.ts`, build explicit diagrams and
require:

```ts
applyWireSever(diagram, {
  kind: 'relation',
  scope: positive,
  occurrences: [
    { sel: firstCopy, args: [firstX] },
    { sel: secondCopy, args: [secondX] },
  ],
})
```

to replace two disjoint, pinned copies of a multi-node `G(x,param)`—including
copies at different cut parities—with atoms headed by one fresh
`Q : rel(iota)`, scoped at `positive`.

Add rejection cases for:

- no occurrences;
- duplicate or overlapping selected content;
- non-descendant occurrence regions;
- non-isomorphic pinned content;
- mismatched ordered argument signatures;
- different ambient parameter host wires;
- an ambient parameter whose scope does not enclose `scope`;
- selecting the prospective quantified content recursively;
- relation content passed to the `iota` variant.

- [ ] **Step 2: Run the sever RED tests**

Run:

```bash
npx vitest run tests/kernel/rules/wire-quantifier.test.ts
```

Expected: FAIL because `wire-quantifier.ts` and relation severing do not exist.

- [ ] **Step 3: Implement one extracted-content representation**

Inside `wire-quantifier.ts`, extract each occurrence and derive:

```ts
type PreparedContent = {
  readonly pattern: DiagramWithBoundary
  readonly formalAttachments: readonly WireId[]
  readonly ambientAttachments: readonly WireId[]
}
```

Build `pattern.boundary` in exactly this order:

```text
[...formal boundary pins in args order,
 ...ambient pins in deterministic host-wire-id order]
```

Repeated formal arguments repeat the same boundary stub. Compare copies with
`exploreForm` under that full ordered boundary. Require all ambient attachment
IDs to be identical across copies; signature equality alone is insufficient.

- [ ] **Step 4: Implement relation severing**

For a `relation` input:

1. require `scope` polarity positive forward / negative backward;
2. require a nonempty, pairwise-disjoint occurrence set;
3. prepare and compare every occurrence;
4. require every occurrence region to descend from `scope`;
5. require every ambient wire scope to enclose `scope`;
6. create one fresh `Q` with
   `relSig(first.args.map((wire) => diagram.wires[wire]!.sig))`;
7. remove all selected occurrences;
8. at each original occurrence region, insert one atom headed by `Q` with its
   ordered occurrence arguments.

An empty selection is valid content `True` when its region identifies a distinct
occurrence site; duplicate empty selections at one region are rejected.

- [ ] **Step 5: Write RED tests for strongest-form grounding join**

Require:

```ts
applyWireJoin(diagram, {
  kind: 'relation',
  wire: universallyScopedP,
  content: gWithBoundary,
  parameters: [ambientParameter],
})
```

to replace **every** atom headed by `P` with a fresh splice of the self-contained
multi-node `G`. The first `P.sig.args.length` positions of
`gWithBoundary.boundary` are the ordered formal arguments; its remaining
positions align with `parameters`. Cover multiple applications, repeated
formal boundary stubs, nested application regions, an empty-sheet `G`, and
identity normalization produced by a repeated boundary pin.

Add rejection cases for:

- wrong forward/backward polarity;
- an endpoint of `P` that is not an atom head;
- a headed atom whose signature or required argument ports disagree;
- too few boundary positions for the formal arity;
- a formal boundary-prefix signature mismatch;
- a parameter count/signature mismatch against the boundary suffix;
- `parameters` containing the dying wire;
- an ambient parameter whose scope does not enclose `P.scope`;
- an application outside `P.scope`;
- relation content passed to the `iota` variant.

- [ ] **Step 6: Run the join RED tests**

Run:

```bash
npx vitest run \
  tests/kernel/rules/wire-quantifier.test.ts \
  tests/kernel/rules/wire-join.test.ts
```

Expected: relation-grounding tests FAIL against the old two-wire merge.

- [ ] **Step 7: Implement relation grounding join**

For a `relation` input:

1. require the dying wire to have a `rel` signature and negative scope forward /
   positive scope backward;
2. validate the self-contained DWB and split its ordered boundary into a formal
   prefix of `wire.sig.args.length` and an ambient suffix;
3. require formal-prefix signatures to equal the relation signature's arguments,
   and require the suffix to align exactly with `parameters`;
4. reject `parameters` containing the dying wire;
5. require all dying-wire endpoints to be atom heads and collect each
   application's argument wires in port-index order;
6. require every parameter to enclose the dying wire's scope;
7. in deterministic atom-ID order, remove all application atoms and splice the
   DWB at each atom region with attachments
   `[...applicationArgs, ...parameters]`;
8. remove the emptied dying wire.

Use the existing splicer for repeated-boundary identity behavior and fresh IDs.
The DWB is the rule's explicit grammatical content operand. Do not implement a
second matcher, manual clone, selected-source requirement, definition lookup, or
special reification case.

- [ ] **Step 8: Restrict and preserve the iota cases**

Move the existing wire merge and endpoint split into the `iota` variants. Require
both selected wires to have `IOTA`; keep scope comparability, retained outer wire,
identity normalization, endpoint validation, and the existing polarity matrix.

- [ ] **Step 9: Migrate the durable proof surfaces**

Add exact JSON round trips for all four inputs:

```text
wireJoin/iota
wireJoin/relation
wireSever/iota
wireSever/relation
```

Require strict-key rejection of the displaced top-level shapes and malformed
content occurrences. Serialize the relation-join DWB with the authoritative DWB
codec. Extend ID-composition tests so host selections, formal args, endpoints,
scopes, dying wires, and relation-join parameter attachments all map exactly
once; the embedded DWB keeps its own namespace unchanged.

Receipt rules:

- iota join transports both source wire identities to the retained outer wire;
- relation join has no image for the eliminated relation wire and preserves every
  surviving application/parameter wire through splicer normalization;
- sever preserves old boundary identities but gives no source identity to its
  fresh relation wire.

Allocation capture includes every node, wire, and region minted by repeated
relation splices in deterministic application-ID order.

- [ ] **Step 10: Run focused rule and proof gates**

```bash
npx vitest run \
  tests/kernel/rules/wire-quantifier.test.ts \
  tests/kernel/rules/wire-join.test.ts \
  tests/kernel/rules/erasure.test.ts \
  tests/kernel/rules/polarity-matrix.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/action.test.ts \
  tests/kernel/proof/theorem.test.ts
npm run typecheck
```

Expected: the focused tests PASS. At this intermediate barrier point,
`npm run typecheck` must fail only on the displaced wire-step consumers owned
by Tasks 4C and 4D:

```text
src/app/interact/moves.ts
src/theories/logic.ts
```

Any kernel/proof/test type error is a Task 4B failure. Do not repair either
named consumer here and do not reintroduce the old step shape.

- [ ] **Step 11: Commit**

```bash
git add -- \
  src/kernel/rules/wire-quantifier.ts \
  src/kernel/rules/wire-join.ts \
  src/kernel/rules/erasure.ts \
  src/kernel/rules/index.ts \
  src/kernel/proof/step.ts src/kernel/proof/json.ts \
  src/kernel/proof/compose.ts src/kernel/proof/action.ts \
  tests/kernel/rules/wire-quantifier.test.ts \
  tests/kernel/rules/wire-join.test.ts \
  tests/kernel/rules/erasure.test.ts \
  tests/kernel/rules/polarity-matrix.test.ts \
  tests/kernel/proof/json.test.ts tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts tests/kernel/proof/action.test.ts \
  tests/kernel/proof/theorem.test.ts
git commit -m "fix: strengthen relation wire quantifiers"
```

### Task 4C: Migrate the durable proof and physical application surfaces

**Files:**

- Delete: `src/kernel/rules/reification.ts`
- Modify: `src/kernel/rules/spawn.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/hittest.ts`
- Modify: `src/app/interact/brush.ts`
- Modify: `src/app/interact/connection.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `tests/kernel/rules/spawn.test.ts`
- Modify: `tests/app/actions.test.ts`
- Modify: `tests/app/brush.test.ts`
- Modify: `tests/app/hittest.test.ts`
- Modify: `tests/app/connection.test.ts`
- Modify: `tests/app/moves.test.ts`
- Modify: `tests/app/viewport-proof-moves.test.ts`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`
- Modify: `tests/architecture/interaction-ownership.test.ts`

**Interfaces:**

- Consumes: `WireSeverInput`, `WireJoinInput`, and `ContentOccurrence` from
  Task 4B.
- Produces uniformly polarity-gated ref spawning and a zero-new-gesture
  interaction domain for Task 4B's durable relation steps.
- `InteractiveViewport`'s single ordered `Hit[]` owns transient designation.
  Region/node hits contribute extent; selected cut boundaries deterministically
  partition that extent into maximal structural occurrences; wire hits form each
  occurrence's ordered formal boundary by their relative position in that same
  array.
- `hittest.ts` owns stable physical node/region/wire and pending-wire hit
  identity. `connection.ts` projects prepared selections, owns the ephemeral
  pending relation wire, and translates explicit contacts into durable inputs.
  The kernel remains the sole semantic validator.

- [x] **Step 1: Write spawn-authority RED tests**

Change spawn tests to require every ref to use the ordinary matrix:

```text
forward: negative only
backward: positive only
```

Exact reification definitions, same-signature lookalikes, root, nested positive,
and nested negative scopes receive no exception. Add an architecture absence
check for `src/kernel/rules/reification.ts` and
`isExactReificationDefinition`.

- [x] **Step 2: Write physical-interaction RED tests**

Require the existing `IOTA` wire-to-wire drag to remain unchanged. Require
relation quantifiers to consume the existing ordered highlight sequence without
adding menus, pickers, selection modes, searches, or a new gesture:

- region/node highlights contribute extent;
- wire highlights define formals in their relative highlight order;
- region/node and wire highlights may be interleaved;
- unhighlighting and re-highlighting a wire moves it to the end;
- unhighlighted crossing wires are ambient parameters, including the nullary
  case;
- selected items in the same region always form one occurrence;
- a highlighted cut boundary joins extent across it, while an unhighlighted cut
  boundary splits occurrences;
- the parser produces maximal structural occurrences; contact timing never
  partitions or batches the selection;
- no double cut, membrane, crossing-tap ledger, or other diagram content
  records editor intent;
- an existing relation wire dropped onto a physically hit parsed occurrence
  emits relation `wireJoin` and consumes only that occurrence;
- dragging from a selected extent starts one fresh pending relation wire;
- dragging from the pending wire body onto another physically hit parsed
  occurrence appends it without rebuilding the selection;
- a repeated contact on the same occurrence refuses, and highlighted
  occurrences never contacted remain selected;
- relation `wireSever` commits only when the loose end lands in a region, whose
  identity supplies the scope.

Add RED coverage for exact interleaved projection, same-region merging,
unhighlighted-cut splitting, highlighted-boundary joining, global argument
order, stable selected-hit and pending-wire-part identities, selective
consumption, duplicate-contact refusal, pending-wire abort, kernel-refusal
spring-back, mismatched explicitly touched occurrences, and absence of the
displaced menu and membrane vocabulary.

- [x] **Step 3: Run RED**

```bash
npx vitest run \
  tests/kernel/rules/spawn.test.ts \
  tests/app/actions.test.ts \
  tests/app/hittest.test.ts \
  tests/app/connection.test.ts \
  tests/app/moves.test.ts \
  tests/architecture/kernel-vocabulary.test.ts \
  tests/architecture/interaction-ownership.test.ts
```

Expected for the selection correction: FAIL until `connection.ts` parses the
single ordered selection structurally, contacts consume exact parsed
occurrences, and `ProofMoveController` supplies its ordered selection to the
connection authority.

- [x] **Step 4: Remove the special ref authority**

Delete `src/kernel/rules/reification.ts`. Remove its import and exceptional
callback from `spawn.ts`; `applyRefSpawn` must call the ordinary polarity gate
with no definition-sensitive branch or diagnostic. Remove every recognizer test
fixture and replace it with ordinary polarity coverage.

- [x] **Step 5: Implement the physical relation-wire domain**

Add one projection from the ordered selection:

```ts
export type PreparedOccurrence = {
  readonly occurrence: ContentOccurrence
  readonly content: DiagramWithBoundary
  readonly parameters: readonly WireId[]
  readonly extentHits: readonly ExtentHit[]
  readonly selectedHits: readonly Hit[]
}

export function prepareSelectedOccurrences(
  diagram: Diagram,
  hits: readonly Hit[],
): readonly PreparedOccurrence[]
```

Filter region/node hits while preserving their identities. Partition them into
maximal structural components: items in the same region merge; selected cut
boundaries connect their inside and outside cells; unselected cut boundaries
split. Normalize each component to one exact `SubgraphSelection`; do not
prevalidate cross-component disjointness. Filter the one global wire-hit order onto every component
whose extracted boundary it crosses. Reorder each bounded diagram as
selected-formal stubs followed by every unselected attachment in deterministic
extracted order; the latter host wires are parameters. A selected wire that
crosses no parsed occurrence refuses. Do not maintain a second order, tap store,
contact batch, or alternate parser.

`ConnectionDragController` receives the proof surface's live `selection()` and
`setSelection()` callbacks only when relation gestures are enabled. A prepared
occurrence is a legal physical target only when the pointer's concrete
region/node hit identifies that parsed extent.

For grounding, commit the exact relation `wireJoin` input on existing
relation-wire drop and consume only the contacted occurrence after success;
other parsed occurrences remain highlighted.

For abstraction, retain a legal endpoint-free relational wire in ephemeral
connection state. Dragging from a selected extent records the first explicit
`ContentOccurrence`; later pending-wire-body drops record later prepared
occurrences. Store each physical contact by stable selected hit identity and
derive overlay geometry from the current engine. Each successful contact
selectively consumes its parsed occurrence, leaving every uncontacted component
in the same ordered selection. A second contact on one consumed occurrence
refuses from the pending contact ledger. The pending loose-end release supplies
the exact region scope and is the sole relation `wireSever` commit. Escape
deletes the pending wire. Kernel refusal must use the existing
refusal/spring-back path without changing the durable diagram.

Delete `PreparedMembrane`, membrane-crossing hit types/functions, membrane
previews, the per-membrane tap map, and every double-cut-dependent interaction
path.

- [x] **Step 6: Delete competing application paths**

Remove relation join/sever action descriptors, discovery, menu rows, picker
markers, and standalone checked constructors. Direct relation-wire-to-relation-
wire dragging still reaches the unchanged kernel `IOTA` gate and is refused.
Do not search for, offer, suggest, or automatically select occurrences. The
deterministic largest-pattern parser is the sole structural partition authority;
it does not prevalidate semantic matches.

- [x] **Step 7: Run focused proof/application gates**

```bash
npx vitest run \
  tests/kernel/rules/spawn.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/action.test.ts \
  tests/kernel/proof/theorem.test.ts \
  tests/app/actions.test.ts \
  tests/app/brush.test.ts \
  tests/app/hittest.test.ts \
  tests/app/connection.test.ts \
  tests/app/moves.test.ts \
  tests/app/viewport-proof-moves.test.ts \
  tests/architecture/kernel-vocabulary.test.ts \
  tests/architecture/interaction-ownership.test.ts
npm run typecheck
```

Expected: all focused tests and typecheck PASS, except that in-progress protected
Task 4D files may temporarily be the sole typecheck failures. No compatibility
shape is permitted for those theory consumers.

- [x] **Step 8: Audit absence and commit the interaction correction**

```bash
rg -n \
  "PreparedMembrane|prepareMembraneContent|membraneCrossing|PendingMembrane|crossing tap|relationJoinStep|relationSeverStep|wire-content-and-parameters|scope-and-occurrences" \
  src/app tests/app tests/architecture \
  docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md
git diff --check
git add -- \
  src/app/hittest.ts src/app/interact/connection.ts src/app/interact/moves.ts \
  tests/app/brush.test.ts tests/app/hittest.test.ts \
  tests/app/connection.test.ts tests/app/moves.test.ts \
  tests/app/viewport-proof-moves.test.ts \
  tests/architecture/interaction-ownership.test.ts \
  docs/superpowers/plans/2026-07-26-task-4c-gesture-correction-fix-round-1.md \
  docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md
git commit -m "fix: designate relation occurrences through selection"
```

Expected `rg`: no displaced programmatic input path or membrane authority.
Negative tests and the explicit deletion/audit instructions above may name
rejected behavior; no executable authority may retain it.

### Task 4D: Re-derive reification and existsProp through severing

**Files:**

- Modify: `src/theories/reification.ts`
- Modify: `src/theories/logic.ts`
- Modify: `src/theories/frege.ts`
- Modify: `tests/theories/reification.test.ts`
- Add: `tests/theories/wire-quantifier-reification.test.ts`

**Interfaces:**

- Consumes: corrected relation `wireSever`/`wireJoin` steps and ordinary theorem
  citation.
- Produces recorded theorems, not special stored definitions:

```ts
export function relationIdentityReification(): Theorem
export function truthReification(): Theorem
export function rightIdentityInductionReification(): Theorem
export function associativityInductionReification(): Theorem
export function successorShiftInductionReification(): Theorem
export function commutativityInductionReification(): Theorem
```

Each theorem LHS contains only its ordered ambient capture boundary; its RHS adds
the existential `P` and exact `forall x. P(x) <-> S(x)` figure. `P` is not a
theorem boundary wire.

- [ ] **Step 1: Write theorem RED tests**

Require:

- `forall P. exists Q. forall x. Q(x) <-> P(x)` as a closed recorded theorem;
- one multi-node closure theorem
  `forall R,S. exists Q. forall x. Q(x) <-> (R(x) and S(x))`, proving that the
  implementation is not limited to the old single-atom instance;
- truth reification from blank;
- each arithmetic carrier reification with exactly its capture boundary;
- no theorem action with `refSpawn`;
- every created witness comes from a relation `wireSever`;
- removing any one sever action breaks `checkTheorem`;
- JSON round-trip re-verifies.

- [ ] **Step 2: Run RED**

```bash
npx vitest run \
  tests/theories/reification.test.ts \
  tests/theories/wire-quantifier-reification.test.ts
```

Expected: FAIL because the existing objects are definitions and `existsProp`
uses exceptional `refSpawn`.

- [ ] **Step 3: Record the general reification construction**

For each explicit `G`:

1. introduce the required double-cut/implication structure;
2. insert one copy of `G` in a legal negative branch;
3. iterate it to produce the second exact copy without deconstructing `G`;
4. apply relation severing to one selected copy in each implication, using the
   same quantifier scope and ordered formal boundary;
5. eliminate/clean the construction to the exact
   `exists P. forall x. P(x) <-> G(x)` RHS.

For `G = True`, use distinct empty-content selections identified by their branch
regions. Do not add a special empty-sheet rule.

- [ ] **Step 4: Re-record existsProp**

Derive:

```text
existsProp : Exists X : rel(). X
```

from blank using the corrected-sever truth reification. The final atom must
descend from the sever-created witness. Remove the old ref spawn, unfold,
recognizer, and identity-retargeted provenance expectations that belonged to the
superseded route.

- [ ] **Step 5: Rebuild the logical dependency prefix**

Order:

```text
ordinaryEqualityContradiction
relationIdentityReification
truthReification
four arithmetic carrier reifications
existsProp
```

Definitions in `Theory.relations` remain ordinary named relations such as `nat`;
do not register reification figures merely to obtain spawn authority.

- [ ] **Step 6: Validate the complete correction barrier**

```bash
npx vitest run \
  tests/kernel/rules/wire-quantifier.test.ts \
  tests/kernel/rules/wire-join.test.ts \
  tests/kernel/rules/erasure.test.ts \
  tests/kernel/rules/spawn.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/theorem.test.ts \
  tests/app/actions.test.ts \
  tests/app/moves.test.ts \
  tests/theories/reification.test.ts \
  tests/theories/wire-quantifier-reification.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
npm run typecheck
git diff -- src/theories/statements.ts tests/theories/frege-statements.test.ts
```

Expected: all tests and typecheck PASS; final diff command empty. No arithmetic
statement or proof work is allowed in the correction commits.

- [ ] **Step 7: Commit**

```bash
git add -- \
  src/theories/reification.ts src/theories/logic.ts src/theories/frege.ts \
  tests/theories/reification.test.ts \
  tests/theories/wire-quantifier-reification.test.ts
git commit -m "feat: derive reification through severing"
```

### Task 4E: Permit ordinary citation of capture-only theorem sides

**Files:**

- Modify: `src/kernel/proof/theorem.ts`
- Modify: `tests/kernel/proof/theorem.test.ts`
- Add:
  `docs/superpowers/specs/2026-07-26-theorem-capture-citation-correction.md`

**Correction boundary:**

The reification theorems produced by Task 4D have only ordered ambient captures
on their left-hand sides. An endpoint-free boundary capture is not a touching
attachment of an empty selected occurrence. Ordinary theorem citation must
therefore build the candidate boundary from both existing authorities:

- selected content and its touching wires come from `sel`;
- every ordered theorem boundary position gets its host wire from `args`.

For an endpoint-bearing theorem boundary position, the argument must remain a
touching attachment. For an endpoint-free theorem boundary position, the
argument supplies an ambient candidate stub even when it is not a touching
attachment. Reuse candidate stubs by actual host-wire identity so the pinned
canonical comparison refuses both diagonalizing distinct theorem captures and
splitting a repeated theorem capture. The existing splice remains
authoritative for host existence, signatures, scope, and connection.

Do not change `TheoremApplication`, proof steps, proof JSON, logical rules,
wire-quantifier rules, applications, or theory proof construction.

**TDD and validation:**

- [x] Prove a capture-only left side can be cited at an empty selection and
  that its right-side content attaches to the supplied host captures.
- [x] Refuse missing, signature-swapped, out-of-scope, diagonalized, and split
  capture arguments.
- [x] Preserve existing incident-boundary, exact-occurrence, and polarity
  behavior.
- [x] Run:

```bash
npx vitest run \
  tests/kernel/proof/theorem.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/action.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/store.test.ts \
  tests/kernel/proof/endtoend.test.ts \
  --config vitest.config.ts
npm run typecheck
git diff --check
```

**Commit:**

```bash
git add -- \
  docs/superpowers/specs/2026-07-26-theorem-capture-citation-correction.md \
  docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md \
  src/kernel/proof/theorem.ts \
  tests/kernel/proof/theorem.test.ts
git commit -m "fix: cite theorems with ambient captures"
```

### Task 5: Define relational naturals and closed arithmetic statements

**Files:**

- Add relational Frege definition and statement modules under `src/theories/`.
- Add: `tests/theories/frege-statements.test.ts`

**Signatures:**

```text
zero : rel(iota)
succ : rel(iota, iota)
plus : rel(iota, iota, iota)
nat  : rel(rel(iota), rel(iota,iota), iota)
```

Only `nat` is an interpreted arithmetic definition. `zero`, `succ`, and `plus`
are theorem-local universally quantified relation wires.

Every arithmetic theorem independently contains these inline hypotheses:

1. `Exists z. Zero(z)`.
2. `Zero(z) and Zero(z') -> z = z'`.
3. `forall n. Exists s. Succ(n,s)`.
4. `Succ(n,s) and Succ(n,s') -> s = s'`.
5. `Zero(z) -> Plus(z,b,b)`.
6. `Plus(a,b,c) and Succ(a,a') and Succ(c,c') -> Plus(a',b,c')`.
7. `Plus(a,b,c) and Plus(a,b,c') -> c = c'`.

Do not add plus totality. Each theorem is the closed graph:

```text
forall zero,succ,plus. standing hypotheses -> theorem-specific conclusion
```

The hypotheses are duplicated inline, not hidden behind a ref or bundle.

**Statement requirements:**

- `plusLeftUnit`: unguarded.
- `plusRightUnit` and `succShiftS`: guarded by Nat of the first addend.
- `plusAssoc`: guarded by Nat of both its first and second addends.
- `plusComm`: guarded by Nat of both addends.
- `zeroIsNat`, `succNat`, `oneIsNat`: closed over the quantified primitives.
- Tests inspect scopes, signatures, shared wires, cuts, and boundaries rather than
  theorem names or source strings alone.

**Validation:**

```bash
npx vitest run tests/theories/frege-statements.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories/frege-statements.test.ts
git commit -m "feat: define closed relational arithmetic statements"
```

### Task 6: Record the eight historical arithmetic proofs

**Files:**

- Add proof modules under `src/theories/`.
- Add: `tests/theories/frege.test.ts`

**Required dependency order (minimum public subsequence):**

1. `plusLeftUnit`
2. `zeroIsNat`
3. `succNat`
4. `oneIsNat`
5. `plusRightUnit`
6. `plusAssoc`
7. `succShiftS`
8. `plusComm`

The logical/reification prefix precedes these eight. This is a minimum ordered
list, not an exact theorem inventory or suffix. Add ordinary recorded support
theorems before their consumers wherever a coherent intermediate carrier fact
materially improves or enables proof composition.

**Semantic obligations:**

- Each required theorem proves its exact closed statement from
  `buildArithmeticStatements()`.
- No particular proof method, action topology, carrier representation,
  primitive-rule inventory, or citation graph is part of the theorem contract.
- Factor nontrivial intermediate facts into explicit closed, recorded support
  theorems when they materially improve or enable proof composition. Support
  theorems are normal `Theory.theorems` entries, never private helpers, hidden
  proof authorities, refs, macros, or kernel rules. Do not create mechanical
  helpers for trivial finishing steps.
- Every proof must use only the surviving kernel rules. No ref spawn,
  definition-store recognizer, capture-connection workaround, macro, tactic, or
  primitive second-order-instantiation authority is permitted.

**Current implementation evidence (non-normative):**

- The checked implementation derives the unit, Nat closure, associativity,
  successor-shift, and commutativity results with unfold/fold, ordinary theorem
  citation, Nat induction, and corrected relation `wireJoin`.
- Five closed carrier support theorems provide the composition boundaries that
  the implemented proof replay requires. Their presence and causal use are
  evidence for this implementation, not restrictions on another kernel-valid
  proof of the same public statements.

**Tests:**

- `verifyTheory(buildFregeTheory())` succeeds.
- Every required arithmetic theorem and support theorem is closed over its
  primitive relations and carries its explicit hypotheses.
- Every action replays; citations target preceding theorems.
- The eight required historical names occur as an ordered subsequence; tests
  must not encode them as an exact suffix or prohibit additional support
  theorems.
- Tests must not require exact primitive-rule inventories, carrier-grounding
  counts, or a fixed citation topology.
- `plusComm` concludes the crossed `Plus(b,a,o)` atom.
- No deleted rule tag or lambda-era node kind occurs.
- Removing a genuinely used hypothesis from representative induction proofs
  makes verification fail.
- Removing a genuinely cited carrier support theorem or its citation from a
  representative induction consumer makes verification fail.

**Validation:**

```bash
npx vitest run \
  tests/theories/reification.test.ts \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories
git commit -m "feat: rebuild relational Frege arithmetic"
```

### Task 7: Restore deterministic whole-theory emission and loading

**Files:**

- Add: `scripts/emit-theories.ts`
- Add: `tests/scripts/emit-theories.test.ts`
- Modify: `package.json`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`
- Modify: `e2e/app.spec.ts`
- Generate: `examples/frege.json`

**Requirements:**

- Restore `emit:theories`, `preapp`, and `pree2e`.
- Emit only `frege.json`; never recreate `lambda.json`.
- Use the authoritative theory codec and newline-terminate deterministic output.
- Load the emitted file through the ordinary loader, re-verifying every theorem.
- Exercise `existsProp` as the higher-order substitution smoke and `plusComm` as
  the full arithmetic citation chain.
- Update the architecture list to permit only the new Frege source, tests, emitter,
  and `frege.json`; keep lambda, macro, comprehension, and `lambda.json` forbidden.

**Validation:**

```bash
npm run emit:theories
npx vitest run tests/scripts/emit-theories.test.ts tests/theories
npm run e2e
npm run typecheck
```

Run emission twice and require no second-run diff.

**Commit:**

```bash
git add -- \
  package.json scripts/emit-theories.ts tests/scripts/emit-theories.test.ts \
  examples/frege.json tests/architecture/kernel-vocabulary.test.ts \
  e2e src/theories tests/theories
git commit -m "feat: ship the verified relational Frege theory"
```

### Task 8: Run the displaced-model audit and full gates

Search executable code, tests, scripts, and generated JSON for:

- specialized identity-contradiction authority;
- exact-reification recognizers, definition-sensitive ref polarity, or
  spawn-anywhere permissions;
- relation-level atomic-only wire split/merge as an alternative to exact-content
  severing/grounding;
- term/body node kinds and lambda/parser/reducer/beta-eta machinery;
- fusion, fission, headstrip, beta-eta congruence, inconsistent-cut;
- comprehension and `relCongruenceJoin`;
- primitive second-order instantiation;
- axiom or import stores;
- macro/tactic theory APIs;
- extensionality as a relation-level proposition;
- `lambda.json`;
- `tests/kernel/rules/uniqueness-representability.test.ts`.

Historical superseded documents may retain historical references. Current specs
and executable artifacts may mention rejected names only in negative tests.

**Full gates:**

```bash
npm run typecheck
npm test
npm run emit:theories
git diff --exit-code -- examples/frege.json
npm run e2e
git status --short
```

Append the foundation record's `<conformance>` section with implemented ownership,
deleted structures, migrated surfaces, validation evidence, and proof that the
displaced models are unavailable.

Do not stage or alter the untracked `scratchpad/` files or the user's existing
stash.

**Acceptance criteria:**

- Only five structural identity transformations remain.
- Equality plus disequality is handled by ordinary logic.
- Relation severing abstracts any permitted exact drawn content, including mixed
  parity copies, under one fresh relation wire with explicit ordered boundary and
  parameter gates.
- Relation `wireJoin` grounds every headed application of a quantified relation
  wire to exact drawn content through the ordinary matcher/splicer.
- Iota sever/join retain their atomic semantics; no relation-level atomic-only
  authority competes with the exact-content forms.
- Reification is the derived existential assertion-to-extent construction.
  Every ref obeys ordinary polarity; the definition store has no reification
  recognizer or spawn exception.
- Extensionality and comprehension are unavailable as grammar or kernel authority.
- `existsProp : Exists X. X` is replayable and serialized, and its witness
  descends from corrected relation severing.
- `buildFregeTheory()` verifies the logical prefix and all eight arithmetic
  theorems.
- Arithmetic statements are closed and inline the selected hypotheses.
- `examples/frege.json` regenerates deterministically, loads, and re-verifies.
- Typecheck, unit tests, emission reproducibility, and E2E pass.
- Lean and the general expressiveness proof remain untouched.
