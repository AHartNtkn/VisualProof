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

- Tasks 4A–4D are a strict correction barrier: complete and validate all four
  before any further work on Task 5 or later.
- Phase-2 kernel changes are prohibited. Tasks 4A–4D are the complete authorized
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
- Follow TDD, explicit-path staging, one validated commit per task, `tsc` plus
  focused test gates, and preserve all user scratch/stash material.
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

Expected: PASS.

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

### Task 4C: Migrate the durable proof and application surfaces

**Files:**

- Delete: `src/kernel/rules/reification.ts`
- Modify: `src/kernel/rules/spawn.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `tests/kernel/rules/spawn.test.ts`
- Modify: `tests/app/actions.test.ts`
- Modify: `tests/app/moves.test.ts`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`

**Interfaces:**

- Consumes: `WireSeverInput`, `WireJoinInput`, and `ContentOccurrence` from
  Task 4B.
- Produces uniformly polarity-gated ref spawning plus explicit application
  affordances for Task 4B's already-landed durable step shapes.

- [ ] **Step 1: Write spawn-authority RED tests**

Change spawn tests to require every ref to use the ordinary matrix:

```text
forward: negative only
backward: positive only
```

Exact reification definitions, same-signature lookalikes, root, nested positive,
and nested negative scopes receive no exception. Add an architecture absence
check for `src/kernel/rules/reification.ts` and
`isExactReificationDefinition`.

- [ ] **Step 2: Write application RED tests**

Require direct connection drag to produce only:

```ts
{ rule: 'wireJoin', input: { kind: 'iota', a, b } }
```

for `IOTA` wires. Require relation wires to use the explicit two-phase
`relationJoin` and `relationSever` descriptors below; a direct relation-wire
merge must be rejected.

- [ ] **Step 3: Run RED**

```bash
npx vitest run \
  tests/kernel/rules/spawn.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/action.test.ts \
  tests/app/actions.test.ts \
  tests/app/moves.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
```

Expected: FAIL on the reification spawn exception and direct relation-wire app
connection.

- [ ] **Step 4: Remove the special ref authority**

Delete `src/kernel/rules/reification.ts`. Remove its import and exceptional
callback from `spawn.ts`; `applyRefSpawn` must call the ordinary polarity gate
with no definition-sensitive branch or diagnostic. Remove every recognizer test
fixture and replace it with ordinary polarity coverage.

- [ ] **Step 5: Migrate application affordances**

Keep direct connection-drag join only for `IOTA`. Add explicit two-phase
descriptors and checked step constructors:

```ts
| {
    readonly kind: 'relationSever'
    readonly label: string
    readonly needsInput: 'scope-and-occurrences'
  }
| {
    readonly kind: 'relationJoin'
    readonly label: string
    readonly needsInput: 'wire-content-and-parameters'
  }
```

They return the exact durable steps; they do not search for proofs, synthesize
content, or retain a macro transaction. The UI may extract a DWB from a selected
occurrence as an editing convenience, but the durable step stores the
self-contained DWB and parameter wire IDs, not the host selection. Discovery
mirrors polarity and basic shape only; the kernel applier remains authoritative
and its refusal is surfaced verbatim.

- [ ] **Step 6: Run focused proof/application gates**

```bash
npx vitest run \
  tests/kernel/rules/spawn.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/kernel/proof/action.test.ts \
  tests/kernel/proof/theorem.test.ts \
  tests/app/actions.test.ts \
  tests/app/moves.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 7: Audit absence and commit**

```bash
rg -n \
  "isExactReificationDefinition|exact reification definition|spawn.*every scope" \
  src tests
test ! -e src/kernel/rules/reification.ts
git add -- \
  src/kernel/rules/reification.ts src/kernel/rules/spawn.ts \
  src/app/actions.ts src/app/interact/moves.ts \
  tests/kernel/rules/spawn.test.ts \
  tests/app/actions.test.ts tests/app/moves.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
git commit -m "fix: remove reification spawn authority"
```

Expected `rg`: no production authority; historical documentation is outside the
search. Negative tests may describe the removed behavior without exporting it.

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

**Dependency order:**

1. `plusLeftUnit`
2. `zeroIsNat`
3. `succNat`
4. `oneIsNat`
5. `plusRightUnit`
6. `plusAssoc`
7. `succShiftS`
8. `plusComm`

The logical/reification prefix precedes these eight.

**Proof obligations:**

- `plusLeftUnit`: base and plus single-valuedness.
- `zeroIsNat`: unfold parameterized Nat and establish its base.
- `succNat`: unfold/fold Nat and establish hereditary closure.
- `oneIsNat`: cite `zeroIsNat` and `succNat`.
- `plusRightUnit`, `plusAssoc`, and `succShiftS`: Nat induction with their explicit
  reified predicates.
- `plusComm`: Nat induction citing unit and successor-shift results as needed.
- Every second-order substitution uses the corrected wire-quantifier pair:
  ground a universally scoped relation wire to exact carrier content with
  strongest-form relation `wireJoin`; derive a relation handle only when a
  higher-order argument/identity port grammatically requires one, using the
  recorded sever-based reification theorem. No ref spawn, definition-store
  recognizer, or capture-connection workaround is permitted.

**Tests:**

- `verifyTheory(buildFregeTheory())` succeeds.
- Every arithmetic theorem is closed and includes its own primitives and seven
  inline hypotheses.
- Every action replays; citations target preceding theorems.
- `plusComm` concludes the crossed `Plus(b,a,o)` atom.
- No deleted rule tag or lambda-era node kind occurs.
- Removing a genuinely used hypothesis from representative induction proofs
  makes verification fail.

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
