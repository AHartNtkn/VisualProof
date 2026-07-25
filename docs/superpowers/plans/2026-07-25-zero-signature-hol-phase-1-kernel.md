# Zero-Signature HOL Phase 1 Kernel Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the TypeScript kernel and every TypeScript consumer with the approved zero-signature `atom`/`ref`/`identity` vocabulary, native conditional equality, and ref-store definitional splicing, with no lambda, body, beta-eta, comprehension, or projection-hack path remaining.

**Architecture:** `Sig` has the base sort `iota` and recursive relation sorts. A diagram has exactly three node variants: positional `atom` and `ref` nodes, plus an unordered homogeneous `identity` hyperedge whose canonicalizer owns degeneracy, co-scoped collapse, and same-region fusion. The existing immutable named-relation map remains the definition store, but unfold/fold is rebuilt as the ref-only splice/recognition equivalence; second-order instantiation has no primitive or macro in this phase.

**Tech Stack:** TypeScript 5.5 (strict mode), Node.js 20+, Vitest 2, existing immutable diagram/subgraph/proof infrastructure, Vite application and canvas view.

## Global Constraints

- The authoritative design inputs are `docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md` and `docs/superpowers/specs/2026-07-25-identity-node-design.md`; where they differ, the umbrella redesign controls.
- Do not consult or implement the superseded
  `docs/superpowers/specs/2026-07-23-drawn-definitions-*` specs or plan. Their
  comprehension rules and retained lambda layer are prohibited here.
- Node kinds are exactly `atom`, `ref`, and `identity`; `term` and `body` are deleted, not deprecated or aliased.
- Signature syntax is `iota | rel(Sig…)`; do not retain `TERM`, `{ kind: 'term' }`, or a decoding compatibility branch.
- Keep insertion/erasure, iteration/deiteration, double-cut introduction/elimination, `wireJoin`, bare vacuous relation-wire introduction/elimination, theorem citation, and ref-only unfold/fold.
- Identity normalization is eager and silent: degeneracy drop, co-scoped collapse, and same-region fusion run to a fixpoint after every construction or rewrite.
- Identity ports are homogeneous and unordered. Storage indices may identify port incidences, but canonical forms, matching, and certificates must not observe their ordering.
- Rule 5 extends iteration/deiteration with explicit, certificate-replayable retargeting through a dominating identity node.
- Rule 6 is structural contradiction discharge: an asserted identity directly
  inside a cut contradicts the same identity directly inside a child cut. It
  introduces no distinctness oracle, beta-eta certificate, normalization search,
  or computation rule. Named-object disequalities remain ordinary Phase-2 theory
  axioms represented by negated identity nodes.
- Ref unfold/fold resolves only through the relation definition store. There is no atom/body path, body payload, comprehension rule, relation-congruence join, or primitive second-order-instantiation step.
- Do not implement an Eq library, reification library, macro system, relational Frege theory, Lean semantics, or expressiveness proof. Those belong to Phases 2, 3, and 4.
- Do not edit `VisualProof/**` in Phase 1. Remove TypeScript-to-Lean parity tests that encode the displaced rule vocabulary; Phase 3 will replace them with the new semantics.
- Delete `tests/kernel/rules/uniqueness-representability.test.ts` even though it is untracked; it asserts the projection workaround this phase replaces.
- Use TDD for every behavior change. Run the named failing test before implementation, then the same test green.
- Stage only explicit task paths. Never use `git add .`, `git add -A`, a
  directory operand, a glob, or command substitution. At each commit, inspect
  `git status --short`, copy every task-owned filename as a literal `git add --`
  operand, and verify the resulting exact list with
  `git diff --cached --name-only`.
- Every task commit must contain only that task's paths. Final acceptance requires `npm run typecheck`, `npm test`, and `npm run test:all`.

---

## File and Responsibility Map

### New authorities

- Create `src/kernel/diagram/canonical/identity.ts`: the sole identity-normalization implementation and wire-image receipt.
- Create `src/kernel/rules/identity.ts`: identity insertion, validation of
  iteration/deiteration retarget evidence, and asserted-equality-versus-negated-
  equality contradiction discharge.
- Create `tests/fixtures/zero-signature.ts`: reusable atom/ref/identity diagrams and a tiny definition-store/theory fixture; this is test data, not the Phase-2 theory corpus.
- Create `tests/kernel/diagram/identity.test.ts`: identity validation, unorderedness, normalization, JSON, canonical form, extraction, matching, and splice coverage.
- Create `tests/kernel/rules/identity.test.ts`: Rules 4–6 behavior, especially insertion polarity and identity-aware iteration/deiteration.
- Create `tests/architecture/kernel-vocabulary.test.ts`: negative authority check proving removed TypeScript vocabulary and files are absent.

### Rebuilt kernel surfaces

- Modify `src/kernel/diagram/sig.ts`, `src/kernel/diagram/diagram.ts`, `src/kernel/diagram/builder.ts`, `src/kernel/diagram/json.ts`, `src/kernel/diagram/index.ts`, and `src/kernel/diagram/spawn.ts`: `iota`, three node kinds, identity ports, construction, codec, and public exports.
- Modify `src/kernel/diagram/canonical/explore.ts`: exact canonical labeling for atom/ref and unordered identity nodes.
- Modify `src/kernel/diagram/subgraph/extract.ts`, `src/kernel/diagram/subgraph/splice.ts`, `src/kernel/diagram/subgraph/match.ts`, and `src/kernel/diagram/subgraph/occurrence-certificate.ts`: exact three-node extraction/splicing/matching and certificate replay with no term comparison or fuel.
- Modify `src/kernel/rules/spawn.ts`, `src/kernel/rules/iteration.ts`, `src/kernel/rules/vacuous.ts`, `src/kernel/rules/fold.ts`, `src/kernel/rules/access.ts`, `src/kernel/rules/doublecut.ts`, `src/kernel/rules/erasure.ts`, `src/kernel/rules/wire-join.ts`, and `src/kernel/rules/index.ts`: surviving structural rules, identity retargeting, and ref-only transparency.
- Modify `src/kernel/proof/context.ts`, `src/kernel/proof/store.ts`, `src/kernel/proof/step.ts`, `src/kernel/proof/json.ts`, `src/kernel/proof/compose.ts`, and `src/kernel/proof/index.ts`: exact definition signatures, reduced proof vocabulary, normalization-aware wire transport, and new JSON schema.
- Modify the kernel diagram/rule/proof tests that currently use term nodes merely as generic content; replace their fixtures with atoms, refs, cuts, identities, and bare wires.

### Deleted kernel authorities

- Delete `src/kernel/diagram/canonical/shape.ts` and `src/kernel/diagram/canonical/matchkey.ts`.
- Delete `src/kernel/rules/anchored-wire.ts`, `src/kernel/rules/body.ts`, `src/kernel/rules/congruence.ts`, `src/kernel/rules/conversion.ts`, `src/kernel/rules/fusion.ts`, `src/kernel/rules/headstrip.ts`, `src/kernel/rules/inconsistent-cut.ts`, `src/kernel/rules/intro.ts`, and `src/kernel/rules/port-correspondence.ts`.
- Delete every file under `src/kernel/term/`.
- Delete every file under `tests/kernel/term/`.
- Delete `tests/kernel/rules/anchored-wire.test.ts`, `tests/kernel/rules/body.test.ts`, `tests/kernel/rules/congruence.test.ts`, `tests/kernel/rules/conversion.test.ts`, `tests/kernel/rules/fusion.test.ts`, `tests/kernel/rules/headstrip.test.ts`, `tests/kernel/rules/inconsistent-cut.test.ts`, `tests/kernel/rules/intro.test.ts`, `tests/kernel/rules/port-correspondence.test.ts`, and the untracked `tests/kernel/rules/uniqueness-representability.test.ts`.
- Delete `tests/kernel/formal/correspondence.test.ts` and `tests/kernel/formal/highlevel-alias-parity.test.ts`; do not replace or edit Lean in Phase 1.

### Rebuilt TypeScript dependents

- Modify `src/app/edit.ts`, `src/app/actions.ts`, `src/app/copy-planner.ts`, `src/app/define.ts`, `src/app/library.ts`, `src/app/boot.ts`, `src/app/persist.ts`, `src/app/proof-front.ts`, `src/app/shell.ts`, `src/app/index.ts`, and the surviving `src/app/interact/*.ts` controllers: three-node construction, exact copy/definition actions, and removal of computation/comprehension affordances.
- Modify `src/view/bend.ts`, `src/view/engine.ts`, `src/view/index.ts`, `src/view/morph.ts`, `src/view/optimize.ts`, `src/view/paint.ts`, and `src/view/relax.ts`: atom/ref/identity geometry only.
- Modify ordinary app/view/physics tests to use `tests/fixtures/zero-signature.ts` instead of the old Frege/Lambda builders.
- Modify `demo/main.ts` to display a small identity/ref diagram without parsing terms.
- Modify `scripts/render-junction-gallery.ts` to use `IOTA` fixtures and remove
  its Frege replay scene.
- Modify `docs/kernel/canonicalization.md` to document unordered identity refinement and the absence of beta-eta matching.

### Deleted TypeScript dependents

- Delete `src/app/abstraction-matches.ts`, `src/app/tactics.ts`, `src/app/relation-transactions.ts`, `src/app/relation-workspace.ts`, `src/app/relation-workspace-draft.ts`, `src/app/interact/closed-term-intro.ts`, `src/app/interact/comprehension-macros.ts`, `src/app/interact/fission.ts`, and `src/interaction/named-relation.ts`.
- Delete their dedicated tests: `tests/app/abstraction-interaction.test.ts`, `tests/app/abstraction-matches.test.ts`, `tests/app/closed-term-intro.test.ts`, `tests/app/comprehension-macros.test.ts`, `tests/app/fission-interaction.test.ts`, `tests/app/relation-transactions.test.ts`, `tests/app/relation-workspace-dependencies.test.ts`, `tests/app/relation-workspace-draft.test.ts`, `tests/app/relation-workspace.test.ts`, `tests/app/tactics.test.ts`, and `tests/interaction/named-relation.test.ts`.
- Delete `app/test/relation-workspace.html`, `app/test/relation-workspace.ts`, `e2e/abstraction.spec.ts`, and `e2e/relation-workspace.spec.ts`.
- Delete `src/view/tromp.ts` and `tests/view/tromp.test.ts`.
- Delete `src/theories/frege.ts`, `src/theories/lambda.ts`, `src/theories/macros.ts`, all `tests/theories/*.test.ts`, `scripts/emit-theories.ts`, `tests/scripts/emit-theories.test.ts`, `examples/frege.json`, and `examples/lambda.json`. Keep `src/theories/index.ts` as an empty module so the established layer boundary remains present for Phase 2.
- Remove `emit:theories`, `preapp`, and `pree2e` from `package.json`.

---

### Task 1: Rename the base signature from `term` to `iota`

**Files:**
- Modify: `src/kernel/diagram/sig.ts:1-171`
- Modify: `src/kernel/diagram/json.ts:58-92`
- Modify: every tracked TypeScript use returned by `rg -l '\bTERM\b|kind: .term.|kind === .term.' src tests scripts`
- Test: `tests/kernel/diagram/sig.test.ts`
- Test: `tests/kernel/diagram/json.test.ts`

**Interfaces:**
- Consumes: the recursive `Sig` grammar already used on every wire.
- Produces:

```ts
export type Sig =
  | { readonly kind: 'iota' }
  | { readonly kind: 'rel'; readonly args: readonly Sig[] }

export type RelSig = Extract<Sig, { kind: 'rel' }>
export const IOTA: Sig
export function relSig(args: readonly Sig[]): RelSig
export function sigEquals(a: Sig, b: Sig): boolean
export function sigKey(sig: Sig): string // "i" for iota
```

- [ ] **Step 1: Change the signature tests to the new vocabulary**

Replace `TERM` expectations with `IOTA`, require `sigKey(IOTA) === 'i'`, require JSON `{ kind: 'iota' }`, and add a rejection assertion for `{ kind: 'term' }`.

```ts
expect(sigEquals(IOTA, { kind: 'iota' })).toBe(true)
expect(sigKey(relSig([IOTA, relSig([IOTA])]))).toBe('(i,(i))')
expect(sigToJson(IOTA)).toEqual({ kind: 'iota' })
expect(() => sigFromJson({ kind: 'term' }, 'wire')).toThrow(/kind.*iota.*rel/)
```

- [ ] **Step 2: Run the focused tests and observe the vocabulary failure**

Run:

```bash
npx vitest run tests/kernel/diagram/sig.test.ts tests/kernel/diagram/json.test.ts
```

Expected: FAIL because `IOTA` is not exported and the old codec still accepts `term`.

- [ ] **Step 3: Replace the signature authority without an alias**

Implement `IOTA`, update recursive equality/key/order/validation, and change the codec to emit and accept only `iota`. Do not export `TERM`.

```ts
export const IOTA: Sig = Object.freeze({ kind: 'iota' })

export function sigKey(sig: Sig): string {
  return sig.kind === 'iota'
    ? 'i'
    : `(${sig.args.map(sigKey).join(',')})`
}
```

- [ ] **Step 4: Mechanically migrate consumers and fixtures**

Use exact replacements only in tracked TypeScript:

```bash
rg -l '\bTERM\b' src tests scripts
rg -l "kind: 'term'|kind === 'term'|case 'term'" src tests scripts
```

Change base-sort references to `IOTA`/`iota`. Do not change semantic node-kind branches yet; those are removed in Task 2.

- [ ] **Step 5: Run focused tests and TypeScript**

Run:

```bash
npx vitest run tests/kernel/diagram/sig.test.ts tests/kernel/diagram/json.test.ts
npm run typecheck
```

Expected: both commands PASS.

- [ ] **Step 6: Commit the signature migration with explicit paths**

```bash
git add -- src/kernel/diagram/sig.ts src/kernel/diagram/json.ts tests/kernel/diagram/sig.test.ts tests/kernel/diagram/json.test.ts
git status --short
git diff --cached --name-only
git commit -m "refactor: rename the individual signature to iota"
```

Before the cached-list check, stage every other Task-1 consumer shown by status
with literal file operands. Do not stage the untracked projection-hack test; Task
5 deletes it.

---

### Task 2: Rebuild the diagram vocabulary and identity canonicalizer

**Files:**
- Create: `src/kernel/diagram/canonical/identity.ts`
- Create: `tests/kernel/diagram/identity.test.ts`
- Modify: `src/kernel/diagram/diagram.ts:1-466`
- Modify: `src/kernel/diagram/builder.ts:1-111`
- Modify: `src/kernel/diagram/json.ts:1-208`
- Modify: `src/kernel/diagram/canonical/explore.ts:1-520`
- Modify: `src/kernel/diagram/index.ts:1-25`
- Modify: `src/kernel/diagram/subgraph/extract.ts:1-91`
- Modify: `src/kernel/diagram/subgraph/splice.ts:1-250`
- Modify: `src/kernel/diagram/subgraph/match.ts:1-503`
- Modify: `src/kernel/diagram/subgraph/occurrence-certificate.ts:1-276`
- Delete: `src/kernel/diagram/canonical/shape.ts`
- Delete: `src/kernel/diagram/canonical/matchkey.ts`

**Interfaces:**
- Consumes: `Sig`, region ancestry, `DiagramWithBoundary`, deterministic fresh IDs.
- Produces:

```ts
export type IdentityDiagramNode = {
  readonly kind: 'identity'
  readonly region: RegionId
  readonly sig: Sig
  readonly arity: number
}

export type DiagramNode =
  | { readonly kind: 'atom'; readonly region: RegionId; readonly sig: RelSig }
  | { readonly kind: 'ref'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | IdentityDiagramNode

export type Port =
  | { readonly kind: 'arg'; readonly index: number }
  | { readonly kind: 'head' }
  | { readonly kind: 'identity'; readonly index: number }

export type DiagramNormalization = {
  readonly diagram: Diagram
  readonly wireImage: ReadonlyMap<WireId, WireId | undefined>
}

export function mkDiagramNormalized(parts: DiagramParts): DiagramNormalization
export function mkDiagram(parts: DiagramParts): Diagram
```

- [ ] **Step 1: Write failing primitive and normalization tests**

Cover these exact cases in `tests/kernel/diagram/identity.test.ts`:

```ts
it('accepts an unordered homogeneous identity with at least two incidences')
it('rejects arity below two, missing incidences, and mixed wire signatures')
it('drops an identity whose incidences all reach one distinct wire')
it('collapses a co-scoped identity to the lexicographically first wire')
it('keeps an identity when any attached wire is scoped above its region')
it('fuses same-region identities sharing a wire and reaches a fixpoint')
it('does not fuse identity nodes in different regions')
it('canonicalizes port permutations to one explore form')
it('round-trips identity JSON and rejects term/body node JSON')
```

The co-scoped test must assert both content and transport:

```ts
const normalized = mkDiagramNormalized(parts)
expect(Object.keys(normalized.diagram.nodes)).not.toContain('eq')
expect(Object.keys(normalized.diagram.wires)).toContain('a')
expect(Object.keys(normalized.diagram.wires)).not.toContain('b')
expect(normalized.wireImage.get('a')).toBe('a')
expect(normalized.wireImage.get('b')).toBe('a')
```

- [ ] **Step 2: Run the new test and observe the missing node kind**

Run:

```bash
npx vitest run tests/kernel/diagram/identity.test.ts
```

Expected: FAIL because identity types, ports, builder, and normalizer do not exist.

- [ ] **Step 3: Replace `DiagramNode`, ports, validation, and builder methods**

Delete term/body imports and free-port canonicalization from `diagram.ts`. Require identity `arity` to be a safe integer at least 2, create exactly `arity` identity ports, and require every attached wire to equal `node.sig`.

```ts
case 'identity':
  return Array.from(
    { length: node.arity },
    (_, index): Port => ({ kind: 'identity', index }),
  )
```

Add:

```ts
identity(region: RegionId, sig: Sig, arity: number): NodeId
```

to `DiagramBuilder`. The builder still auto-creates one wire per unattached port; tests that need a specific equality attach the identity ports explicitly.

- [ ] **Step 4: Implement one fixpoint normalizer with a wire-image receipt**

In `canonical/identity.ts`, validate the raw graph first, then repeatedly apply rules in this deterministic order:

1. lexicographically first degenerate identity;
2. lexicographically first fully co-scoped identity;
3. lexicographically first pair of same-region identities sharing a wire.

For wire merging, the lexicographically first wire survives, non-identity endpoints are unioned, absorbed wires map to the survivor, and composed `wireImage` entries are path-compressed before return. For node fusion, the lexicographically first node survives, its incident distinct wire IDs are sorted only for storage, and its `arity` is rebuilt from that set.

```ts
export function normalizeIdentities(raw: Diagram): DiagramNormalization {
  let current = raw
  const image = new Map(Object.keys(raw.wires).map((wire) => [wire, wire] as const))
  for (;;) {
    const next = normalizeOneIdentity(current, image)
    if (next === null) return { diagram: current, wireImage: freezeImage(image) }
    current = next
  }
}
```

Keep raw validation and normalized validation as private helpers so `mkDiagramNormalized` does not recurse through `mkDiagram`.

- [ ] **Step 5: Rebuild the codec and exact canonical explorer**

Identity JSON is:

```json
{"kind":"identity","region":"r1","sig":{"kind":"iota"},"arity":3}
```

Identity port keys are `i:0`, `i:1`, and so on. The storage keys identify incidences only. In canonical refinement and serialization, use a sorted multiset of incident wire colors/ordinals for identity nodes; never serialize the incidence index as semantic order.

Delete term shape keys, beta-eta modes, `NodeMatchVerdict`, undecided term pairs, conversion fuel, and `termCertificates`. The exact matcher interface becomes:

```ts
export type MatchResult = {
  readonly status: 'complete' | 'exhausted'
  readonly matches: readonly Occurrence[]
  readonly explorationSteps: number
}

export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts?: {
    readonly explorationFuel?: number
    readonly inRegion?: RegionId
    readonly attachments?: readonly WireId[]
  },
): MatchResult
```

For identity compatibility, compare `sig`, `arity`, and the unordered mapped incident-wire multiset.

- [ ] **Step 6: Replace the repeated-boundary projection hack in splice**

In `spliceSubgraphMapped`, remove the `port('s0')` import and projection term construction. For each repeated pattern boundary wire landing on more than one distinct host wire, add one identity node at `atRegion`:

```ts
nodes[identityId] = {
  kind: 'identity',
  region: atRegion,
  sig: stub.sig,
  arity: distinctAttachments.length,
}
```

Attach `{ kind: 'identity', index }` once to each distinct attachment. Pass the result through `mkDiagramNormalized`; compose its wire image into `MappedSplice.wireMap`. Same-scope attachments collapse to one shared wire; outer-scoped attachments remain connected by the conditional identity node.

- [ ] **Step 7: Migrate extraction, occurrence certificates, and existing diagram tests**

Every exhaustive node switch has only atom/ref/identity branches. Replace generic term fixtures in diagram tests with:

- a unary `ref` for positional-port tests;
- an `atom` on a relational head wire for mixed-sort tests;
- an outer-scoped identity inside a cut for unordered-node tests.

Delete `tests/kernel/diagram/matchkey.test.ts` and `tests/kernel/diagram/shape.test.ts`; move any still-relevant exact graph-isomorphism assertions into `identity.test.ts` or `explore.test.ts`.

- [ ] **Step 8: Run the complete diagram suite**

Run:

```bash
npx vitest run tests/kernel/diagram
```

Expected: PASS with no term/body matcher or certificate tests remaining.

- [ ] **Step 9: Commit the diagram vocabulary**

```bash
git add -- src/kernel/diagram/diagram.ts src/kernel/diagram/builder.ts src/kernel/diagram/json.ts src/kernel/diagram/index.ts src/kernel/diagram/canonical/identity.ts src/kernel/diagram/canonical/explore.ts src/kernel/diagram/subgraph/extract.ts src/kernel/diagram/subgraph/splice.ts src/kernel/diagram/subgraph/match.ts src/kernel/diagram/subgraph/occurrence-certificate.ts tests/kernel/diagram/identity.test.ts src/kernel/diagram/canonical/shape.ts src/kernel/diagram/canonical/matchkey.ts tests/kernel/diagram/shape.test.ts tests/kernel/diagram/matchkey.test.ts
git status --short
git diff --cached --name-only
git commit -m "feat: replace diagram nodes with atom ref and identity"
```

Stage every other modified diagram test as its own literal operand before the
cached-list check.

---

### Task 3: Add identity insertion and equals-for-equals iteration

**Files:**
- Create: `src/kernel/rules/identity.ts`
- Create: `tests/kernel/rules/identity.test.ts`
- Modify: `src/kernel/rules/iteration.ts:1-143`
- Modify: `src/kernel/rules/erasure.ts:1-51`
- Modify: `src/kernel/rules/doublecut.ts:1-180`
- Modify: `src/kernel/rules/wire-join.ts:1-56`
- Modify: `src/kernel/rules/index.ts:1-34`
- Modify: `tests/kernel/rules/iteration.test.ts`
- Modify: `tests/kernel/rules/open-rules.test.ts`
- Modify: `tests/kernel/rules/polarity-matrix.test.ts`

**Interfaces:**
- Consumes: normalized identity nodes, region ancestry, extraction/splice, occurrence certificates.
- Produces:

```ts
export type IdentityRetarget = {
  readonly boundary: number
  readonly identity: NodeId
  readonly from: WireId
  readonly to: WireId
}

export function applyIdentityInsertion(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
  reservation?: IdReservation,
): Diagram

export function applyIteration(
  diagram: Diagram,
  selection: SubgraphSelection,
  targetRegion: RegionId,
  retargets?: readonly IdentityRetarget[],
  reservation?: IdReservation,
): Diagram

export type IdentityContradictionEvidence = {
  readonly equality: NodeId
  readonly disequalityCut: RegionId
  readonly disequality: NodeId
}

export function applyIdentityContradiction(
  diagram: Diagram,
  enclosingCut: RegionId,
  evidence: IdentityContradictionEvidence,
): Diagram
```

`applyDeiteration` and `findDeiterationEvidence` gain the same retarget evidence.

- [ ] **Step 1: Write the six-rule behavioral matrix**

Tests must cover:

- Rule 1, Rule 2, and Rule 3 through the canonicalizer tests from Task 2;
- Rule 4 insertion only in a negative region and ordinary positive erasure of
  an identity selection;
- ordinary positive erasure deleting an identity node;
- Rule 5 iteration retargeting `from` to `to` through an identity whose region dominates the target;
- reverse retargeting (symmetry), multi-boundary retargeting, and deiteration round-trip;
- rejection for a wrong identity ID, unlinked wires, mismatched boundary index, signature mismatch, non-dominating identity, and reversed source/target direction;
- Rule 6 discharges a cut containing an asserted identity plus a direct child
  cut containing the same unordered identity. It rejects mismatched signatures,
  wire sets, non-direct regions, non-identity nodes, and evidence outside the
  enclosing cut.
- Rule 6's simplified contract has no `distinctness`, `normalize`,
  `certificate`, or object-language callback parameter. The old
  `applyInconsistentCutElim` API is not exported.

Use an outer `iota` wire pair, an identity node in an ancestor cut, and an atom copied into a descendant cut. Assert the copied atom's selected argument endpoint lands on `to`, while the source remains on `from`.

- [ ] **Step 2: Run the identity rule test and observe missing APIs**

Run:

```bash
npx vitest run tests/kernel/rules/identity.test.ts
```

Expected: FAIL because insertion and retarget evidence are not implemented.

- [ ] **Step 3: Implement identity insertion as inherited insertion**

Validate at least two distinct existing wires, one signature, visibility at
`region`, and negative polarity. Create the node and its incidences; let
canonicalization eliminate an unconditional same-scope equality. Positive
removal continues through ordinary `applyErasure`.

```ts
if (polarity(diagram, region) !== 'negative') {
  throw new RuleError('identity insertion requires a negative region')
}
```

- [ ] **Step 4: Validate explicit retarget evidence before splicing**

For each retarget:

1. `boundary` is a unique safe index into the extracted boundary;
2. the extracted source attachment equals `from`;
3. `identity` names an identity node containing both `from` and `to`;
4. `from` and `to` have the identity signature;
5. the identity region is ancestor-or-equal to the copy/removal region;
6. iteration moves from the outer justifier toward the inner copy, and deiteration proves the inverse against the supplied occurrence.

Retarget only the named boundary position. Do not globally replace every equal wire, because one boundary may repeat and substitution is an endpoint-level choice.

- [ ] **Step 5: Remove beta-eta search from deiteration**

`findDeiterationEvidence` accepts only `explorationFuel`; occurrence matching is exact and returns no `undecided` list. Its refusal reports either no exact justifier or exhausted graph exploration, never beta-eta fuel.

- [ ] **Step 6: Implement structural Rule 6 without an oracle**

`applyIdentityContradiction` validates this exact shape:

1. `enclosingCut` is a cut;
2. `equality` is an identity node directly in `enclosingCut`;
3. `disequalityCut` is a direct child cut of `enclosingCut`;
4. `disequality` is an identity node directly in `disequalityCut`;
5. both nodes have recursively equal signatures and the same unordered set of
   attached wire IDs.

The conjunction inside `enclosingCut` contains both `x=y` and `¬(x=y)`, so remove
the entire enclosing cut subgraph. This is the old cut-discharge *shape* with
pure graph evidence; do not import term normalization or accept any external
certificate.

- [ ] **Step 7: Run the rule slice**

Run:

```bash
npx vitest run tests/kernel/rules/identity.test.ts tests/kernel/rules/iteration.test.ts tests/kernel/rules/erasure.test.ts tests/kernel/rules/doublecut.test.ts tests/kernel/rules/wire-join.test.ts tests/kernel/rules/open-rules.test.ts tests/kernel/rules/polarity-matrix.test.ts
```

Expected: PASS, including direct Rule-6 acceptance and every malformed-evidence
rejection.

- [ ] **Step 8: Commit identity rules**

```bash
git add -- src/kernel/rules/identity.ts src/kernel/rules/iteration.ts src/kernel/rules/erasure.ts src/kernel/rules/doublecut.ts src/kernel/rules/wire-join.ts src/kernel/rules/index.ts tests/kernel/rules/identity.test.ts tests/kernel/rules/iteration.test.ts tests/kernel/rules/open-rules.test.ts tests/kernel/rules/polarity-matrix.test.ts
git diff --cached --name-only
git commit -m "feat: add identity insertion and substitution rules"
```

---

### Task 4: Rebuild unfold/fold as ref-store splicing

**Files:**
- Modify: `src/kernel/rules/fold.ts:1-282`
- Modify: `src/kernel/rules/spawn.ts:1-71`
- Modify: `src/kernel/diagram/spawn.ts:1-82`
- Modify: `src/kernel/rules/access.ts:1-26`
- Modify: `src/kernel/proof/context.ts:303-395`
- Modify: `tests/kernel/rules/fold.test.ts`
- Modify: `tests/kernel/diagram/ref-node.test.ts`
- Modify: `tests/kernel/proof/context.test.ts`

**Interfaces:**
- Consumes: `ReadonlyMap<string, DiagramWithBoundary>` as the sole definition store, exact boundary signatures, splice and canonical form.
- Produces:

```ts
export function definitionSig(definition: DiagramWithBoundary): RelSig

export function applyUnfold(
  diagram: Diagram,
  refNode: NodeId,
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  reservation?: IdReservation,
): Diagram

export function applyFold(
  diagram: Diagram,
  occurrence: SubgraphSelection,
  args: readonly WireId[],
  defId: string,
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  reservation?: IdReservation,
): Diagram
```

- [ ] **Step 1: Rewrite fold tests around refs only**

Add failing tests for:

- unfold obtains the body from `ref.defId`, freshens all internal IDs, attaches each boundary position to the ref argument wire, and removes only the ref;
- fold recognizes the exact boundary-pinned definition and creates one ref;
- unfold then fold and fold then unfold preserve `exploreForm`;
- both directions work in positive and negative regions;
- repeated definition boundary incidences use Task-2 identity splicing;
- missing definition, wrong arity, wrong nested signature, unused attachment, and near-match refuse;
- atom nodes are rejected by unfold and no `wireId`/body fold target exists.

- [ ] **Step 2: Run the focused test and observe the atom/body path**

Run:

```bash
npx vitest run tests/kernel/rules/fold.test.ts tests/kernel/diagram/ref-node.test.ts
```

Expected: FAIL because the current fold module still accepts atom/body targets and checks only the older definition shape.

- [ ] **Step 3: Rebuild `fold.ts` around one definition source**

Delete `bodyOnWire`, `bodyParamWires`, the atom branch, `FoldTarget`, and parameter-boundary arithmetic. Derive the stored definition signature from the ordered boundary wire signatures:

```ts
export function definitionSig(definition: DiagramWithBoundary): RelSig {
  return relSig(definition.boundary.map((wire) => definition.diagram.wires[wire]!.sig))
}
```

Compare `definitionSig(body)` to `ref.sig` with recursive `sigEquals`, not arity alone.

- [ ] **Step 4: Strengthen definition-store ref verification**

Replace the `relationArities` map in `context.ts` with exact `RelSig` values. `assertRefsResolve` must reject a ref whose arity matches but nested argument signature differs.

```ts
if (!sigEquals(node.sig, expected)) {
  throw new ProofError(
    `${where}: reference node '${id}' signature '${sigKey(node.sig)}' does not match definition '${node.defId}' signature '${sigKey(expected)}'`,
  )
}
```

- [ ] **Step 5: Rename spawn operations to the vocabulary they create**

Replace `spawnRelationNode`/`applyRelationSpawn` with `spawnRefNode`/`applyRefSpawn`. Replace `spawnBoundRelationNode`/`applyBoundRelationSpawn` with `spawnAtomNode`/`applyAtomSpawn`. Do not keep aliases; proof steps migrate in Task 5.

- [ ] **Step 6: Run fold/context tests**

Run:

```bash
npx vitest run tests/kernel/rules/fold.test.ts tests/kernel/diagram/ref-node.test.ts tests/kernel/proof/context.test.ts
```

Expected: PASS.

- [ ] **Step 7: Commit ref-store transparency**

```bash
git add -- src/kernel/rules/fold.ts src/kernel/rules/spawn.ts src/kernel/diagram/spawn.ts src/kernel/rules/access.ts src/kernel/proof/context.ts tests/kernel/rules/fold.test.ts tests/kernel/diagram/ref-node.test.ts tests/kernel/proof/context.test.ts
git diff --cached --name-only
git commit -m "refactor: source fold and unfold only from refs"
```

---

### Task 5: Replace the proof-step and persistence vocabulary

**Files:**
- Modify: `src/kernel/proof/step.ts:1-288`
- Modify: `src/kernel/proof/json.ts:1-555`
- Modify: `src/kernel/proof/compose.ts:1-240`
- Modify: `src/kernel/proof/store.ts:1-65`
- Modify: `src/kernel/proof/index.ts:1-17`
- Modify: `src/kernel/rules/vacuous.ts:1-106`
- Modify: `src/kernel/rules/index.ts:1-34`
- Delete: `src/kernel/rules/anchored-wire.ts`
- Delete: `src/kernel/rules/body.ts`
- Delete: `src/kernel/rules/congruence.ts`
- Delete: `src/kernel/rules/conversion.ts`
- Delete: `src/kernel/rules/fusion.ts`
- Delete: `src/kernel/rules/headstrip.ts`
- Delete: `src/kernel/rules/inconsistent-cut.ts`
- Delete: `src/kernel/rules/intro.ts`
- Delete: `src/kernel/rules/port-correspondence.ts`
- Delete: every `src/kernel/term/*.ts`
- Test: `tests/kernel/proof/step.test.ts`
- Test: `tests/kernel/proof/json.test.ts`
- Test: `tests/kernel/proof/compose.test.ts`
- Test: `tests/kernel/proof/store.test.ts`

**Interfaces:**
- Consumes: surviving rules from Tasks 3–4 and identity normalization receipts.
- Produces this exact primitive step inventory:

```ts
export type ProofStep =
  | { readonly rule: 'refSpawn'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | { readonly rule: 'atomSpawn'; readonly region: RegionId; readonly wire: WireId }
  | { readonly rule: 'identityInsert'; readonly region: RegionId; readonly wires: readonly WireId[] }
  | { readonly rule: 'identityContradiction'; readonly enclosingCut: RegionId; readonly evidence: IdentityContradictionEvidence }
  | { readonly rule: 'wireJoin'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly wire: WireId; readonly keep: readonly Endpoint[] }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId; readonly retargets: readonly IdentityRetarget[] }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly justifier: SubgraphSelection; readonly certificate: OccurrenceCertificate; readonly retargets: readonly IdentityRetarget[] }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuousIntro'; readonly scope: RegionId; readonly sig: Sig }
  | { readonly rule: 'vacuousElim'; readonly wireId: WireId }
  | { readonly rule: 'unfold'; readonly nodeId: NodeId }
  | { readonly rule: 'fold'; readonly occurrence: SubgraphSelection; readonly args: readonly WireId[]; readonly defId: string }
```

- [ ] **Step 1: Rewrite proof JSON tests to the final inventory**

Round-trip every variant above. Add one table-driven rejection test for all removed rule strings:

```ts
for (const rule of [
  'openTermSpawn', 'relationSpawn', 'boundRelationSpawn',
  'inconsistentCutElim', 'conversion', 'congruenceJoin',
  'anchoredWireSplit', 'anchoredWireContract', 'headStrip',
  'closedTermIntro', 'fusion', 'fission',
  'bodyAttach', 'bodyDetach',
]) {
  expect(() => stepFromJson({ rule })).toThrow(/unknown rule/)
}
```

Update occurrence-certificate JSON to omit `termCertificates`. Bump the theory-store version from `1` to `2`; version 1 must reject rather than migrate.

- [ ] **Step 2: Run proof JSON tests and observe old variants**

Run:

```bash
npx vitest run tests/kernel/proof/json.test.ts tests/kernel/proof/store.test.ts
```

Expected: FAIL because removed rule variants and theory version 1 are still accepted/emitted.

- [ ] **Step 3: Reduce `ProofStep`, replay, composition, and codecs**

Implement exactly the union above. `mapStepIds` maps identity wire arrays and each retarget's node/wires; fold maps `defId` directly. Delete all term/path/certificate/correspondence helpers and JSON fields.

`mapStepIds` also maps all three IDs in
`IdentityContradictionEvidence`. Replay routes `identityContradiction` only to
`applyIdentityContradiction`; it never invokes discovery or semantic search.

Keep `vacuousIntro` bare:

```ts
export function applyVacuousIntro(
  diagram: Diagram,
  scope: RegionId,
  sig: Sig,
  reservation?: IdReservation,
): Diagram
```

Delete bodied vacuity and all body-node elimination branches.

- [ ] **Step 4: Make step receipts compose identity normalization**

Use the normalizer's `wireImage` after every raw rule result. Compose:

1. the rule's intentional wire mapping (`wireJoin`, splice, fold/unfold);
2. identity canonicalization's mapping;
3. the root-scope filter.

An absorbed root boundary wire must map to the canonical survivor; an erased wire remains `undefined`. Add a step test where `wireJoin` degenerates an identity and a double-cut elimination makes an identity co-scoped.

- [ ] **Step 5: Delete the displaced kernel and tests**

Delete the files listed for this task and:

```bash
rm -f tests/kernel/rules/uniqueness-representability.test.ts
```

Delete every test under `tests/kernel/term/` and the dedicated removed-rule tests listed in the File Map. Do not add skip markers.

- [ ] **Step 6: Migrate surviving proof/rule tests**

Replace incidental term content with the shared zero-signature fixtures:

- use a ref node for proof boundary transport;
- use an atom inside cuts for polarity and double-cut tests;
- use an identity node for multi-wire normalization;
- use exact occurrence matching with `explorationFuel`, never beta-eta fuel.

Remove the bodied vacuity block from `tests/kernel/rules/vacuous.test.ts`; keep bare `iota` and relation-sort vacuity tests.

- [ ] **Step 7: Run all kernel tests**

Run:

```bash
npx vitest run tests/kernel
```

Expected: PASS. No file under `tests/kernel` imports `src/kernel/term` or names a removed proof rule.

- [ ] **Step 8: Commit the proof vocabulary and deletions**

```bash
git add -- src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts src/kernel/proof/store.ts src/kernel/proof/index.ts src/kernel/rules/vacuous.ts src/kernel/rules/index.ts
git add -- src/kernel/rules/anchored-wire.ts src/kernel/rules/body.ts src/kernel/rules/congruence.ts src/kernel/rules/conversion.ts src/kernel/rules/fusion.ts src/kernel/rules/headstrip.ts src/kernel/rules/inconsistent-cut.ts src/kernel/rules/intro.ts src/kernel/rules/port-correspondence.ts
git status --short
git diff --cached --name-only
git commit -m "refactor: remove lambda and comprehension proof rules"
```

Stage every deleted `src/kernel/term/*.ts`, `tests/kernel/term/*.ts`, removed-rule
test, formal parity test, and modified surviving kernel test with literal
operands from `git status --short`. Verify
`test ! -e tests/kernel/rules/uniqueness-representability.test.ts` before
committing.

---

### Task 6: Migrate app construction and proof interactions

**Files:**
- Create: `tests/fixtures/zero-signature.ts`
- Modify: `src/app/edit.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/copy-planner.ts`
- Modify: `src/app/define.ts`
- Modify: `src/app/library.ts`
- Modify: `src/app/boot.ts`
- Modify: `src/app/persist.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/index.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/interact/copy.ts`
- Modify: `src/app/interact/motion.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/interact/proof-spawn.ts`
- Modify: `src/app/interact/spawn.ts`
- Delete: app/macro files listed in the File Map.
- Test: surviving `tests/app/*.test.ts`
- Test: `tests/architecture/interaction-ownership.test.ts`

**Interfaces:**
- Consumes: final `ProofStep`, identity insertion, ref-store fold/unfold, exact matcher.
- Produces:

```ts
export function addIdentity(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
): Diagram

export type ActionDescriptor =
  | { readonly kind: 'erase'; readonly label: string }
  | { readonly kind: 'doubleCutWrap'; readonly label: string }
  | { readonly kind: 'doubleCutElim'; readonly label: string }
  | { readonly kind: 'identityInsert'; readonly label: string }
  | { readonly kind: 'identityContradiction'; readonly label: string }
  | { readonly kind: 'vacuousElim'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string; readonly needsTarget: true }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'relUnfold'; readonly label: string }
  | { readonly kind: 'relFold'; readonly label: string; readonly needsInput: 'relation' }
  | { readonly kind: 'citeTheorem'; readonly label: string; readonly name: string; readonly direction: 'forward' | 'reverse' }
```

- [ ] **Step 1: Build a zero-signature fixture authority**

`tests/fixtures/zero-signature.ts` exports:

```ts
export const UNARY = relSig([IOTA])
export const BINARY = relSig([IOTA, IOTA])
export function unaryDefinition(): DiagramWithBoundary
export function identityInCut(): Diagram
export function tinyTheory(): Theory
```

`tinyTheory` contains one relation definition and structural theorem only; it must not model Frege arithmetic or an Eq library.

- [ ] **Step 2: Rewrite app action/edit tests first**

Require:

- construction can place a conditional identity on outer-scoped wires;
- construction co-scoped identity immediately becomes a shared wire;
- action enumeration offers identity insertion only for at least two homogeneous visible wires at the correct orientation;
- action enumeration offers identity contradiction only for the exact asserted-
  identity/directly-negated-identity shape;
- convert, instantiate, abstract, and beta-eta inconsistent-cut actions are absent;
- unfold/fold still appear from the definition store.

Run:

```bash
npx vitest run tests/app/actions.test.ts tests/app/edit.test.ts
```

Expected: FAIL on the old action union and term-based construction.

- [ ] **Step 3: Remove computation/comprehension UI ownership**

Delete the named files and remove all imports, controllers, pending states, buttons, keyboard paths, debug fields, and CSS hooks for:

- term entry and closed-term introduction;
- fission/fusion;
- conversion/HNF tactics;
- comprehension substitution/abstraction;
- relation workspace;
- inconsistent-cut evidence search.

Keep identity contradiction as an exact structural action. It takes the selected
enclosing cut and already-identified node/child-cut IDs; it performs no search
over terms, normal forms, or certificates.

In `interact/motion.ts`, delete `conversionFrames`, term-grid morphing,
`conversionAnimation`, and the active-conversion state machine. Keep generic
whole-diagram transition ghosts, pulses, hover timing, motion speed, and their
tests; all proof steps now commit through that structural path.

Do not leave disabled menu items or compatibility event handlers.

- [ ] **Step 4: Rebuild copy planning for the three-node graph**

Copying in proof mode is ordinary iteration and is legal only when the target is in the source region's descendant cone. Copying in edit mode uses extract/splice directly. Node compilation has exactly:

```ts
switch (node.kind) {
  case 'atom': /* create atom on mapped head and arg wires */
  case 'ref': /* create ref with mapped ordered args */
  case 'identity': /* create one unordered identity on mapped incident wires */
}
```

Delete fission-tree discovery, term substitution, closed witnesses, K tricks, and body refusal branches. If a proof copy target is outside the iteration cone, return the real gate refusal; do not synthesize a different proof.

- [ ] **Step 5: Keep named definition authoring, but remove comprehension semantics**

`define.ts` continues extracting a `DiagramWithBoundary` and choosing canonical
boundary order. Exact fold inference uses only the structural graph-exploration
bound and reports graph exploration exhaustion or exact shape mismatch. Replace
“convert first if beta-eta” diagnostics with “the selection must match the
definition exactly.”

- [ ] **Step 6: Migrate library, session, replay, and shell tests**

Replace old `buildFregeTheory`/`buildLambdaTheory` fixtures with `tinyTheory`. Keep generic load/unload/conflict/session behavior. Remove assertions tied to `plusAssoc`, `fixedPoint`, `nat`, or generated examples.

- [ ] **Step 7: Run the app and architecture suites**

Run:

```bash
npx vitest run tests/app tests/interaction tests/architecture
```

Expected: PASS with the removed dedicated test files absent.

- [ ] **Step 8: Commit the app migration**

```bash
git add -- tests/fixtures/zero-signature.ts src/app/edit.ts src/app/actions.ts src/app/copy-planner.ts src/app/define.ts src/app/library.ts src/app/boot.ts src/app/persist.ts src/app/proof-front.ts src/app/shell.ts src/app/index.ts src/app/interact/construct.ts src/app/interact/copy.ts src/app/interact/motion.ts src/app/interact/moves.ts src/app/interact/proof-spawn.ts src/app/interact/spawn.ts
git add -- src/app/abstraction-matches.ts src/app/tactics.ts src/app/relation-transactions.ts src/app/relation-workspace.ts src/app/relation-workspace-draft.ts src/app/interact/closed-term-intro.ts src/app/interact/comprehension-macros.ts src/app/interact/fission.ts src/interaction/named-relation.ts app/test/relation-workspace.html app/test/relation-workspace.ts e2e/abstraction.spec.ts e2e/relation-workspace.spec.ts
git status --short
git diff --cached --name-only
git commit -m "refactor: migrate app interactions to zero-signature graphs"
```

Stage each modified surviving app/interaction/architecture test and each deleted
dedicated test with a literal filename before the cached-list check.

---

### Task 7: Replace lambda rendering with identity rendering

**Files:**
- Modify: `src/view/bend.ts`
- Modify: `src/view/engine.ts`
- Modify: `src/view/index.ts`
- Modify: `src/view/morph.ts`
- Modify: `src/view/optimize.ts`
- Modify: `src/view/paint.ts`
- Modify: `src/view/relax.ts`
- Delete: `src/view/tromp.ts`
- Modify: `tests/view/*.test.ts`
- Modify: `tests/physics/*.test.ts`
- Delete: `tests/view/tromp.test.ts`
- Modify: `demo/main.ts`
- Modify: `scripts/render-junction-gallery.ts`

**Interfaces:**
- Consumes: atom/ref/identity nodes and their exact port sets.
- Produces:

```ts
export type BodyKind = 'ref' | 'atom' | 'identity' | 'end' | 'anchor'
export function atomGeometry(arity: number): NodeGeometry
export function refGeometry(arity: number): NodeGeometry
export function identityGeometry(arity: number): NodeGeometry
```

- [ ] **Step 1: Replace view tests with three-node geometry expectations**

Require:

- an n-ary identity has n evenly spaced rim anchors keyed `i:0..i:n-1`;
- permuting semantic identity wires changes no disc radius or canonical paint class;
- atom head/args and ref args retain their existing geometry;
- no term occurrence, lambda arc, output anchor, fission target, or body geometry appears in debug state or paint output.

- [ ] **Step 2: Run the view slice and observe lambda dependencies**

Run:

```bash
npx vitest run tests/view tests/physics/paint.test.ts tests/physics/hittest.test.ts
```

Expected: FAIL because engine/bend/paint still import Tromp/term structures.

- [ ] **Step 3: Simplify geometry types and engine switches**

Delete `TermOccurrenceGeometry`, `PathSeg`, `bendGrid`, term output/exit anatomy, and `bodyGeometry`. Identity geometry is a neutral equality bridge: a small disc/bar with unordered radial anchors. Its storage indices locate anchors, but paint must not label or order them semantically.

```ts
case 'identity':
  return identityGeometry(node.arity)
```

- [ ] **Step 4: Remove fission morph/highlight paths**

Delete term-substructure occurrence interpolation and `fissionTargets` from proof-front debug output. Keep whole-node transition morphing for atom/ref/identity, wire routing, cuts, boundary slots, and fixed-frame behavior.

- [ ] **Step 5: Replace theory-based view/physics fixtures**

Use `tests/fixtures/zero-signature.ts` and locally composed high-valence atom/identity diagrams. Preserve physics assertions about routing, rest, dragging, fixed frames, and rendering ownership; only their semantic fixture changes.

- [ ] **Step 6: Replace the demo**

`demo/main.ts` builds one unary ref, one atom, and one identity inside a cut using `IOTA` and `relSig`. It imports no parser or term module.

- [ ] **Step 7: Migrate the junction-gallery script**

Change its base-sort helper from `TERM` to `IOTA`. Replace the
`bootFixture`/`plusComm` scene with an identity/ref scene from the shared
zero-signature fixture, while keeping its real settle-and-paint pipeline. The
script must import neither old theory builders nor any term module.

- [ ] **Step 8: Run view and physics suites**

Run:

```bash
npx vitest run tests/view
npm run test:physics
```

Expected: PASS.

- [ ] **Step 9: Commit rendering changes**

```bash
git add -- src/view/bend.ts src/view/engine.ts src/view/index.ts src/view/morph.ts src/view/optimize.ts src/view/paint.ts src/view/relax.ts src/view/tromp.ts src/app/proof-front.ts tests/view/tromp.test.ts demo/main.ts scripts/render-junction-gallery.ts
git status --short
git diff --cached --name-only
git commit -m "refactor: render identity nodes without lambda anatomy"
```

Stage each modified view and physics test with a literal filename before the
cached-list check.

---

### Task 8: Remove the old TypeScript theory corpus and generated artifacts

**Files:**
- Modify: `src/theories/index.ts`
- Modify: `package.json`
- Delete: `src/theories/frege.ts`
- Delete: `src/theories/lambda.ts`
- Delete: `src/theories/macros.ts`
- Delete: `tests/theories/battery.test.ts`
- Delete: `tests/theories/frege.test.ts`
- Delete: `tests/theories/lambda.test.ts`
- Delete: `tests/theories/macros.test.ts`
- Delete: `scripts/emit-theories.ts`
- Delete: `tests/scripts/emit-theories.test.ts`
- Delete: `examples/frege.json`
- Delete: `examples/lambda.json`
- Modify: remaining tests that import old theory builders
- Modify: `e2e/app.spec.ts`
- Modify: `e2e/construction.spec.ts`
- Modify: `e2e/contextual-copy.spec.ts`

**Interfaces:**
- Consumes: generic theory load/save plus the test-only `tinyTheory`.
- Produces: an empty `src/theories/index.ts` module awaiting Phase 2; no production bundled theory or generator.

- [ ] **Step 1: Change corpus-dependent tests to test-only fixtures**

Replace every import reported by:

```bash
rg -l 'buildFregeTheory|buildLambdaTheory|DerivationCursor' tests src scripts
```

with `tests/fixtures/zero-signature.ts`, unless the entire test is specifically about the deleted corpus. Corpus-specific tests are deleted.

- [ ] **Step 2: Run affected tests and observe corpus dependencies**

Run:

```bash
npx vitest run tests/app tests/view tests/physics tests/scripts
```

Expected: FAIL until all old builder imports and emitter expectations are removed.

- [ ] **Step 3: Delete the TypeScript theories and emitter**

Make `src/theories/index.ts` an empty module:

```ts
export {}
```

Remove `emit:theories`, `preapp`, and `pree2e` from `package.json`. Do not add placeholder relational Frege content.

- [ ] **Step 4: Update browser tests away from generated examples**

Delete E2E assertions whose product is lambda/comprehension behavior. For generic library-loading E2E, write the serialized `tinyTheory` to a test temp file inside the E2E setup and load that file. Keep construction, selection, proof-session, routing, and library error behavior that remains meaningful.

- [ ] **Step 5: Run ordinary and physics tests**

Run:

```bash
npm test
npm run test:physics
```

Expected: PASS.

- [ ] **Step 6: Commit corpus removal**

```bash
git add -- src/theories/index.ts package.json src/theories/frege.ts src/theories/lambda.ts src/theories/macros.ts scripts/emit-theories.ts tests/scripts/emit-theories.test.ts tests/theories/battery.test.ts tests/theories/frege.test.ts tests/theories/lambda.test.ts tests/theories/macros.test.ts examples/frege.json examples/lambda.json e2e/app.spec.ts e2e/construction.spec.ts e2e/contextual-copy.spec.ts
git status --short
git diff --cached --name-only
git commit -m "chore: remove lambda-based theory corpus"
```

Stage each additional corpus-import migration with a literal filename before the
cached-list check.

---

### Task 9: Add conformance guards, update docs, and run final gates

**Files:**
- Create: `tests/architecture/kernel-vocabulary.test.ts`
- Modify: `docs/kernel/canonicalization.md`
- Modify: any surviving TypeScript file found by the authority scans below.

**Interfaces:**
- Consumes: the completed Phase-1 repository state.
- Produces: executable negative evidence that the displaced model cannot return unnoticed.

- [ ] **Step 1: Write the architecture guard and see it fail on any residue**

The test must:

```ts
expect(sortedNodeKinds).toEqual(['atom', 'identity', 'ref'])
expect(existsSync('src/kernel/term')).toBe(false)
```

It must also scan `src/**/*.ts` and reject these semantic symbols:

```ts
[
  "kind: 'term'",
  "kind: 'body'",
  'TermDiagramNode',
  'ConversionCertificate',
  'NormalSeparationCertificate',
  'applyFusion',
  'applyFission',
  'applyCongruenceJoin',
  'applyHeadStrip',
  'applyInconsistentCutElim',
  'applyBodyAttach',
  'applyBodyDetach',
  'relCongruenceJoin',
]
```

Exclude prose specs/plans and `VisualProof/**`; Phase 3 owns Lean removal.

- [ ] **Step 2: Run the architecture test**

Run:

```bash
npx vitest run tests/architecture/kernel-vocabulary.test.ts
```

Expected: FAIL if any TypeScript authority or export remains; otherwise PASS.

- [ ] **Step 3: Update canonicalization documentation**

Document:

- the `iota | rel` signature grammar;
- exactly atom/ref/identity nodes;
- identity incidence indices as storage-only;
- sorted identity-neighbor refinement;
- three-rule identity fixpoint normalization and deterministic survivors;
- exact structural occurrence matching with only a graph-exploration bound;
- no beta-eta or semantic term comparison.

Delete descriptions of term shape keys, bodies, conversion fuel, and comprehension fingerprints.

- [ ] **Step 4: Run explicit absence checks**

Run:

```bash
test ! -d src/kernel/term
test ! -e tests/kernel/rules/uniqueness-representability.test.ts
test ! -e src/theories/frege.ts
test ! -e src/theories/lambda.ts
test ! -e src/theories/macros.ts
test ! -e src/app/interact/comprehension-macros.ts
test ! -e src/app/relation-workspace.ts
test ! -e src/view/tromp.ts
! rg -n "kind: 'term'|kind: 'body'|TermDiagramNode|ConversionCertificate|NormalSeparationCertificate|applyFusion|applyFission|applyCongruenceJoin|applyHeadStrip|applyInconsistentCutElim|applyBodyAttach|applyBodyDetach|relCongruenceJoin" src tests scripts
! rg -n '\bTERM\b|kind: .term.' src tests scripts
```

Expected: every command exits successfully with no matches.

- [ ] **Step 5: Prove the phase boundary**

Run:

```bash
git diff --name-only 2cdf7d7 -- VisualProof
```

Expected: no output. Also verify no relational Frege replacement, Eq library, reification library, reference HOL, or expressiveness files were added.

- [ ] **Step 6: Run all authoritative gates**

Run:

```bash
npm run typecheck
npm test
npm run test:all
```

Expected: all commands PASS. Repair in-scope failures and rerun until green.

- [ ] **Step 7: Inspect repository ownership and commit**

Run:

```bash
git status --short
git diff --check
git diff --stat 2cdf7d7
```

Expected: only Phase-1 task paths are dirty before the final commit; no whitespace errors.

```bash
git add -- tests/architecture/kernel-vocabulary.test.ts docs/kernel/canonicalization.md
git commit -m "test: enforce zero-signature kernel vocabulary"
git status --short
```

Expected: clean repository after the commit.

---

## Phase-1 Acceptance Checklist

- [ ] `Sig` is `iota | rel(Sig…)`; no base-sort `term` alias or codec exists.
- [ ] `DiagramNode` has exactly atom/ref/identity.
- [ ] Identity normalization Rules 1–3 run eagerly to a fixpoint and transport absorbed wire identities.
- [ ] Rule 4 uses ordinary insertion/erasure; Rule 5 is identity-aware iteration/deiteration with replayable gates.
- [ ] Rule 6 discharges the exact asserted-identity/directly-negated-identity
      contradiction with graph evidence only; it has no computation or
      distinctness oracle, and named disequality axioms are left to Phase 2.
- [ ] Repeated-boundary splice emits identity and never a projection node.
- [ ] Unfold/fold is ref-only and definition-store-sourced at both polarities.
- [ ] No primitive second-order instantiation or macro system exists.
- [ ] The TypeScript lambda layer, beta-eta rules/certificates, body/comprehension rules, old theories, generated examples, and projection scratch test are absent.
- [ ] Lean, relational Frege, Eq/reification libraries, and expressiveness work remain untouched for later phases.
- [ ] TypeScript, ordinary tests, and all tests pass.
- [ ] Every kept change is committed and `git status --short` is empty.
