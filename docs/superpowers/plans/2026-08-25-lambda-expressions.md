# Lambda Expressions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore nameless Lambda expressions, their complete interaction surface,
proof rules, formula support, 2D/3D rendering, and corrected structural reduction
animation to the signature-indexed-wire branch.

**Architecture:** A whole nameless term is stored in a signature-correct `term`
diagram node with one `IOTA` output and an ordered `IOTA` free-slot interface.
Dedicated TypeScript and Lean Lambda rule modules own conversion and the
free-variable/binary-identity equivalence. A shared structural motion plan drives
the established 2D Tromp painter and a planar 3D embedding.

**Tech Stack:** TypeScript 5, Vitest, Playwright, Canvas 2D, Three.js, Lean 4,
Lake.

**Spec:** `docs/superpowers/specs/2026-08-25-lambda-expressions-design.md`

## Global Constraints

- Base all work on `worktree-signature-indexed-wires` in the isolated
  `feature/lambda-expressions` worktree.
- The term calculus is nameless: bound indices and canonical numeric free slots
  are the only kernel references.
- A Lambda expression is one whole term. Definitions are relations.
- TypeScript Lambda rules live under `src/kernel/rules/lambda/`.
- Lean Lambda rules live in `VisualProof/Rule/Lambda.lean`, with proofs under
  `VisualProof/Rule/Soundness/Lambda/`.
- Right-click construction exposes an entry labeled `Lambda expression` and
  spawns every fresh term incidence with a unary `IOTA` identity cap.
- The 3D Lambda figure is unfilled planar line geometry perpendicular to its
  branch and uses the term-wire color in both themes.
- Reduction geometry, stage boundaries, and color lineage match
  `/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html`.
- Lean production theorems use theorem-driven RED/GREEN development and finish
  with no `sorry`.
- Commit every completed task after its focused tests pass.

---

## File structure

### TypeScript term and rules

- `src/kernel/term/*.ts` — nameless term data, parsing boundary, printing,
  serialization, substitution, reduction, normalization, paths, and certificates.
- `src/kernel/rules/lambda/conversion.ts` — beta-eta conversion and interface
  correspondence.
- `src/kernel/rules/lambda/free-variable-identity.ts` — the two-way term/identity
  graph rewrite.
- `src/kernel/rules/lambda/index.ts` — Lambda rule exports only.

### Diagram, formula, proof, and application

- `src/kernel/diagram/*` — term-node validation, canonical graph participation,
  subgraph operations, spawning, and JSON.
- `src/formula/*` — formula operands that may contain whole Lambda terms and
  formula-to-diagram translation.
- `src/kernel/proof/{step,json,compose,action}.ts` — replayable Lambda steps.
- `src/app/interact/*`, `src/app/tactics.ts`, and existing application owners —
  the main-branch interaction surface adapted to current identities and wires.

### Rendering and motion

- `src/view/tromp.ts` — term-to-rectilinear Tromp incidence grid.
- `src/view/lambda-motion.ts` — beta-step correspondence, stage timing, and color
  lineage shared by both renderers.
- `src/view/{bend,engine,paint}.ts` — circular 2D term-node geometry and paint.
- `src/view3d/lambda.ts` — local-plane 3D Lambda strokes.
- `src/view3d/{spec,layout,scene,render,pick,transition}.ts` — scene integration.

### Lean

- `VisualProof/Lambda/*.lean` — intrinsically scoped nameless Lambda calculus.
- `VisualProof/Diagram/*` and `VisualProof/Model.lean` — term items and their
  signature-indexed semantics.
- `VisualProof/Rule/Lambda.lean` — Lambda rule relations.
- `VisualProof/Rule/Soundness/Lambda/*.lean` — soundness proofs.
- `VisualProof/Rule/Step.lean`, `VisualProof/Rule/Soundness.lean`, and
  `VisualProof.lean` — public registration.

---

### Task 1: Restore the nameless TypeScript term calculus

**Files:**

- Create: `src/kernel/term/term.ts`
- Create: `src/kernel/term/parse.ts`
- Create: `src/kernel/term/print.ts`
- Create: `src/kernel/term/serialize.ts`
- Create: `src/kernel/term/path.ts`
- Create: `src/kernel/term/reduce.ts`
- Create: `src/kernel/term/hnf.ts`
- Create: `src/kernel/term/certificate.ts`
- Create: `src/kernel/term/convert.ts`
- Create: `src/kernel/term/index.ts`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`
- Create: `tests/kernel/term/*.test.ts`

**Interfaces:**

- Produces:

```ts
export type Term =
  | { readonly kind: 'bound'; readonly index: number }
  | { readonly kind: 'free'; readonly slot: number }
  | { readonly kind: 'lambda'; readonly body: Term }
  | { readonly kind: 'application'; readonly fn: Term; readonly argument: Term }

export type ParsedTerm = {
  readonly term: Term
  readonly freeIdentifiers: readonly string[]
}

export function parseTerm(source: string): ParsedTerm
export function printTerm(term: Term, freeIdentifiers?: readonly string[]): string
export function freeArity(term: Term): number
export function assertWellFormedTerm(term: Term, interfaceArity?: number): void
export function normalize(term: Term, fuel: number): NormalizeResult
export function headNormalize(term: Term, fuel: number): ReductionTrace
export function weakHeadNormalize(term: Term, fuel: number): ReductionTrace
export function checkConversion(
  left: Term,
  right: Term,
  certificate: ConversionCertificate,
): ConversionCheck
```

- Source authority: port the algorithms and coverage from `main:src/kernel/term/`,
  replacing `bvar/port/lam/app` storage with `bound/free/lambda/application` and
  assigning numeric free slots in first-occurrence parser order.

- [ ] **Step 1: Write failing structural and parser tests**

```ts
it('erases binder spelling and canonicalizes free identifiers by occurrence', () => {
  expect(parseTerm('\\x. x y').term).toEqual({
    kind: 'lambda',
    body: {
      kind: 'application',
      fn: { kind: 'bound', index: 0 },
      argument: { kind: 'free', slot: 0 },
    },
  })
  expect(parseTerm('\\z. z y').term).toEqual(parseTerm('\\x. x y').term)
  expect(parseTerm('\\x. x y').freeIdentifiers).toEqual(['y'])
})
```

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/kernel/term/parse.test.ts`

Expected: FAIL because `src/kernel/term/parse.ts` does not exist.

- [ ] **Step 3: Implement the structural type, smart constructors, parser, and printer**

Use a parser-local environment of binder identifiers. A bound identifier becomes
`{ kind: 'bound', index: depthFromInnermost }`; any other identifier receives the
first existing or next numeric free slot. Return parser spellings only in
`ParsedTerm.freeIdentifiers`.

- [ ] **Step 4: Add substitution, reduction, normalization, path, serialization,
and certificate RED tests**

Pin beta substitution, eta contraction, nested binders, capture avoidance,
Omega fuel exhaustion, path replay, injective serialization, and certificate
tamper rejection using the corresponding `main:tests/kernel/term/` cases.

- [ ] **Step 5: Implement the remaining term modules and GREEN the suite**

Remove the term subsystem, certificate types, term-module imports, and term test
paths from the existing anti-Lambda exclusions in
`tests/architecture/kernel-vocabulary.test.ts`. Do not add a replacement source
scanner.

Run:

```bash
npx vitest run tests/kernel/term tests/architecture/kernel-vocabulary.test.ts
npm run typecheck
```

Expected: all term tests PASS and `tsc --noEmit` exits 0.

- [ ] **Step 6: Commit**

```bash
git add src/kernel/term tests/kernel/term tests/architecture/kernel-vocabulary.test.ts
git commit -m "feat(kernel): restore nameless lambda terms"
```

---

### Task 2: Add term nodes to signature-indexed diagrams

**Files:**

- Modify: `src/kernel/diagram/diagram.ts`
- Modify: `src/kernel/diagram/builder.ts`
- Modify: `src/kernel/diagram/spawn.ts`
- Modify: `src/kernel/diagram/json.ts`
- Modify: `src/kernel/diagram/canonical/refine.ts`
- Modify: `src/kernel/diagram/canonical/iso.ts`
- Modify: `src/kernel/diagram/canonical/wire-order.ts`
- Modify: `src/kernel/diagram/subgraph/extract.ts`
- Modify: `src/kernel/diagram/subgraph/match.ts`
- Modify: `src/kernel/diagram/subgraph/splice.ts`
- Modify: `src/kernel/diagram/subgraph/occurrence-certificate.ts`
- Modify: `src/app/edit.ts`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`
- Test: `tests/kernel/diagram/term-node.test.ts`
- Test: existing `tests/kernel/diagram/{json,iso,match,extract,splice,wellformed}.test.ts`

**Interfaces:**

- Consumes: `Term`, `freeArity`, and `assertWellFormedTerm` from Task 1.
- Produces:

```ts
export type TermDiagramNode = {
  readonly kind: 'term'
  readonly region: RegionId
  readonly term: Term
  readonly freeArity: number
}

// Added to Port:
| { readonly kind: 'output' }
| { readonly kind: 'free'; readonly index: number }

export function spawnTermNode(
  diagram: Diagram,
  region: RegionId,
  term: Term,
  interfaceArity: number,
  reservation?: IdReservation,
): { readonly diagram: Diagram; readonly node: NodeId; readonly wires: readonly WireId[] }
```

- [ ] **Step 1: Write the term-node invariant RED test**

```ts
it('requires one IOTA output and one IOTA port per numeric free slot', () => {
  const term = parseTerm('\\x. x y').term
  const built = termNodeFixture(term, 1)
  expect(requiredPorts(built.diagram.nodes[built.node]!)).toEqual([
    { kind: 'output' },
    { kind: 'free', index: 0 },
  ])
  expect(built.portSignatures).toEqual([IOTA, IOTA])
})
```

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/kernel/diagram/term-node.test.ts`

Expected: FAIL because `DiagramNode` and `Port` lack the new variants.

- [ ] **Step 3: Implement diagram validation and construction**

Extend every exhaustive node/port switch. Validate `freeArity` as a nonnegative
safe integer, call `assertWellFormedTerm(node.term, node.freeArity)`, and make
`portSig` return `IOTA` for both term port kinds. Add `term` to the exhaustive
`DiagramNode['kind']` fixture and remove its former prohibition.

- [ ] **Step 4: Make term structure canonical graph content**

Include injective term serialization and `freeArity` in initial node color,
canonical serialization, isomorphism comparison, occurrence certificates, and
matching. Keep free ports ordered by numeric index.

- [ ] **Step 5: GREEN all diagram transformations**

Add round-trip cases proving extraction and splicing retain the whole term and
each external attachment. Run:

```bash
npx vitest run tests/kernel/diagram tests/architecture/kernel-vocabulary.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/kernel/diagram src/app/edit.ts tests/kernel/diagram tests/architecture/kernel-vocabulary.test.ts
git commit -m "feat(diagram): add signature-indexed term nodes"
```

---

### Task 3: Extend formula entry with Lambda operands

**Files:**

- Modify: `src/formula/syntax.ts`
- Modify: `src/formula/parse.ts`
- Modify: `src/formula/diagram.ts`
- Modify: `src/formula/index.ts`
- Modify: `src/app/formula-entry.ts`
- Modify: `src/app/shell.ts`
- Modify: `app/style.css`
- Test: `tests/formula/parse.test.ts`
- Test: `tests/formula/diagram.test.ts`
- Test: `tests/app/formula-entry.test.ts`

**Interfaces:**

- Consumes: `ParsedTerm` and term-node diagram construction.
- Produces:

```ts
export type FormulaOperand =
  | { readonly kind: 'reference'; readonly name: string; readonly span: SourceSpan }
  | { readonly kind: 'term'; readonly parsed: ParsedTerm; readonly span: SourceSpan }

// Atom.args and Equality.operands become readonly FormulaOperand[].
```

- [ ] **Step 1: Write formula parser RED tests**

```ts
it('accepts lambda terms as proposition operands', () => {
  expect(parseFormula('forall P : i -> o. P(λx. x)').kind).toBe('quantifier')
  expect(parseFormula('(\\x. x) = (\\y. y)').kind).toBe('equality')
})
```

Also assert that the two equality terms have identical nameless `Term` values.

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: FAIL at tokenization or operand parsing on `λ` and `\\`.

- [ ] **Step 3: Implement operand parsing and validation**

Add `lambda` to `FormulaUnicodeTokenKind`, lex `\\` as the same token, and parse
term operands through balanced formula delimiters. A bare identifier remains a
`reference`; abstraction or application produces a `term`. Require every parsed
free identifier to resolve to an enclosing `IOTA` binding.

- [ ] **Step 4: Implement diagram translation**

For a bare individual reference, return its bound wire. For a term operand, create
one term node, attach each numeric free port using
`parsed.freeIdentifiers[index]`, and return its output wire to the atom or identity
constructor. Ensure every completed wire still has two ends.

- [ ] **Step 5: Add the palette symbol and GREEN**

The formula palette button inserts `λ`. Run:

```bash
npx vitest run tests/formula tests/app/formula-entry.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/formula src/app/formula-entry.ts src/app/shell.ts app/style.css tests/formula tests/app/formula-entry.test.ts
git commit -m "feat(formula): support lambda term operands"
```

---

### Task 4: Implement dedicated TypeScript Lambda rules

**Files:**

- Create: `src/kernel/rules/lambda/correspondence.ts`
- Create: `src/kernel/rules/lambda/conversion.ts`
- Create: `src/kernel/rules/lambda/free-variable-identity.ts`
- Create: `src/kernel/rules/lambda/index.ts`
- Modify: `src/kernel/rules/access.ts`
- Modify: `src/kernel/rules/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/kernel/proof/action.ts`
- Test: `tests/kernel/rules/lambda-conversion.test.ts`
- Test: `tests/kernel/rules/lambda-free-variable-identity.test.ts`
- Test: existing `tests/kernel/proof/{step,json,compose,action}.test.ts`

**Interfaces:**

- Produces:

```ts
export type SlotCorrespondence = {
  readonly commonArity: number
  readonly left: readonly number[]
  readonly right: readonly number[]
}

export function applyLambdaConversion(
  diagram: Diagram,
  node: NodeId,
  term: Term,
  correspondence: SlotCorrespondence,
  certificate: ConversionCertificate,
  attachments?: Readonly<Record<number, WireId>>,
): Diagram

export type FreeVariableIdentityAction =
  | { readonly direction: 'toIdentity'; readonly node: NodeId }
  | { readonly direction: 'toTerm'; readonly node: NodeId; readonly outputPort: 0 | 1 }

export function applyFreeVariableIdentity(
  diagram: Diagram,
  action: FreeVariableIdentityAction,
): Diagram
```

- Adds replayable proof-step variants `lambdaConversion` and
  `lambdaFreeVariableIdentity`.

- [ ] **Step 1: Write conversion and identity RED tests**

```ts
it('round-trips a free-slot term node through binary IOTA identity', () => {
  const asIdentity = applyFreeVariableIdentity(source, {
    direction: 'toIdentity', node: 'term',
  })
  expect(asIdentity.nodes.term?.kind).toBe('identity')
  const restored = applyFreeVariableIdentity(asIdentity, {
    direction: 'toTerm', node: 'term', outputPort: 0,
  })
  expect(canonicalKey(restored)).toBe(canonicalKey(source))
})
```

Test both reverse orientations, repeated-wire incidences, non-`IOTA` refusal,
nonbinary refusal, non-free-only term refusal, conversion certificate replay, and
new/free interface attachments.

- [ ] **Step 2: Run RED**

Run:

```bash
npx vitest run tests/kernel/rules/lambda-conversion.test.ts tests/kernel/rules/lambda-free-variable-identity.test.ts
```

Expected: FAIL because the dedicated rule modules do not exist.

- [ ] **Step 3: Implement exact node surgery**

For `toIdentity`, locate the output and free-slot wire owners, replace the term
node in place with `{ kind: 'identity', sig: IOTA, arity: 2 }`, and attach storage
ports `0` and `1` to those owners. Reverse this operation with the selected
identity port as output. Build through `mkDiagram` so derived scope and two-end
validation remain authoritative.

- [ ] **Step 4: Implement conversion and replay registration**

Port main's conversion-certificate checking and interface-column surgery to
numeric slots. Add exhaustive JSON encode/decode and composition remapping for the
two proof-step variants.

- [ ] **Step 5: GREEN focused and proof suites**

```bash
npx vitest run tests/kernel/rules/lambda-conversion.test.ts tests/kernel/rules/lambda-free-variable-identity.test.ts tests/kernel/proof
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/kernel/rules/lambda src/kernel/rules/access.ts src/kernel/rules/index.ts src/kernel/proof tests/kernel/rules tests/kernel/proof
git commit -m "feat(rules): add lambda conversions and identity bridge"
```

---

### Task 5: Restore circular 2D Lambda geometry

**Files:**

- Create: `src/view/tromp.ts`
- Modify: `src/view/bend.ts`
- Modify: `src/view/engine.ts`
- Modify: `src/view/paint.ts`
- Modify: `src/view/index.ts`
- Modify: `src/app/hittest.ts`
- Test: `tests/view/tromp.test.ts`
- Test: `tests/view/bend.test.ts`
- Test: `tests/view/engine.test.ts`
- Test: `tests/view/paint.test.ts`
- Test: `tests/app/hittest.test.ts`

**Interfaces:**

- Produces `trompGrid(term: Term): TrompGrid` and
  `termGeometry(term: Term): NodeGeometry` with numeric free-port anchors,
  structural occurrence ownership, exit geometry, and circular arcs.

- [ ] **Step 1: Write geometry RED tests**

Port the main-branch `trompGrid` fixture tests and assert that alpha-equivalent
inputs produce exactly equal geometry. Assert output/free anchors use `out` and
`f:<index>` storage keys.

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/view/tromp.test.ts tests/view/bend.test.ts`

Expected: FAIL because `trompGrid` and term geometry are absent.

- [ ] **Step 3: Port and adapt Tromp layout**

Port `main:src/view/tromp.ts`, replacing name-keyed rails with slot-keyed rails
and ownership paths with the Task 1 path type. Extend `NodeGeometry` with the
term exit arc/line and structural occurrence geometry used for hit testing.

- [ ] **Step 4: Integrate engine, paint, and hit testing**

Use `termGeometry` for `term` bodies, restore term anatomy scaling, paint every
internal and exit stroke with `Theme.wire`, and select the node/subterm from the
same occurrence geometry used by paint.

- [ ] **Step 5: GREEN**

```bash
npx vitest run tests/view tests/app/hittest.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/view src/app/hittest.ts tests/view tests/app/hittest.test.ts
git commit -m "feat(view): restore circular lambda diagrams"
```

---

### Task 6: Restore Lambda spawning and conversion interactions

**Files:**

- Create: `src/kernel/rules/lambda/spawn.ts`
- Create: `src/app/tactics.ts`
- Modify: `src/kernel/rules/lambda/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/app/interact/spawn.ts`
- Modify: `src/app/interact/proof-spawn.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/replay.ts`
- Modify: `src/app/persist.ts`
- Test: `tests/app/spawn.test.ts`
- Test: `tests/app/moves.test.ts`
- Test: `tests/app/actions.test.ts`
- Test: `tests/app/replay.test.ts`
- Test: `tests/app/persist.test.ts`

**Interfaces:**

- Produces `proofTermSpawnStep(source, region)`, `convertToNormal`,
  `convertToHeadNormal`, and `convertToWeakHeadNormal`.
- Adds a replayable `lambdaTermSpawn` proof step owned by
  `src/kernel/rules/lambda/spawn.ts`.
- The spawn callback receives `ParsedTerm` and commits a replayable term-spawn
  action whose result contains unary caps on output and every free slot.

- [ ] **Step 1: Write right-click and cap RED tests**

```ts
it('offers Lambda expression and caps every spawned incidence', () => {
  cascade.open(invocation, relations, [])
  clickRow(host, 'Lambda expression')
  submitText(host, '\\x. x y')
  const node = onlyTermNode(diagram())
  expect(incidentUnaryIdentityCount(diagram(), node)).toBe(2)
})
```

Assert captured pointer placement, parse refusal, closed-term output cap,
open-term free caps, undo, replay, and persistence round trip.

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/app/spawn.test.ts tests/app/moves.test.ts`

Expected: FAIL because the menu and term proof actions are absent.

- [ ] **Step 3: Implement spawning**

Port `SpawnCascade` term mode from main, change the row label to exactly
`Lambda expression`, and create term node plus unary identity caps in one edit or
proof action. `applyLambdaTermSpawn` owns the existing forward/backward spawn
polarity check and calls `spawnTermNode`. Placement uses the term node id, never a
cap id. Add exact JSON and composition cases for `lambdaTermSpawn`.

- [ ] **Step 4: Implement conversion actions**

Restore double-click normalization and the context rows for normal, head-normal,
weak-head-normal, and custom target conversion. All committed changes use the
Task 4 replay steps and checked certificates.

- [ ] **Step 5: GREEN**

```bash
npx vitest run tests/app/spawn.test.ts tests/app/moves.test.ts tests/app/actions.test.ts tests/app/replay.test.ts tests/app/persist.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/kernel/rules/lambda/spawn.ts src/kernel/rules/lambda/index.ts src/kernel/proof src/app tests/app
git commit -m "feat(app): restore lambda spawning and conversion"
```

---

### Task 7: Restore the remaining term interaction surface

**Files:**

- Create: `src/kernel/rules/lambda/fission.ts`
- Create: `src/kernel/rules/lambda/congruence.ts`
- Create: `src/kernel/rules/lambda/head-strip.ts`
- Create: `src/kernel/rules/lambda/anchored-wire.ts`
- Modify: `src/kernel/rules/lambda/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Create: `src/app/interact/fission.ts`
- Modify: `src/app/interact/connection.ts`
- Modify: `src/app/interact/copy.ts`
- Modify: `src/app/interact/copy-view.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/copy-planner.ts`
- Modify: `src/app/edit.ts`
- Modify: `src/app/hit-selection.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/shell.ts`
- Test: `tests/app/term-interactions.test.ts`
- Test: `tests/kernel/rules/lambda-fission.test.ts`
- Test: `tests/kernel/rules/lambda-congruence.test.ts`
- Test: `tests/kernel/rules/lambda-head-strip.test.ts`
- Test: `tests/kernel/rules/lambda-anchored-wire.test.ts`
- Test: existing copy, connection, edit, and proof-front tests.

**Interfaces:**

- Consumes term occurrence paths from Task 1 and occurrence geometry from Task 5.
- Produces the main-branch selection, subterm fission preview/commit, copying,
  output/free-port connection, and proof-front behavior for term nodes.
- Adds replayable `lambdaFission`, `lambdaFusion`, `lambdaCongruenceJoin`,
  `lambdaHeadStrip`, `lambdaAnchoredWireSplit`, and
  `lambdaAnchoredWireContract` proof steps.

- [ ] **Step 1: Write interaction-parity RED tests**

Port the main rule tests first. Exercise selecting a nested subterm, dragging a
fission preview, committing the selected whole subterm, fusing the result,
copying a term node with all external incidences, congruence joining convertible
outputs, head stripping equal heads, anchored-wire split/contract, and connecting
term output/free-slot wires.

- [ ] **Step 2: Run RED**

Run:

```bash
npx vitest run tests/kernel/rules/lambda-fission.test.ts tests/kernel/rules/lambda-congruence.test.ts tests/kernel/rules/lambda-head-strip.test.ts tests/kernel/rules/lambda-anchored-wire.test.ts tests/app/term-interactions.test.ts
```

Expected: FAIL because term-specific fission and connection paths are absent.

- [ ] **Step 3: Port the main term rules into the dedicated Lambda owner**

Adapt `main`'s fusion/fission, congruence, head-strip, and anchored-wire algorithms
to numeric free slots, signature-indexed wires, derived scope, unary identities,
and the two-end floor. Keep their graph rewrites and replay codecs under the
Lambda module paths listed above.

- [ ] **Step 4: Port the main interaction controllers**

Port `main:src/app/interact/fission.ts` and the term branches of copy, connection,
moves, proof-front, and shell. Replace string free-port lookups with numeric
`{ kind: 'free', index }` ports and route every proof change through the dedicated
Lambda proof steps from Tasks 4, 6, and this task.

- [ ] **Step 5: GREEN all affected rule and application suites**

```bash
npx vitest run tests/kernel/rules/lambda-fission.test.ts tests/kernel/rules/lambda-congruence.test.ts tests/kernel/rules/lambda-head-strip.test.ts tests/kernel/rules/lambda-anchored-wire.test.ts tests/app/term-interactions.test.ts tests/app/copy-interaction.test.ts tests/app/copy-planner.test.ts tests/app/connection.test.ts tests/app/edit.test.ts tests/app/proof-front.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/kernel/rules/lambda src/kernel/proof src/app tests/kernel/rules tests/app
git commit -m "feat(app): restore complete term interactions"
```

---

### Task 8: Implement corrected structural reduction motion and color lineage

**Files:**

- Create: `src/view/lambda-motion.ts`
- Modify: `src/app/interact/motion.ts`
- Modify: `src/view/morph.ts`
- Modify: `src/view/paint.ts`
- Test: `tests/view/lambda-motion.test.ts`
- Test: `tests/app/motion.test.ts`

**Interfaces:**

- Produces:

```ts
export type LambdaPhase =
  | 'identify' | 'duplicate' | 'discard' | 'make-space'
  | 'substitute' | 'cleanup' | 'settle'

export type LambdaStrokeFrame = {
  readonly phase: LambdaPhase
  readonly strokes: readonly LambdaStroke[]
  readonly sockets: readonly LambdaSocket[]
}

export function planBetaMotion(source: Term, step: ReductionStep): LambdaMotionPlan
export function sampleBetaMotion(plan: LambdaMotionPlan, progress: number, baseColor: string): LambdaStrokeFrame
```

- [ ] **Step 1: Write stage and lineage RED tests**

For one-use, duplication, deletion, nested-binder, and capture-avoidance terms,
assert phase boundaries from the spec, exact copy count, complete copied stroke
sets, persistent junction destinations, and hue identity at samples immediately
before/after every boundary.

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/view/lambda-motion.test.ts`

Expected: FAIL because the shared motion planner is absent.

- [ ] **Step 3: Port the corrected-demo correspondence algorithm**

Port semantic node identities, origin keys, source/target junction offers,
introduced-copy classification, parking geometry, socket docking, binder-stem
retraction, and stage timing from the corrected HTML. Throw on unclassified
consumed strokes or introduced non-copy strokes.

- [ ] **Step 4: Port color tracking**

Use redex `#f06aa7`, argument `#f0bd55`, and copy hues
`#58ddcf`, `#6da8ff`, `#c084fc`, `#fb7185`, `#34d399`, mixed from and back to the
renderer-supplied term-wire base color at the corrected stages.

- [ ] **Step 5: Integrate app motion and GREEN**

Ensure scrub, play, step, cancel, and history transitions sample the same plan.
Run:

```bash
npx vitest run tests/view/lambda-motion.test.ts tests/app/motion.test.ts
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/view/lambda-motion.ts src/view/morph.ts src/view/paint.ts src/app/interact/motion.ts tests/view/lambda-motion.test.ts tests/app/motion.test.ts
git commit -m "feat(view): animate structural lambda reduction"
```

---

### Task 9: Render and animate Lambda diagrams in 3D

**Files:**

- Create: `src/view3d/lambda.ts`
- Modify: `src/view3d/spec.ts`
- Modify: `src/view3d/layout.ts`
- Modify: `src/view3d/scene.ts`
- Modify: `src/view3d/render.ts`
- Modify: `src/view3d/pick.ts`
- Modify: `src/view3d/transition.ts`
- Modify: `src/view3d/index.ts`
- Test: `tests/view3d/lambda.test.ts`
- Test: existing `tests/view3d/{spec,layout,scene,pick,transition}.test.ts`

**Interfaces:**

- Produces a Lambda scene entity containing only stroke polylines and ownership
  metadata. `lambdaPlane(branchTangent)` returns an orthonormal local basis whose
  normal is parallel to the branch tangent.

- [ ] **Step 1: Write planar-geometry RED tests**

Assert every point of a Lambda entity lies in one plane, the plane normal is
parallel to the incident branch direction, no mesh/fill entity exists, the static
stroke graph matches 2D `termGeometry`, and light/dark base strokes equal the
corresponding term-wire color.

- [ ] **Step 2: Run RED**

Run: `npx vitest run tests/view3d/lambda.test.ts`

Expected: FAIL because the 3D Lambda entity does not exist.

- [ ] **Step 3: Implement the local-plane embedding**

Map each 2D Lambda stroke point `(x, y)` to
`center + x * plane.right + y * plane.up`. Build line/tube render objects only.
Attach term node, subterm path, and source stroke ids for picking and transitions.

- [ ] **Step 4: Integrate layout, scene, picking, and transitions**

Give term nodes clearance from their planar outline, connect IOTA strands to the
embedded output/free anchors, include Lambda strokes in bounds and focus, and
sample Task 8 motion/color frames in `transition.ts`.

- [ ] **Step 5: GREEN**

```bash
npx vitest run tests/view3d
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/view3d tests/view3d
git commit -m "feat(view3d): render planar lambda diagrams"
```

---

### Task 10: Restore Lean's intrinsically scoped Lambda foundation

**Files:**

- Create: `VisualProof/Lambda/Syntax.lean`
- Create: `VisualProof/Lambda/Rename.lean`
- Create: `VisualProof/Lambda/Substitute.lean`
- Create: `VisualProof/Lambda/Reduction.lean`
- Create: `VisualProof/Lambda/Normalize.lean`
- Create: `VisualProof/Lambda/Quotient.lean`
- Create: `VisualProof/Lambda/Certificate.lean`
- Create: `VisualProof/Lambda/NormalSeparation.lean`
- Modify: `VisualProof/Model.lean`

**Interfaces:**

- Produces `Lambda.TermCore free bound`, `Lambda.BetaEta`, conversion
  certificates, `Lambda.LambdaModel`, and `Model.toLambdaModel`.
- `Model` extends a lawful Lambda model and retains `Nonempty Carrier`.

- [ ] **Step 1: Restore complete definitions and compile the foundation**

Restore the eight `VisualProof/Lambda/` modules from the last main-branch versions,
preserving intrinsically scoped `Fin` bound variables and positional `Fin` free
ports. Adapt imports only; do not add a second term representation.

Run:

```bash
lake env lean VisualProof/Lambda/NormalSeparation.lean
```

Expected: PASS. This is structural setup and does not require a synthetic RED
theorem.

- [ ] **Step 2: Extend the semantic model**

Use:

```lean
structure Model extends Lambda.LambdaModel where
  nonempty : Nonempty Carrier
```

Update existing field projections through `model.toLambdaModel` only where Lean
cannot infer the inherited projection.

- [ ] **Step 3: Validate the existing formal calculus**

```bash
lake build
rg -n '\bsorry\b' VisualProof --glob '*.lean'
```

Expected: build PASS and no `sorry`.

- [ ] **Step 4: Commit**

```bash
git add VisualProof/Lambda VisualProof/Model.lean
git commit -m "feat(lean): restore nameless lambda calculus"
```

---

### Task 11: Add Lambda term items to Lean diagrams

**Files:**

- Modify: `VisualProof/Diagram/Core.lean`
- Modify: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/Context.lean`
- Modify: `VisualProof/Diagram/Boundary.lean`
- Modify: `VisualProof/Diagram/Scope/*.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/Semantics/*.lean`
- Modify: affected `VisualProof/Rule/WirePrimitive/Transform.lean` recursors

**Interfaces:**

- Adds:

```lean
| term {wires : List Sig} (output : Var wires .iota)
    (freeArity : Nat) (ports : Fin freeArity → Var wires .iota)
    (term : Lambda.Term 0 (Fin freeArity)) : Item wires
```

- Denotation is:

```lean
env.lookup output =
  model.eval term (fun slot => env.lookup (ports slot))
```

- [ ] **Step 1: Complete the new constructor's dependency closure**

Add the constructor and exhaustive cases for renaming, wire counting,
canonicality, two-endedness, context filling, isomorphism, and structural
transform recursors. The term maps its free `Fin` slots through `ports`; wire
renaming changes output/ports and leaves the term unchanged.

- [ ] **Step 2: State the owning semantic theorem in RED**

```lean
@[simp] theorem denoteItem_term
    (model : Model) (env : Values model wires)
    (output : Var wires .iota) (ports : Fin freeArity → Var wires .iota)
    (term : Lambda.Term 0 (Fin freeArity)) :
    denoteItem model env (.term output freeArity ports term) ↔
      env.lookup output =
        model.eval term (fun slot => env.lookup (ports slot)) := by
  sorry
```

Run: `lake env lean VisualProof/Diagram/Semantics.lean`

Expected: PASS with this theorem as the only owning proof admission.

- [ ] **Step 3: GREEN the semantic theorem and transport lemmas**

Replace the proof with `rfl`, then complete the new constructor cases in semantic
renaming, isomorphism, context, and algebra theorems.

- [ ] **Step 4: Validate**

```bash
lake build
rg -n '\bsorry\b' VisualProof --glob '*.lean'
```

Expected: PASS and no `sorry`.

- [ ] **Step 5: Commit**

```bash
git add VisualProof/Diagram VisualProof/Rule/WirePrimitive/Transform.lean
git commit -m "feat(lean): add lambda term diagram items"
```

---

### Task 12: Prove Lean Lambda rules and register Step evidence

**Files:**

- Create: `VisualProof/Rule/Lambda.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/Conversion.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/FreeVariableIdentity.lean`
- Create: `VisualProof/Rule/Soundness/Lambda.lean`
- Create: `VisualProof/Rule/Executable/Lambda.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Executable/Step.lean`
- Modify: `VisualProof/Rule/Executable.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces `Rule.Lambda.Conversion`, `Rule.Lambda.FreeVariableIdentity`, their
  contextual public relations, `iso` transport, and soundness theorems.
- Adds `lambdaConversion` and `lambdaFreeVariableIdentity` constructors to
  `Step.Evidence`.
- Produces source-indexed forward/backward indices and exact runners for both
  relations.

- [ ] **Step 1: Define complete rule witnesses**

`Conversion.Local` replaces one `.term` item with another whose terms are
`Lambda.BetaEta` under a covered common positional interface. The
free-variable/identity relation replaces exactly one `.term output 1 ports
(.port 0)` with `.identity .iota 2` on `output` and `ports 0`, or conversely.
Lift both through `Contextual` and implement their isomorphism transports.

- [ ] **Step 2: State conversion soundness RED theorem**

```lean
theorem Conversion.sound (step : Conversion source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  sorry
```

Run: `lake env lean VisualProof/Rule/Soundness/Lambda/Conversion.lean`.

Expected: PASS with the production theorem admission.

- [ ] **Step 3: GREEN conversion soundness**

Use the correspondence environment lemma, `model.betaEta_sound`, and contextual
denotation transport to replace the admission.

- [ ] **Step 4: State and GREEN free-variable identity soundness**

The local semantic proof reduces both sides to equality of the same two
`IOTA` values using `model.eval_port`. Lift it with contextual soundness.

- [ ] **Step 5: Register evidence and prove aggregate soundness**

Add both evidence constructors, cases in `Evidence.iso`, smart constructors, and
cases in `Step.sound`. Import the public modules from `VisualProof.lean`.

- [ ] **Step 6: Implement exact source-indexed runners**

Use the existing `Executable.ComputedDirected` family construction. Conversion
indices carry the selected occurrence, replacement positional term, covered
interface correspondence, and `BetaEta` evidence. Free-variable identity indices
carry the selected occurrence and, in the identity-to-term direction, the chosen
output incidence. Prove `forward_exact` and `backward_exact` for both and add their
cases to `Step.Evidence.ForwardExecutable`, `BackwardExecutable`, and the aggregate
execution-completeness theorems.

- [ ] **Step 7: Validate**

```bash
lake build
rg -n '\bsorry\b' VisualProof --glob '*.lean'
```

Expected: PASS and no `sorry`.

- [ ] **Step 8: Commit**

```bash
git add VisualProof/Rule/Lambda.lean VisualProof/Rule/Soundness/Lambda VisualProof/Rule/Soundness/Lambda.lean VisualProof/Rule/Executable/Lambda.lean VisualProof/Rule/Step.lean VisualProof/Rule/Soundness.lean VisualProof/Rule/Executable/Step.lean VisualProof/Rule/Executable.lean VisualProof.lean
git commit -m "feat(lean): prove lambda rule soundness"
```

---

### Task 13: Restore the remaining Lean Lambda rule surface

**Files:**

- Create: `VisualProof/Rule/Lambda/Spawn.lean`
- Create: `VisualProof/Rule/Lambda/Fission.lean`
- Create: `VisualProof/Rule/Lambda/Congruence.lean`
- Create: `VisualProof/Rule/Lambda/HeadStrip.lean`
- Create: `VisualProof/Rule/Lambda/AnchoredWire.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/Spawn.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/Fission.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/Congruence.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/HeadStrip.lean`
- Create: `VisualProof/Rule/Soundness/Lambda/AnchoredWire.lean`
- Modify: `VisualProof/Rule/Lambda.lean`
- Modify: `VisualProof/Rule/Soundness/Lambda.lean`
- Modify: `VisualProof/Rule/Executable/Lambda.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Executable/Step.lean`

**Interfaces:**

- Produces the formal relations corresponding exactly to Task 6 spawning and Task
  7 fission/fusion, congruence, head stripping, and anchored-wire operations.
- Registers each replayable Lambda proof operation in `Step.Evidence`, aggregate
  soundness, and exact source-indexed execution.

- [ ] **Step 1: Define the rule relations from current diagram objects**

Port the statements from the last main-branch Lambda formalization, replacing the
former untyped concrete graph objects with the current `.term` item, recursive
signature contexts, derived wire scope, and identity items. Put each relation in
its listed Lambda module and import them from the Lambda aggregator.

- [ ] **Step 2: RED and GREEN spawn soundness**

State `Lambda.Spawn.sound` over `denoteOpen`, compile with its proof as `sorry`,
then prove it by choosing the spawned output/free values through the model's
inhabited carrier and `model.eval`. Complete the owning theorem before starting
the next rule.

- [ ] **Step 3: RED and GREEN fission/fusion soundness**

State the bidirectional theorem for the exact split/fused endpoints. Prove it from
capture-avoiding term substitution, the equality introduced between the source
subterm output and replacement port, and contextual denotation transport.

- [ ] **Step 4: RED and GREEN congruence and head-strip soundness**

For congruence, use the covered common-interface environment and beta-eta
soundness. For head stripping, use equality of the common rigid head and preserve
the ordered argument equations exposed by the rule.

- [ ] **Step 5: RED and GREEN anchored-wire soundness**

Prove split and contract as the two directions of the same equality-preserving
term-output factorization, including the derived-scope and two-ended endpoint
conditions in the relation witness.

- [ ] **Step 6: Register exact execution and aggregate evidence**

Add evidence, isomorphism, soundness, `ForwardExecutable`, `BackwardExecutable`,
and execution-completeness cases for every relation. Source-indexed runner inputs
carry the explicit term, path, certificate, correspondence, occurrence, endpoint
partition, and destination required by their relation witnesses.

- [ ] **Step 7: Validate**

```bash
lake build
rg -n '\bsorry\b' VisualProof --glob '*.lean'
```

Expected: PASS and no `sorry`.

- [ ] **Step 8: Commit**

```bash
git add VisualProof/Rule/Lambda VisualProof/Rule/Lambda.lean VisualProof/Rule/Soundness/Lambda VisualProof/Rule/Soundness/Lambda.lean VisualProof/Rule/Executable/Lambda.lean VisualProof/Rule/Step.lean VisualProof/Rule/Soundness.lean VisualProof/Rule/Executable/Step.lean
git commit -m "feat(lean): restore lambda interaction rules"
```

---

### Task 14: End-to-end interaction and persistence coverage

**Files:**

- Create: `examples/lambda.json`
- Modify: `e2e/construction.spec.ts`
- Modify: `e2e/interaction.spec.ts`
- Modify: `e2e/view3.spec.ts`
- Modify: `tests/app/pipeline.test.ts`
- Modify: `tests/app/session.test.ts`
- Modify: `tests/app/proof-snapshot.test.ts`
- Modify: `scripts/emit-theories.ts` only if its exhaustive proof-step switch
  requires the Lambda cases.

**Interfaces:**

- Consumes the complete TypeScript and Lean surface.
- Produces a loadable Lambda example and browser-level proof-mode coverage.

- [ ] **Step 1: Write browser RED tests**

In the real application, right-click an empty region, select `Lambda expression`,
enter `(\\x. x) a`, assert one term node plus two unary caps, double-click it,
undo, redo, save, reload, switch to 3D, and assert the Lambda scene remains
pickable.

- [ ] **Step 2: Run RED**

Run:

```bash
npx playwright test e2e/construction.spec.ts e2e/interaction.spec.ts e2e/view3.spec.ts
```

Expected: at least the new Lambda scenario FAIL before fixtures and exhaustive
session handling are complete.

- [ ] **Step 3: Complete fixtures and pipeline cases**

Generate `examples/lambda.json` through the normal serializer. Add every new step
variant to snapshots, sessions, theory emission, and proof pipeline switches.

- [ ] **Step 4: GREEN**

```bash
npx vitest run tests/app/pipeline.test.ts tests/app/session.test.ts tests/app/proof-snapshot.test.ts
npx playwright test e2e/construction.spec.ts e2e/interaction.spec.ts e2e/view3.spec.ts
```

- [ ] **Step 5: Commit**

```bash
git add examples/lambda.json e2e tests/app scripts/emit-theories.ts
git commit -m "test: cover lambda workflows end to end"
```

---

### Task 15: Compare real 2D and 3D renders with the corrected reference

**Files:**

- Create: `scripts/capture-lambda-comparison.ts`
- Create: `tests/visual/lambda-reference.test.ts`
- Create: `artifacts/lambda-comparison/.gitkeep` only if the repository tracks
  an artifact directory; otherwise write captures under `/tmp`.

**Interfaces:**

- Produces reproducible reference and application captures at phase boundaries
  for the five required terms in both render modes.

- [ ] **Step 1: Implement deterministic capture orchestration**

For each required term, load both the corrected HTML and the running application,
set identical normalized progress values at every phase boundary and midpoint,
and capture the Lambda drawing bounds. Record geometry measurements and sampled
stroke colors alongside each image.

- [ ] **Step 2: Run the comparison**

Run:

```bash
npx tsx scripts/capture-lambda-comparison.ts
npx vitest run tests/visual/lambda-reference.test.ts
```

Expected: all five examples produce reference, 2D, and 3D evidence; measurement
tests PASS.

- [ ] **Step 3: Inspect several examples directly**

Open and compare the one-use, duplication, deletion, nested-binder, and
capture-avoidance image sets. Check that argument copies separate before docking,
unused arguments contract, surviving geometry reaches target coordinates before
cleanup, copy hues track lineage, and 3D figures remain planar and branch-normal.
Record only current measured results in the test output.

- [ ] **Step 4: Repair any discrepancy and rerun**

Changes go to the owning geometry, motion, color, or 3D module and their focused
tests. Rerun Steps 2 and 3 until every comparison passes.

- [ ] **Step 5: Commit**

```bash
git add scripts/capture-lambda-comparison.ts tests/visual/lambda-reference.test.ts
git commit -m "test: verify lambda renders against reference"
```

---

### Task 16: Final verification and review

**Files:** No production changes unless validation finds an owning defect.

- [ ] **Step 1: Run complete TypeScript validation**

```bash
npm run typecheck
npm test
npm run e2e
```

Expected: all commands exit 0.

- [ ] **Step 2: Run complete Lean validation**

```bash
lake build
rg -n '\bsorry\b' VisualProof --glob '*.lean'
```

Expected: build exits 0 and the search returns no matches.

- [ ] **Step 3: Check repository and code ownership**

```bash
git diff --check worktree-signature-indexed-wires...HEAD
git status --short
```

Expected: no diff-format errors and a clean worktree. Confirm Lambda rule
implementations are located in the dedicated TypeScript and Lean Lambda owners.

- [ ] **Step 4: Review the implementation against the specification**

Check every specification section against production behavior and the rendered
comparison evidence. Repair any gap in its owning task and rerun the affected
focused and full validation.
