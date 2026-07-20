# Inconsistent Cut Elimination Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the native, replay-certified `inconsistentCutElim` proof rule across TypeScript, contextual deletion, Lean operational soundness, and the exact 26-tag correspondence inventory.

**Architecture:** Authoring deterministically searches direct closed shared-output term pairs with the existing fuelled normalizer, while replay checks only stored finite reduction paths, normal endpoints, and syntactic separation. The successful TypeScript and Lean rules both delegate structural mutation to the existing subtree-removal authority, and all proof/session/theorem/interaction surfaces consume the same proof-step constructor.

**Tech Stack:** TypeScript 5.5, Vitest 2, Lean 4 via Lake, existing VisualProof diagram/lambda kernels, Node-based Lean/TypeScript correspondence checker.

## Global Constraints

- The serialized tag is exactly `inconsistentCutElim`; no aliases, compatibility tags, or alternate certificate representation.
- `NormalSeparationCertificate` stores exactly `firstSteps` and `secondSteps`; normal forms and fuel are never serialized.
- Replay is finite and fuel-independent: apply stored steps, check both endpoints normal, compare syntax, then remove.
- Discovery uses the existing shared authoring fuel, continues after equal results and exhausted candidates, and never treats exhaustion as consistency.
- Only distinct direct closed term nodes in a real cut with one shared output wire are eligible.
- The cut may contain arbitrary additional nodes, wires, and descendant regions.
- The rule is a polarity-independent equivalence in forward and backward orientations.
- Backspace and Delete remain one shared contextual interaction with priority: double cut, vacuous bubble, inconsistent cut, erasure, deiteration.
- Reuse `removeSubgraph` in TypeScript and `ConcreteDiagram.removeRaw` in Lean; do not introduce another deletion model.
- Production code and formalization must not recognize particular constants, encodings, named terms, or special term shapes.
- Lean uses no `sorry`, `admit`, project-defined axioms, normalization axiom, quotient injectivity axiom, or weakened soundness boundary.
- Preserve unrelated user changes, including the existing untracked `docs/goals/` tree.

## File Structure

- Create `src/kernel/rules/inconsistent-cut.ts`: kernel gate, deterministic authoring discovery, and canonical cut selection.
- Modify `src/kernel/term/certificate.ts`: sole TypeScript `NormalSeparationCertificate` representation and fuel-free checker.
- Modify `src/kernel/term/index.ts`: export the certificate and checker.
- Modify `src/kernel/rules/index.ts`: export the rule and discovery API.
- Create `tests/kernel/rules/inconsistent-cut.test.ts`: focused kernel, certificate, search, structural, polarity, and orientation tests.
- Modify `src/kernel/proof/step.ts`: 26th proof constructor and replay dispatch.
- Modify `src/kernel/proof/json.ts`: strict codec.
- Modify `src/kernel/proof/compose.ts`: region/node remapping.
- Modify `tests/kernel/proof/json.test.ts`, `tests/kernel/proof/compose.test.ts`, and `tests/kernel/proof/step.test.ts`: persistence, remapping, and fuel-free replay coverage.
- Modify `src/app/actions.ts`: polarity-blind action descriptor and structurally plausible discovery mirror.
- Modify `src/app/interact/moves.ts`: contextual priority, certificate authoring, refusal, menus, and shared keys/orientations.
- Modify `tests/app/actions.test.ts` and `tests/app/moves.test.ts`: action discovery and interaction behavior.
- Create `VisualProof/Lambda/NormalSeparation.lean`: executable normality checker, checked finite separation, non-convertibility, quotation inequality, and local contradiction.
- Modify `VisualProof.lean`: public lambda import.
- Create `VisualProof/Rule/Structural/InconsistentCut.lean`: executable gate, canonical removal receipt, and realization theorem.
- Modify `VisualProof/Rule/Structural/Semantics.lean`: import the executable rule into the structural rule family.
- Modify `VisualProof/Rule/Step.lean`: proof-bearing payload, tag, count, classification, error, constructor, and exhaustive tag mapping.
- Create `VisualProof/Rule/Soundness/InconsistentCut.lean`: direct equation contradiction, arbitrary-conjunct cut truth, contextual removal equivalence, and receipt soundness.
- Modify `VisualProof/Rule/Soundness/Structural.lean` and `VisualProof/Rule/Soundness/All.lean`: soundness import and dispatcher case.
- Modify `VisualProof/Correspondence/StepTags.lean`: exact serialized spelling and count 26.
- Modify `VisualProof/Audit.lean`: trust-boundary prints.
- Modify `tests/kernel/formal/highlevel-alias-parity.test.ts` only if its exhaustive fixture inventory requires the new tag; do not add a hand-authored correspondence artifact.

---

### Task 1: Fuel-Free TypeScript Normal-Separation Certificate

**Files:**
- Modify: `src/kernel/term/certificate.ts`
- Modify: `src/kernel/term/index.ts`
- Test: `tests/kernel/term/certificate.test.ts`

**Interfaces:**
- Consumes: `ReductionStep`, `applyStepAt`, `stepNormalOrder`, `stepEta`, and `termEq`.
- Produces: `NormalSeparationCertificate`, `NormalSeparationCheck`, and `checkNormalSeparation(first, second, certificate)`.

- [ ] **Step 1: Write failing certificate tests**

Add tests that assert empty paths accept two arbitrary distinct normal closed terms, nonempty beta/eta paths return their normal endpoints, invalid paths identify side/index, reducible endpoints reject, and equal normal endpoints reject:

```ts
const distinct: NormalSeparationCertificate = { firstSteps: [], secondSteps: [] }
expect(checkNormalSeparation(p('\\x. x'), p('\\x. \\y. x'), distinct)).toMatchObject({ ok: true })

const reducible: NormalSeparationCertificate = {
  firstSteps: [{ kind: 'beta', path: [] }],
  secondSteps: [],
}
expect(checkNormalSeparation(p('(\\x. x) (\\z. z)'), p('\\x. \\y. x'), reducible))
  .toMatchObject({ ok: true, firstNormal: p('\\z. z') })

expect(checkNormalSeparation(p('\\x. x'), p('\\x. \\y. x'), {
  firstSteps: [{ kind: 'beta', path: [] }], secondSteps: [],
})).toMatchObject({ ok: false, reason: expect.stringMatching(/first step 0/) })
```

- [ ] **Step 2: Run the focused test and confirm the missing API failure**

Run: `npx vitest run --config vitest.config.ts tests/kernel/term/certificate.test.ts`

Expected: FAIL because `NormalSeparationCertificate` and `checkNormalSeparation` are not exported.

- [ ] **Step 3: Implement the certificate and checker**

Add one representation and one replay helper to `certificate.ts`:

```ts
export type NormalSeparationCertificate = {
  readonly firstSteps: readonly ReductionStep[]
  readonly secondSteps: readonly ReductionStep[]
}

export type NormalSeparationCheck =
  | { readonly ok: true; readonly firstNormal: Term; readonly secondNormal: Term }
  | { readonly ok: false; readonly reason: string }

function replayPath(start: Term, steps: readonly ReductionStep[], side: 'first' | 'second'):
    { readonly ok: true; readonly term: Term } | { readonly ok: false; readonly reason: string } {
  let term = start
  for (const [index, step] of steps.entries()) {
    try { term = applyStepAt(term, step) }
    catch (error) {
      return { ok: false, reason: `${side} step ${index} is invalid: ${error instanceof Error ? error.message : String(error)}` }
    }
  }
  return { ok: true, term }
}

export function checkNormalSeparation(
  first: Term,
  second: Term,
  certificate: NormalSeparationCertificate,
): NormalSeparationCheck {
  const firstResult = replayPath(first, certificate.firstSteps, 'first')
  if (!firstResult.ok) return firstResult
  const secondResult = replayPath(second, certificate.secondSteps, 'second')
  if (!secondResult.ok) return secondResult
  if (stepNormalOrder(firstResult.term) !== null || stepEta(firstResult.term) !== null) {
    return { ok: false, reason: 'first reduction path does not end in beta-eta normal form' }
  }
  if (stepNormalOrder(secondResult.term) !== null || stepEta(secondResult.term) !== null) {
    return { ok: false, reason: 'second reduction path does not end in beta-eta normal form' }
  }
  if (termEq(firstResult.term, secondResult.term)) {
    return { ok: false, reason: 'the two reduction paths end in the same normal form' }
  }
  return { ok: true, firstNormal: firstResult.term, secondNormal: secondResult.term }
}
```

Import `stepNormalOrder` and `stepEta`, and export the new types/functions from `src/kernel/term/index.ts`.

- [ ] **Step 4: Run certificate and normalizer tests**

Run: `npx vitest run --config vitest.config.ts tests/kernel/term/certificate.test.ts tests/kernel/term/normalize.test.ts`

Expected: PASS with no normalization search invoked by checker tests.

- [ ] **Step 5: Commit the certificate unit**

```bash
git add src/kernel/term/certificate.ts src/kernel/term/index.ts tests/kernel/term/certificate.test.ts
git commit -m "feat: check finite normal separation certificates"
```

### Task 2: TypeScript Kernel Gate, Search, and Atomic Removal

**Files:**
- Create: `src/kernel/rules/inconsistent-cut.ts`
- Modify: `src/kernel/rules/index.ts`
- Create: `tests/kernel/rules/inconsistent-cut.test.ts`

**Interfaces:**
- Consumes: `checkNormalSeparation`, `normalize`, `termEq`, `wireAt`, `removeSubgraph`, and `mkSelection`-compatible selection shape.
- Produces:

```ts
export type InconsistentCutDiscovery =
  | { readonly status: 'certified'; readonly first: NodeId; readonly second: NodeId; readonly certificate: NormalSeparationCertificate }
  | { readonly status: 'undecided' }
  | { readonly status: 'absent' }

export function hasInconsistentCutCandidate(d: Diagram, region: RegionId): boolean
export function findInconsistentCutEvidence(d: Diagram, region: RegionId, fuel: number): InconsistentCutDiscovery
export function applyInconsistentCutElim(d: Diagram, region: RegionId, first: NodeId, second: NodeId, certificate: NormalSeparationCertificate): Diagram
```

- [ ] **Step 1: Write the failing kernel/search test matrix**

Build diagrams with `DiagramBuilder` and arbitrary closed terms. Cover:

- already-normal separation with empty paths;
- reducible separation with nonempty paths;
- arbitrary extra nodes and a descendant cut removed;
- ancestor-scoped shared output wire retained with removed endpoints trimmed;
- cut-scoped wires removed;
- unrelated regions, nodes, wires, and IDs deeply equal before/after;
- both positive and negative cut contexts;
- both orientations by applying the eventual proof step through `applyStep` in Task 3;
- open node interface, descendant node, different output wires, same normal form, repeated ID, invalid path, and non-normal endpoint rejection;
- deterministic lexical pair choice;
- continuation after an equal-normal pair;
- continuation after an exhausted pair to a later certifying pair;
- final `undecided` only when no later certificate exists;
- final `absent` when nothing exhausts.

Use an omega-like self-application only as ordinary test input for exhaustion; do not name or detect it in production.

- [ ] **Step 2: Run the new rule test and confirm the missing module failure**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/inconsistent-cut.test.ts`

Expected: FAIL because `src/kernel/rules/inconsistent-cut.ts` does not exist.

- [ ] **Step 3: Implement canonical candidate discovery**

Use direct ownership and lexical ID order:

```ts
function candidates(d: Diagram, region: RegionId): readonly NodeId[] {
  return Object.keys(d.nodes)
    .filter((id) => {
      const node = d.nodes[id]!
      return node.kind === 'term' && node.region === region && node.freePorts.length === 0
    })
    .sort()
}

export function findInconsistentCutEvidence(d: Diagram, region: RegionId, fuel: number): InconsistentCutDiscovery {
  const ids = candidates(d, region)
  let exhausted = false
  for (let left = 0; left < ids.length; left++) for (let right = left + 1; right < ids.length; right++) {
    const first = ids[left]!
    const second = ids[right]!
    if (wireAt(d, first, { kind: 'output' }) !== wireAt(d, second, { kind: 'output' })) continue
    const firstResult = normalize(termNodeAt(d, first).term, fuel)
    const secondResult = normalize(termNodeAt(d, second).term, fuel)
    if (firstResult.status === 'fuel-exhausted' || secondResult.status === 'fuel-exhausted') {
      exhausted = true
      continue
    }
    if (termEq(firstResult.term, secondResult.term)) continue
    return {
      status: 'certified', first, second,
      certificate: { firstSteps: firstResult.path, secondSteps: secondResult.path },
    }
  }
  return exhausted ? { status: 'undecided' } : { status: 'absent' }
}
```

`hasInconsistentCutCandidate` performs only the real-cut/direct-closed/shared-output structural filter and no reduction search.

- [ ] **Step 4: Implement the replay gate and canonical removal**

```ts
export function applyInconsistentCutElim(
  d: Diagram,
  region: RegionId,
  first: NodeId,
  second: NodeId,
  certificate: NormalSeparationCertificate,
): Diagram {
  const cut = d.regions[region]
  if (cut === undefined) throw new DiagramError(`unknown region '${region}'`)
  if (cut.kind !== 'cut') throw new RuleError(`inconsistent-cut elimination requires a cut; '${region}' is a ${cut.kind}`)
  if (first === second) throw new RuleError('inconsistent-cut elimination requires two distinct term nodes')
  const firstNode = termNodeAt(d, first)
  const secondNode = termNodeAt(d, second)
  if (firstNode.region !== region || secondNode.region !== region) {
    throw new RuleError(`both term nodes must be directly contained in cut '${region}'`)
  }
  if (firstNode.freePorts.length !== 0 || secondNode.freePorts.length !== 0) {
    throw new RuleError('inconsistent-cut elimination requires closed terms')
  }
  if (wireAt(d, first, { kind: 'output' }) !== wireAt(d, second, { kind: 'output' })) {
    throw new RuleError('the two term outputs must share one wire')
  }
  const checked = checkNormalSeparation(firstNode.term, secondNode.term, certificate)
  if (!checked.ok) throw new RuleError(`invalid normal-separation certificate: ${checked.reason}`)
  return removeSubgraph(d, { region: cut.parent, regions: [region], nodes: [], wires: [] })
}
```

- [ ] **Step 5: Run focused rule tests and diagram well-formedness tests**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/inconsistent-cut.test.ts tests/kernel/diagram/wellformed.test.ts tests/kernel/diagram/splice.test.ts`

Expected: PASS; every result is accepted by `mkDiagram` and unrelated content assertions hold.

- [ ] **Step 6: Commit the kernel rule**

```bash
git add src/kernel/rules/inconsistent-cut.ts src/kernel/rules/index.ts tests/kernel/rules/inconsistent-cut.test.ts
git commit -m "feat: add inconsistent cut kernel rule"
```

### Task 3: Proof Language, Replay, Strict JSON, and ID Remapping

**Files:**
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `tests/kernel/proof/step.test.ts`
- Modify: `tests/kernel/proof/json.test.ts`
- Modify: `tests/kernel/proof/compose.test.ts`

**Interfaces:**
- Consumes: `applyInconsistentCutElim` and `NormalSeparationCertificate` from Tasks 1–2.
- Produces the exact `ProofStep` constructor and exhaustive persistence/remapping support.

- [ ] **Step 1: Add failing replay, round-trip, malformed JSON, and remapping tests**

Add the constructor to the exhaustive test inventory:

```ts
{
  rule: 'inconsistentCutElim', region: 'r1', first: 'n0', second: 'n1',
  certificate: { firstSteps: [], secondSteps: [{ kind: 'eta', path: ['body'] }] },
}
```

Add malformed cases for missing `certificate`, `firstSteps`, `secondSteps`, `region`, `first`, or `second`; unknown step/certificate/reduction-step fields; non-array paths; invalid kind/path segment; and non-string IDs. Add a composition test whose source/target diagrams are isomorphic but use different region/node IDs, then assert all three IDs remap and the certificate remains equal.

Add a replay test that authors under one fuel, changes a local UI-fuel variable, and calls `applyStep` successfully without passing fuel.

- [ ] **Step 2: Run focused proof tests and verify exhaustive failures**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts`

Expected: FAIL on the missing `ProofStep` union member and switch cases.

- [ ] **Step 3: Add the proof constructor and replay dispatch**

In `step.ts`, import the certificate type/applier and place the constructor immediately after `doubleCutElim` in both union and dispatcher:

```ts
| { readonly rule: 'inconsistentCutElim'; readonly region: RegionId; readonly first: NodeId; readonly second: NodeId; readonly certificate: NormalSeparationCertificate }
```

```ts
case 'inconsistentCutElim':
  return applyInconsistentCutElim(d, step.region, step.first, step.second, step.certificate)
```

Do not add an orientation argument or receipt special case; same-ID surviving wires already use the correct root-filtered transport.

- [ ] **Step 4: Add strict JSON using the existing reduction-step parser**

Refactor the local nested `steps` parser into shared private `reductionStepsToJson` and `reductionStepsFromJson` helpers, then define:

```ts
function normalSeparationToJson(certificate: NormalSeparationCertificate): unknown {
  return {
    firstSteps: reductionStepsToJson(certificate.firstSteps),
    secondSteps: reductionStepsToJson(certificate.secondSteps),
  }
}

function normalSeparationFromJson(value: unknown, what: string): NormalSeparationCertificate {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['firstSteps', 'secondSteps'], what)
  return {
    firstSteps: reductionStepsFromJson(value.firstSteps, `${what}.firstSteps`),
    secondSteps: reductionStepsFromJson(value.secondSteps, `${what}.secondSteps`),
  }
}
```

Add exact top-level key validation and string parsing in `stepFromJson`.

- [ ] **Step 5: Add composition mapping**

```ts
case 'inconsistentCutElim':
  return {
    ...step,
    region: mapId(iso.regions, step.region, 'region'),
    first: mapId(iso.nodes, step.first, 'node'),
    second: mapId(iso.nodes, step.second, 'node'),
  }
```

- [ ] **Step 6: Run proof-language tests and typecheck**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts tests/kernel/proof/theorem.test.ts tests/app/replay.test.ts tests/app/session.test.ts`

Run: `npm run typecheck`

Expected: both commands PASS.

- [ ] **Step 7: Commit proof-language integration**

```bash
git add src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts
git commit -m "feat: persist inconsistent cut elimination"
```

### Task 4: Contextual Backspace/Delete, Discovery, Priority, and Menus

**Files:**
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `tests/app/actions.test.ts`
- Modify: `tests/app/moves.test.ts`

**Interfaces:**
- Consumes: `hasInconsistentCutCandidate`, `findInconsistentCutEvidence`, `ProofStep`, and shared `fuel()`.
- Produces: `ActionDescriptor['kind'] === 'inconsistentCutElim'` and one shared contextual resolution path.

- [ ] **Step 1: Add failing discovery and controller tests**

Add tests for:

- descriptor appears for a single selected plausible cut at both polarities and orientations;
- selecting cut plus all contents produces the same absorbed selection;
- `contextualDeleteStep` chooses double cut, then vacuous, then inconsistent cut, then erasure, then deiteration;
- inconsistency beats available erasure;
- equal normal forms fall through;
- final exhaustion throws `/inconsistency is undecided under the current fuel/` and returns no step;
- later certifying pair beats earlier exhaustion;
- `ProofMoveController.keyDown` records the same `inconsistentCutElim` action for `Backspace` and `Delete`;
- forward and backward controllers share the same result;
- menu action authors and commits the same proof step.

- [ ] **Step 2: Run focused app tests and confirm missing descriptor failures**

Run: `npx vitest run --config vitest.config.ts tests/app/actions.test.ts tests/app/moves.test.ts`

Expected: FAIL because the descriptor and contextual branch do not exist.

- [ ] **Step 3: Add the polarity-blind action mirror**

Extend `ActionDescriptor`:

```ts
| { readonly kind: 'inconsistentCutElim'; readonly label: string }
```

Inside the existing single-selected-region block, add only when `r.kind === 'cut'` and `hasInconsistentCutCandidate(d, rid)`:

```ts
out.push({ kind: 'inconsistentCutElim', label: 'Eliminate the inconsistent cut' })
```

Do not use polarity or fuel in this mirror.

- [ ] **Step 4: Implement exact contextual priority and refusal**

Replace the single null-coalescing action choice with staged resolution:

```ts
const doubleCut = byKind('doubleCutElim')
if (doubleCut !== undefined) return { rule: 'doubleCutElim', region: discovery.sel.regions[0]! }
const vacuous = byKind('vacuousElim')
if (vacuous !== undefined) return { rule: 'vacuousElim', region: discovery.sel.regions[0]! }
if (byKind('inconsistentCutElim') !== undefined) {
  const region = discovery.sel.regions[0]!
  const result = findInconsistentCutEvidence(d, region, fuel)
  if (result.status === 'certified') {
    return { rule: 'inconsistentCutElim', region, first: result.first, second: result.second, certificate: result.certificate }
  }
  if (result.status === 'undecided') {
    throw new RuleError('inconsistency is undecided under the current fuel')
  }
}
const erase = byKind('erase')
if (erase !== undefined) return erasureStep(d, discovery.sel)
const deiterate = byKind('deiterate')
return deiterate === undefined ? null : deiterationStep(d, discovery.sel, fuel)
```

- [ ] **Step 5: Add the menu branch without another controller**

In `#appendAction`, call one helper that converts a certified discovery into the exact proof step and throws the same undecided/absent refusal. Do not add keyboard listeners, state fields, prompts, or confirmation UI.

- [ ] **Step 6: Run interaction, ownership, and session tests**

Run: `npx vitest run --config vitest.config.ts tests/app/actions.test.ts tests/app/moves.test.ts tests/app/edit.test.ts tests/app/replay.test.ts tests/app/session.test.ts tests/architecture/interaction-ownership.test.ts`

Expected: PASS, with both keys and orientations sharing `ProofMoveController`.

- [ ] **Step 7: Commit interaction integration**

```bash
git add src/app/actions.ts src/app/interact/moves.ts tests/app/actions.test.ts tests/app/moves.test.ts
git commit -m "feat: resolve inconsistent cuts on deletion"
```

### Task 5: Lean Executable Normality and Generic Separation Metatheory

**Files:**
- Create: `VisualProof/Lambda/NormalSeparation.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `Term`, `etaContract`, `OneStep`, `Reduces`, `checkPath`, `not_betaEta_of_normal_ne`, `quote`, and `quote_eq_iff`.
- Produces:

```lean
def hasRedex (term : Term n α) : Bool
def isNormal (term : Term n α) : Bool := !hasRedex term
theorem isNormal_iff : isNormal term = true ↔ Normal term

structure NormalSeparationCertificate where
  firstSteps : ReductionPath
  secondSteps : ReductionPath

def checkNormalSeparation [DecidableEq α]
  (first second : Term n α) (certificate : NormalSeparationCertificate) : Bool

structure CheckedNormalSeparation [DecidableEq α]
  (first second : Term n α) where
  certificate : NormalSeparationCertificate
  valid : checkNormalSeparation first second certificate = true
```

- [ ] **Step 1: Add the definitions and failing example theorems**

Start the new module with generic examples built only from lambda constructors:

```lean
example : checkNormalSeparation
    (Term.lam (Term.bvar 0))
    (Term.lam (Term.lam (Term.bvar 1)))
    { firstSteps := [], secondSteps := [] } = true := by
  native_decide

example : checkNormalSeparation
    (Term.app (Term.lam (Term.bvar 0)) (Term.lam (Term.bvar 0)))
    (Term.lam (Term.lam (Term.bvar 1)))
    { firstSteps := [{ path := [], kind := .beta }], secondSteps := [] } = true := by
  native_decide
```

- [ ] **Step 2: Run the module and confirm missing definitions**

Run: `lake env lean VisualProof/Lambda/NormalSeparation.lean`

Expected: FAIL because the checker is not defined.

- [ ] **Step 3: Implement executable redex detection**

```lean
def hasRedex : Term n α → Bool
  | .bvar _ | .port _ => false
  | .lam body => (etaContract body).isSome || hasRedex body
  | .app (.lam _) _ => true
  | .app fn arg => hasRedex fn || hasRedex arg

def isNormal (term : Term n α) : Bool := !hasRedex term
```

Prove `hasRedex_eq_true_iff` by structural induction, using `etaContract_sound`, `etaContract_complete`, and `OneStep.beta/eta/lam/appFn/appArg`. Then derive:

```lean
theorem isNormal_iff : isNormal term = true ↔ Normal term := by
  rw [Bool.not_eq_true]
  constructor
  · intro noRedex next step
    exact noRedex ((hasRedex_eq_true_iff).2 ⟨next, step⟩)
  · intro normal
    apply Bool.eq_false_iff.mpr
    rintro redex
    obtain ⟨next, step⟩ := (hasRedex_eq_true_iff).1 redex
    exact normal next step
```

- [ ] **Step 4: Add finite-path reduction soundness and the raw checker**

Prove the stronger path theorem omitted by the existing conversion checker:

```lean
theorem checkPath_reduces : checkPath start path = some finish →
    Reduces start finish := by
  induction path generalizing start with
  | nil => intro equality; cases equality; exact .refl
  | cons step rest ih =>
      simp only [checkPath]
      split
      · intro impossible; contradiction
      · rename_i next stepValid
        intro restValid
        exact (Reduces.tail .refl (stepAt_sound stepValid)).trans
          (ih restValid)
```

Define `checkNormalSeparation` by applying both paths, then deciding `isNormal firstEnd && isNormal secondEnd && firstEnd != secondEnd`.

- [ ] **Step 5: Prove certificate consequences and generic contradiction**

From a checked certificate, expose normals and reductions, then prove:

```lean
theorem CheckedNormalSeparation.not_betaEta
    (checked : CheckedNormalSeparation first second) :
    ¬ BetaEta first second := by
  obtain ⟨firstNormal, secondNormal, firstReduces, secondReduces,
    firstNormalProof, secondNormalProof, different⟩ := checked.sound
  intro equivalent
  exact not_betaEta_of_normal_ne firstNormalProof secondNormalProof different
    (firstReduces.toBetaEta.symm.trans (equivalent.trans secondReduces.toBetaEta))

theorem CheckedNormalSeparation.quote_ne
    (checked : CheckedNormalSeparation first second) :
    quote first ≠ quote second := by
  intro equal
  exact checked.not_betaEta ((quote_eq_iff).mp equal)

theorem shared_output_closed_terms_false
    (checked : CheckedNormalSeparation first second) :
    ¬ ∃ output : Individual,
      output = quote first ∧ output = quote second := by
  rintro ⟨output, firstEq, secondEq⟩
  exact checked.quote_ne (firstEq.symm.trans secondEq)
```

Add the public theorem used above directly in this module:

```lean
theorem Reduces.betaEta (reduces : Reduces first second) :
    BetaEta first second := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (.step step)
```

- [ ] **Step 6: Build and audit the lambda module**

Run: `lake env lean VisualProof/Lambda/NormalSeparation.lean`

Run: `rg -n 'sorry|admit|decreasing_by sorry|^axiom ' VisualProof/Lambda`

Expected: Lean succeeds; ripgrep prints no matches.

- [ ] **Step 7: Commit Lean lambda metatheory**

```bash
git add VisualProof/Lambda/NormalSeparation.lean VisualProof.lean
git commit -m "feat: formalize finite normal separation"
```

### Task 6: Lean Proof-Bearing Step and Executable Removal

**Files:**
- Create: `VisualProof/Rule/Structural/InconsistentCut.lean`
- Modify: `VisualProof/Rule/Structural/Semantics.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Correspondence/StepTags.lean`

**Interfaces:**
- Consumes: Task 5 certificate checker and existing `CheckedSelection`, `removeRaw`, removal well-formedness, provenance, and interface transport.
- Produces: `InconsistentCutPayload` in the existing payload authority, `applyInconsistentCutElim`, realization theorem, 26th Step/StepTag, and exact serialized spelling.

- [ ] **Step 1: Add failing StepTag and payload examples**

Change expected lengths to 26 and add `inconsistentCutElim` to `StepTag.all` and serialized-name tests first. Add a small formal example constructing a payload over a generic concrete fixture in the new rule module or reuse an existing arbitrary fixture builder without giving any term special semantics.

- [ ] **Step 2: Run Lean and correspondence checks to verify red state**

Run: `lake env lean VisualProof/Correspondence/StepTags.lean`

Run: `npm run formal:tags`

Expected: FAIL until TypeScript/Lean both expose the matching 26th tag and the Lean constructor exists.

- [ ] **Step 3: Define the proof-bearing payload in `Step.lean`**

```lean
structure InconsistentCutPayload
    (input : Diagram.CheckedDiagram signature)
    (region : Fin input.val.regionCount)
    (first second : Fin input.val.nodeCount) where
  parent : Fin input.val.regionCount
  region_is_cut : input.val.regions region = .cut parent
  distinct : first ≠ second
  firstTerm secondTerm : Lambda.ClosedTerm
  firstNode : input.val.nodes first = .term region 0 firstTerm
  secondNode : input.val.nodes second = .term region 0 secondTerm
  outputWire : Fin input.val.wireCount
  firstOutput : input.val.EndpointOccurs outputWire { node := first, port := .output }
  secondOutput : input.val.EndpointOccurs outputWire { node := second, port := .output }
  certificate : Lambda.NormalSeparationCertificate
  selection : Diagram.CheckedSelection input.val
  selection_eq : selection.val = {
    anchor := parent, childRoots := [region], directNodes := [], explicitWires := []
  }
```

Keeping this structure in `Step.lean` follows the existing `ConversionPayload`, `CongruencePayload`, and theorem-payload ownership and avoids a `Step`/structural-applier import cycle.

- [ ] **Step 4: Implement the executable applier and receipt**

```lean
def applyInconsistentCutElim
    (input : CheckedDiagram signature)
    (region first second)
    (payload : InconsistentCutPayload input region first second) :
    Except StepError (StepReceipt input) :=
  if hcertificate : Lambda.checkNormalSeparation
      payload.firstTerm payload.secondTerm payload.certificate = true then
    .ok {
      result := ⟨input.val.removeRaw payload.selection {},
        ConcreteDiagram.removeRaw_wellFormed input payload.selection {}⟩
      provenance := removeWireProvenance input payload.selection
      interface := removeWireInterfaceTransport input payload.selection
    }
  else .error .invalidCertificate
```

Prove `applyInconsistentCutElim_realizes` by unfolding the successful branch and returning `StepReceipt.Realizes` with `rfl` component proofs, following `applyDeiteration_realizes`.

- [ ] **Step 5: Integrate the 26th proof-bearing constructor**

Add `inconsistentCutElim` after `doubleCutElim` in `StepTag`, `StepTag.all`, `semanticMode` as `.equivalent`, `Step`, `Step.tag`, and the complete serialized name mapping. Update comments and both length theorems from 25 to 26. Use `.invalidCertificate` for failed certificate checking; structural invalidity is excluded by the proof-bearing payload just as current payloads exclude stale finite IDs.

- [ ] **Step 6: Build the executable rule and run tag correspondence**

Run: `lake env lean VisualProof/Rule/Structural/InconsistentCut.lean`

Run: `npm run formal:tags`

Expected: the module builds and the checker prints `Lean and TypeScript agree on 26 proof-step tags.`

- [ ] **Step 7: Commit executable Lean integration**

```bash
git add VisualProof/Rule/Structural/InconsistentCut.lean VisualProof/Rule/Structural/Semantics.lean VisualProof/Rule/Step.lean VisualProof/Correspondence/StepTags.lean
git commit -m "feat: add formal inconsistent cut step"
```

### Task 7: Lean Local Contradiction and Cut-Body Semantics

**Files:**
- Create: `VisualProof/Rule/Soundness/InconsistentCut.lean`

**Interfaces:**
- Consumes: `InconsistentCutPayload`, `shared_output_closed_terms_false`, concrete compiler node-equation lemmas, item-sequence conjunction, and `cut_denotes_negation`.
- Produces local theorems proving the selected cut item denotes true despite arbitrary additional contents.

- [ ] **Step 1: State failing semantic boundary theorems before proofs**

State these generic results with actual payload terms and compiler environments:

```lean
theorem direct_shared_output_equations_false
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation payload.firstTerm payload.secondTerm)
    (env : Fin wires → Lambda.Individual) :
    ¬ (env firstOutputIndex = Lambda.quote payload.firstTerm ∧
       env firstOutputIndex = Lambda.quote payload.secondTerm)

theorem inconsistent_cut_body_false
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation payload.firstTerm payload.secondTerm) :
    ∀ env relEnv,
      ¬ denoteRegion Lambda.canonicalModel named env relEnv compiledCutBody

theorem inconsistent_cut_item_true ... :
    denoteItem Lambda.canonicalModel named env relEnv (.cut compiledCutBody)
```

Bind `firstOutputIndex` and `compiledCutBody` to the concrete compiler output supplied by existing site-view/compile-node witnesses rather than introducing abstract assumptions.

- [ ] **Step 2: Run the new soundness module and record missing lemma errors**

Run: `lake env lean VisualProof/Rule/Soundness/InconsistentCut.lean`

Expected: FAIL on the unproved compiler-to-equation and conjunction obligations.

- [ ] **Step 3: Prove direct equation contradiction**

Use the direct-node equations (`payload.firstNode`, `payload.secondNode`) with the existing `compileNode?` term case and endpoint ownership uniqueness to show both equations read the same environment coordinate. Rewrite canonical-model evaluation of closed terms to `quote`; then apply:

```lean
exact Lambda.shared_output_closed_terms_false checked
  ⟨env sharedOutputIndex, firstEquation, secondEquation⟩
```

Do not derive inequality from a head shape or named constant.

- [ ] **Step 4: Prove arbitrary additional conjuncts cannot restore the body**

Use `denoteItemSeq_append`/permutation lemmas to isolate the two direct equation items. From a body denotation, project both equation conjuncts and contradict Step 3. The proof must quantify over the untouched suffix/prefix and every child-region item.

- [ ] **Step 5: Prove the cut item denotes true**

Rewrite with `cut_denotes_negation`; the body-false theorem discharges the negation. Then prove conjunction with/removal of the true cut item by `And` simplification and the existing item-sequence permutation equivalence.

- [ ] **Step 6: Build and audit the local soundness module**

Run: `lake env lean VisualProof/Rule/Soundness/InconsistentCut.lean`

Run: `rg -n 'sorry|admit|decreasing_by sorry|^axiom ' VisualProof/Rule/Soundness/InconsistentCut.lean`

Expected: Lean succeeds and ripgrep prints no matches.

- [ ] **Step 7: Commit local semantic proof**

```bash
git add VisualProof/Rule/Soundness/InconsistentCut.lean
git commit -m "proof: establish inconsistent cut truth"
```

### Task 8: Lean Concrete Removal, Contextual Equivalence, and Global Soundness

**Files:**
- Modify: `VisualProof/Rule/Soundness/InconsistentCut.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Soundness/All.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: Task 7 true-cut theorem, `ConcreteDiagram.removeRaw` decomposition/reassembly, standard removal transports, and `SuccessfulReceiptSound.of_realized_operational`.
- Produces `applyInconsistentCutElim_sound`, the global dispatcher case, replay/theorem inheritance, and public audit coverage.

- [ ] **Step 1: State the failing receipt-level theorem**

```lean
theorem applyInconsistentCutElim_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : CheckedDiagram signature)
    (region first second)
    (payload : InconsistentCutPayload input region first second)
    (receipt : StepReceipt input)
    (happly : applyInconsistentCutElim input region first second payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.inconsistentCutElim region first second payload) receipt
```

- [ ] **Step 2: Run the soundness module and confirm the missing contextual proof**

Run: `lake env lean VisualProof/Rule/Soundness/InconsistentCut.lean`

Expected: FAIL until concrete removal is connected to canonical semantics.

- [ ] **Step 3: Normalize the successful receipt through removal realization**

Obtain the successful certificate equality from the `if` branch, construct `Lambda.CheckedNormalSeparation`, and obtain `realizes` from `applyInconsistentCutElim_realizes`. Apply `SuccessfulReceiptSound.of_realized_operational` using the same operational open result and boundary transport pattern as erasure/deiteration.

- [ ] **Step 4: Prove concrete source/result equivalence**

Use the checked selection's `selection_eq` to specialize the existing decomposition/reassembly theorems. The original source reassembles as the retained frame conjoined with the selected cut; the `removeRaw` result is the retained frame. Feed Task 7's proof that the selected cut denotes true into the existing context equivalence/congruence theorem. Establish both directions directly, then simplify:

```lean
change DirectedEntailment .inconsistentCutElim orientation sourceDenotes targetDenotes
unfold DirectedEntailment
simp only [StepTag.semanticMode]
exact contextualEquivalence
```

The proof must retain arbitrary ordered boundaries and work at any ancestor depth; do not specialize to closed root diagrams.

- [ ] **Step 5: Add exhaustive dispatcher and public audit cases**

Add to `Rule.applyStep`:

```lean
| .inconsistentCutElim region first second payload =>
    applyInconsistentCutElim input region first second payload
```

Add to `applyStep_sound`:

```lean
| inconsistentCutElim region first second payload =>
    exact applyInconsistentCutElim_sound context orientation input
      region first second payload receipt happly
```

Add audit prints for `Lambda.shared_output_closed_terms_false`, `Rule.applyInconsistentCutElim_sound`, and retain `Rule.applyStep_sound`, replay, theorem, and theory prints.

- [ ] **Step 6: Run focused and global Lean builds**

Run: `lake env lean VisualProof/Rule/Soundness/InconsistentCut.lean`

Run: `lake build`

Run: `rg -n 'sorry|admit|decreasing_by sorry|^axiom ' VisualProof`

Expected: both Lean commands succeed; ripgrep prints no matches.

- [ ] **Step 7: Commit operational soundness**

```bash
git add VisualProof/Rule/Soundness/InconsistentCut.lean VisualProof/Rule/Soundness/Structural.lean VisualProof/Rule/Soundness.lean VisualProof/Rule/Soundness/All.lean VisualProof/Audit.lean VisualProof.lean
git commit -m "proof: connect inconsistent cut removal to semantics"
```

### Task 9: Full Integration Validation and Foundation Conformance

**Files:**
- Modify only files implicated by failures from the required commands.
- Modify: `/tmp/visualproof-inconsistent-cut-elim-foundation-fUMcPP/foundation.md` outside the repository to append `<conformance>` after all validation succeeds.

**Interfaces:**
- Consumes the complete implementation.
- Produces authoritative green evidence and the final foundation conformance receipt.

- [ ] **Step 1: Run focused feature suites together**

Run:

```bash
npx vitest run --config vitest.config.ts \
  tests/kernel/term/certificate.test.ts \
  tests/kernel/rules/inconsistent-cut.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/app/actions.test.ts \
  tests/app/moves.test.ts
```

Expected: PASS.

- [ ] **Step 2: Run the full TypeScript suite and typecheck**

Run: `npm test`

Run: `npm run typecheck`

Expected: both PASS.

- [ ] **Step 3: Run exact tag correspondence**

Run: `npm run formal:tags`

Expected: `Lean and TypeScript agree on 26 proof-step tags.`

- [ ] **Step 4: Run the full Lean build and trust scan**

Run: `lake build`

Run: `rg -n 'sorry|admit|decreasing_by sorry|^axiom ' VisualProof`

Expected: `lake build` succeeds; ripgrep prints no matches and exits 1 because the pattern is absent.

- [ ] **Step 5: Run repository integrity checks**

Run: `git diff --check`

Run: `git status --short`

Expected: no whitespace errors; status lists only intentional feature changes/commits plus the pre-existing untracked `docs/goals/` tree.

- [ ] **Step 6: Repair and rerun every in-scope failure**

For any failing command, identify the first root cause, add or tighten the focused regression test, repair the implementation without weakening a gate, and rerun the focused command followed by its full validation command. Continue until all required commands are green or an external blocker has an exact documented unblock.

- [ ] **Step 7: Append foundation conformance evidence**

Append without changing earlier foundation sections:

```xml
<conformance>
Implemented the finite normal-separation certificate and fuel-free replay checker; the direct closed shared-output cut gate; deterministic fuelled authoring discovery; canonical removeSubgraph/removeRaw transformation; strict proof JSON; ID remapping; shared Backspace/Delete/menu behavior in both orientations; Lean executable normality, separation, contradiction, cut truth, contextual removal equivalence, receipt soundness, and global replay/theorem dispatch. No prior model was retained or replaced because this is a new native constructor; no alternate deletion or certificate path was introduced. Record the exact green command outputs and the 26-tag correspondence result here.
</conformance>
```

- [ ] **Step 8: Commit any final validation-only repairs**

If Step 6 changed files:

```bash
git add <only the in-scope repaired files>
git commit -m "test: complete inconsistent cut validation"
```

If no files changed, do not create an empty commit.
