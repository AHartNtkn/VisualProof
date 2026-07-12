# Atomic Proof Spawning Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Delete arbitrary graphical insertion and replace every use with shared atomic spawning and ordinary proof operations, while restoring named and bound relation spawning—with approved binder colors and subtree hover highlighting—to every Proof canvas.

**Architecture:** Move node-plus-singleton-wire construction into one kernel structural module consumed by Edit and Proof. Add three non-overlapping atomic proof steps (`openTermSpawn`, `relationSpawn`, `boundRelationSpawn`) and keep `closedTermIntro` authoritative for closed terms. One shared `ProofSpawnController` owns `SpawnCascade` policy for main and fixed Proof surfaces. Remove the general insertion model completely and reconstruct bundled Frege derivations from atomic spawns and existing rules.

**Tech Stack:** TypeScript, immutable diagram kernel, Vitest, Playwright, Vite-generated theory JSON.

## Global Constraints

- Do not retain an insertion alias, wrapper, private arbitrary-pattern helper, compatibility decoder, or legacy serialized step.
- Edit, comprehension construction, main Proof, and fixed Proof use the same `SpawnCascade` and the same structural spawn functions.
- Closed λ-terms use only `closedTermIntro`; `openTermSpawn` requires at least one free port.
- Forward atomic spawning requires a negative region; backward atomic spawning requires a positive region.
- Named and bound relation options appear in the same valid Proof contexts; bound relations additionally require an enclosing bubble.
- Preserve the existing circular binder swatches, nested ordering, arity labels, and complete binder-group hover highlighting.
- Do not run `test:physics` or `test:all` unless physics implementation changes.

---

### Task 1: Shared structural spawning and atomic kernel rules

**Files:**
- Create: `src/kernel/diagram/spawn.ts`
- Create: `src/kernel/rules/spawn.ts`
- Modify: `src/app/edit.ts`
- Modify: `src/app/index.ts`
- Modify: every importer of `addTermNode`, `addRefNode`, and `addAtomNode`
- Modify: `src/kernel/rules/index.ts`
- Test: `tests/kernel/rules/spawn.test.ts`
- Test: `tests/app/edit.test.ts`

**Interfaces:**
- Produce structural functions:
  - `spawnTermNode(d: Diagram, region: RegionId, term: Term): { diagram: Diagram; node: NodeId }`
  - `spawnRelationNode(d: Diagram, region: RegionId, defId: string, arity: number): { diagram: Diagram; node: NodeId }`
  - `spawnBoundRelationNode(d: Diagram, region: RegionId, binder: RegionId): { diagram: Diagram; node: NodeId }`
- Produce gated appliers:
  - `applyOpenTermSpawn(d, region, term, orientation)`
  - `applyRelationSpawn(d, region, defId, expectedArity, relations, orientation)`
  - `applyBoundRelationSpawn(d, region, binder, orientation)`
- Consume the structural functions from both Edit and the gated Proof appliers; no copied node/wire construction remains in `src/app/edit.ts`.

- [ ] **Step 1: Write failing structural-sharing and rule tests**

Add tests proving one-node construction, exact singleton wires, non-overlap with closed-term introduction, relation revalidation, binder enclosure, and forward/backward gates:

```ts
it('open-term spawn creates exactly one node and one singleton wire per required port', () => {
  const host = hostWithNegativeCut()
  const out = applyOpenTermSpawn(host.diagram, host.cut, parseTerm('f x'), 'forward')
  expect(Object.keys(out.nodes)).toHaveLength(1)
  expect(Object.values(out.wires).every((wire) => wire.scope === host.cut && wire.endpoints.length === 1)).toBe(true)
})

it('open-term spawn rejects closed terms instead of overlapping closedTermIntro', () => {
  expect(() => applyOpenTermSpawn(host.diagram, host.cut, parseTerm('\\x. x'), 'forward'))
    .toThrow(/requires at least one free port/)
})

it('relation spawn revalidates the live definition and displayed arity', () => {
  expect(() => applyRelationSpawn(host.diagram, host.cut, 'logic/R', 2, relations, 'forward')).not.toThrow()
  expect(() => applyRelationSpawn(host.diagram, host.cut, 'logic/R', 1, relations, 'forward')).toThrow(/arity/)
})

it('bound spawn requires an enclosing bubble and the active insertion polarity', () => {
  expect(() => applyBoundRelationSpawn(diagram, negativeInsideBubble, bubble, 'forward')).not.toThrow()
  expect(() => applyBoundRelationSpawn(diagram, outsideBubble, bubble, 'forward')).toThrow(/enclose/)
})
```

- [ ] **Step 2: Run the new tests and verify RED**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/spawn.test.ts tests/app/edit.test.ts`

Expected: FAIL because the shared structural module and atomic appliers do not exist.

- [ ] **Step 3: Move structural construction into the kernel**

Move the existing immutable implementations from `src/app/edit.ts` into `src/kernel/diagram/spawn.ts`, preserving fresh-id selection and `mkDiagram` validation. Migrate every caller to the new names and delete the three app-owned implementations; do not re-export aliases from `src/app/edit.ts` or `src/app/index.ts`.

- [ ] **Step 4: Implement the three gated appliers**

Use one private polarity helper and the shared structural functions:

```ts
function requireSpawnPolarity(d: Diagram, region: RegionId, orientation: Orientation): void {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, region)
  if (have !== need) throw new RuleError(`${orientation === 'backward' ? 'backward ' : ''}spawning requires a ${need} region; '${region}' is ${have}`)
}

export function applyOpenTermSpawn(d: Diagram, region: RegionId, term: Term, orientation: Orientation): Diagram {
  requireSpawnPolarity(d, region, orientation)
  if (freePorts(term).length === 0) throw new RuleError('open-term spawn requires at least one free port; use closed-term introduction')
  return spawnTermNode(d, region, term).diagram
}
```

`applyRelationSpawn` must look up `defId` in the live relation map and compare `boundary.length` with `expectedArity`. `applyBoundRelationSpawn` must verify the binder is a bubble enclosing `region` before calling `spawnBoundRelationNode`.

- [ ] **Step 5: Run focused tests and verify GREEN**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/spawn.test.ts tests/app/edit.test.ts tests/app/comprehension-editor.test.ts`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add src/kernel/diagram/spawn.ts src/kernel/rules/spawn.ts src/kernel/rules/index.ts src/app/edit.ts src/app/index.ts src tests/kernel/rules/spawn.test.ts tests/app/edit.test.ts
git commit -m "refactor: share atomic diagram spawning"
```

---

### Task 2: Replace the insertion proof model with atomic steps

**Files:**
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Delete insertion-only portions from: `src/kernel/rules/insertion.ts`
- Modify: `src/kernel/rules/index.ts`
- Delete or rewrite: `tests/kernel/rules/insertion.test.ts`
- Modify: `tests/kernel/proof/step.test.ts`
- Modify: `tests/kernel/proof/json.test.ts`
- Modify: `tests/kernel/proof/open-steps.test.ts`
- Modify: `tests/kernel/proof/compose.test.ts`
- Modify: `tests/kernel/rules/polarity-matrix.test.ts`
- Modify: `tests/kernel/rules/error-vocabulary.test.ts`
- Modify: `tests/app/actions.test.ts`
- Modify: `tests/app/session.test.ts`

**Interfaces:**
- Add `ProofStep` variants:

```ts
| { readonly rule: 'openTermSpawn'; readonly region: RegionId; readonly term: Term }
| { readonly rule: 'relationSpawn'; readonly region: RegionId; readonly defId: string; readonly arity: number }
| { readonly rule: 'boundRelationSpawn'; readonly region: RegionId; readonly binder: RegionId; readonly arity: number }
```

- Remove the `insertion` variant and every arbitrary-pattern field.

- [ ] **Step 1: Write failing proof-model tests**

Replace insertion round-trip tests with atomic-step replay/JSON/composition tests. Add an explicit legacy rejection:

```ts
expect(() => stepFromJson({
  rule: 'insertion', region: 'r1', pattern: closedPatternJson, attachments: [], binders: {},
})).toThrow(/unknown proof rule 'insertion'/)
```

Add backward-session tests using `openTermSpawn`, `relationSpawn`, and `boundRelationSpawn` to prove the orientation-flipped gate and theorem declaration.

- [ ] **Step 2: Run focused proof tests and verify RED**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts tests/kernel/proof/open-steps.test.ts tests/kernel/proof/compose.test.ts tests/app/session.test.ts`

Expected: FAIL because the atomic variants are absent and insertion is still accepted.

- [ ] **Step 3: Add atomic dispatch, mapping, and JSON cases**

Dispatch the three variants to Task 1’s appliers, map only their host ids in `mapStepIds`, and serialize only scalar/term fields. `relationSpawn` consumes `ctx.relations`; the other two do not carry context values.

- [ ] **Step 4: Delete the general insertion model**

Remove `applyInsertion` while keeping `applyWireJoin` in a file named for wire joining (rename to `src/kernel/rules/wire-join.ts`). Delete the insertion action descriptor, discovery branch, menu row, `#openTermInsertion`, arbitrary-pattern imports, and insertion-specific tests. Update comments describing polarity symmetry to name atomic spawning rather than insertion.

- [ ] **Step 5: Run the ordinary kernel/app proof tests and verify GREEN**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof tests/kernel/rules tests/app/actions.test.ts tests/app/session.test.ts tests/app/moves.test.ts`

Expected: PASS except bundled theory tests, which remain for Tasks 4–5.

- [ ] **Step 6: Commit**

```bash
git add src/kernel src/app tests/kernel tests/app
git commit -m "refactor: replace graphical insertion with atomic proof steps"
```

---

### Task 3: One shared Proof spawn controller with named and bound relations

**Files:**
- Create: `src/app/interact/proof-spawn.ts`
- Modify: `src/app/interact/spawn.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/fixed-side-workspace.ts` only if debug typing requires it
- Modify: `tests/app/spawn.test.ts`
- Modify: `tests/app/closed-term-intro.test.ts`
- Create: `tests/app/proof-spawn.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- Produce one `ProofSpawnController` used by main and fixed Proof surfaces:

```ts
type ProofSpawnControllerOptions = {
  host: HTMLElement
  diagram(): Diagram
  context(): ProofContext
  commit(step: ProofStep): Diagram
  place(node: NodeId, at: Vec2): void
  refuse(text: string, pointer: Vec2): void
  binderColor(binder: RegionId): string
  hoverBinder(binder: RegionId | null): void
  openChanged(open: boolean): void
}

class ProofSpawnController {
  open(sample: PointerSample, region: RegionId): void
  close(): boolean
  dispose(): void
}
```

- Internally own exactly one `SpawnCascade` and pass the live relation map plus `boundPredicateOptions(diagram, region)`.

- [ ] **Step 1: Write failing shared-policy tests**

Test that closed term input records `closedTermIntro`, open input records `openTermSpawn`, a named row records `relationSpawn`, and a bound row records `boundRelationSpawn`. Assert placement uses the sole introduced node and refusals retain the menu without cursor mutation.

- [ ] **Step 2: Run tests and verify RED**

Run: `npx vitest run --config vitest.config.ts tests/app/spawn.test.ts tests/app/closed-term-intro.test.ts tests/app/proof-spawn.test.ts`

Expected: FAIL because Proof currently suppresses relations/binders and duplicates host callbacks.

- [ ] **Step 3: Implement `ProofSpawnController`**

Parse λ input once and dispatch by `freePorts(term).length`. For every accepted spawn, snapshot `before`, commit the atomic step, identify the sole introduced node with `introducedNodeId`, and call `place`. Relation and binder callbacks use the cascade snapshot arity for stale-option checks before synchronous commit.

- [ ] **Step 4: Integrate main Proof without duplicating Edit policy**

Keep the shell’s Edit `SpawnCascade` callbacks unchanged. Replace main Proof’s `new Map(), []` opening path with `ProofSpawnController.open`. Reuse `bubbleHues` and the existing `spawnHoverBinder` paint path. Mode changes, motion, selection transitions, and disposal close the controller.

- [ ] **Step 5: Integrate both fixed fronts through the same controller**

Replace fixed-front false callbacks and empty catalogs. Add one transient `#spawnHoverBinder` id per front; render `highlightGroup(this.#engine, theme, binder)` in that front’s overlay. Focus loss, front switches, motion, editor opening, commit/refusal cleanup, and disposal clear it.

- [ ] **Step 6: Add browser demonstrations**

In forward and backward ordinary Proof and both fixed fronts:

- load at least one named relation;
- create nested bubbles;
- open the spawn cascade in a legal atomic-spawn region;
- assert named relation rows and ordered bound rows are present;
- assert circular swatches have distinct renderer-derived colors;
- hover each bound row and assert the corresponding complete binder group is highlighted;
- spawn a named reference and a bound atom, assert owning cursor/node placement, undo/replay, and other-front isolation;
- exercise an illegal polarity and a stale option refusal.

- [ ] **Step 7: Run focused unit and browser tests**

Run: `npx vitest run --config vitest.config.ts tests/app/spawn.test.ts tests/app/proof-spawn.test.ts tests/app/proof-front.test.ts tests/app/session.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "proof spawn|bound relation|named relation"`

Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add src/app tests/app e2e/app.spec.ts
git commit -m "feat: share named and bound relation spawning with proof"
```

---

### Task 4: Migrate flat Frege insertion patterns

**Files:**
- Modify: `src/theories/frege.ts`
- Modify: `src/theories/macros.ts`
- Modify: `tests/theories/macros.test.ts`
- Test: `tests/theories/frege.test.ts`

**Interfaces:**
- Add `DerivationCursor` helpers that emit only atomic steps:
  - `spawnOpenTerm(tag, region, term): NodeId`
  - `spawnRelation(tag, region, defId): NodeId`
  - `spawnBoundRelation(tag, region, binder): NodeId`
  - reuse existing `wireOf` plus `wireJoin` steps for attachments.
- Delete `extractClosedPattern` and every macro that returns a pattern for later insertion.

- [ ] **Step 1: Change Frege tests to reject insertion steps**

Add:

```ts
for (const theorem of theory.theorems) {
  expect(theorem.steps.some((step) => (step as { rule: string }).rule === 'insertion')).toBe(false)
  expect(theorem.backSteps?.some((step) => (step as { rule: string }).rule === 'insertion') ?? false).toBe(false)
}
```

- [ ] **Step 2: Run Frege tests and verify RED**

Run: `npx vitest run --config vitest.config.ts tests/theories/frege.test.ts tests/theories/macros.test.ts`

Expected: FAIL on the four insertion steps and macro test.

- [ ] **Step 3: Replace `c2 insert IH+SUCC`**

Spawn the three open terms in `cutA` using `openTermSpawn`. Join the three `s0` wires, join `H1`/`H2` outputs, and retain the successor output singleton exactly as the old pattern did. Use explicit `wireJoin` steps so every merge replays under `cutA`’s negative polarity.

- [ ] **Step 4: Replace `c2 insert hyp pair+SUCC`**

Spawn both `PT` nodes and `SC(s0)` in `cutA`. Join their output/free wires to reproduce the old internal equivalence classes, then join the old boundary-class wire to host wire `wb`. Assert the resulting boundary-pinned canonical form at the next existing derivation checkpoint before continuing.

- [ ] **Step 5: Delete extraction/insertion macros and run GREEN**

Remove `extractClosedPattern` and replace its test with a cursor-helper test proving the atomic sequence constructs the same canonical diagram as its former flat pattern.

Run: `npx vitest run --config vitest.config.ts tests/theories/macros.test.ts tests/theories/frege.test.ts`

Expected: only the two nested guard insertions remain failing for Task 5.

- [ ] **Step 6: Commit**

```bash
git add src/theories/frege.ts src/theories/macros.ts tests/theories/macros.test.ts tests/theories/frege.test.ts
git commit -m "refactor: build flat Frege facts from atomic steps"
```

---

### Task 5: Reconstruct Frege guard skeletons from ordinary rules

**Files:**
- Modify: `src/theories/frege.ts`
- Test: `tests/theories/frege.test.ts`
- Test: `tests/theories/battery.test.ts`

**Interfaces:**
- Add one derivation helper, not a kernel/app shortcut:

```ts
function buildNatGuardSkeleton(
  e: DerivationCursor,
  tag: string,
  guardBubble: RegionId,
): { zeroWitness: NodeId; baseWire: WireId; baseAtom: NodeId; closureOuter: RegionId; closureInner: RegionId }
```

- The helper may only call `e.push` with existing atomic/structural `ProofStep` variants. It must not build or splice a `DiagramWithBoundary`.

- [ ] **Step 1: Add a guard-equivalence checkpoint test and verify RED**

Extract the former builder-produced guard body only as a test oracle. Run `buildNatGuardSkeleton` in a legal fixture and compare `exploreForm` of the resulting selected guard content with the oracle’s boundary-pinned canonical form. The test must fail before the helper exists.

- [ ] **Step 2: Build the base and closure cuts atomically**

Inside negative `guardBubble`:

1. record `relationSpawn` for `zero`;
2. record `boundRelationSpawn` for the base atom;
3. join their singleton argument wires;
4. unfold `zero` to obtain the closed `ZERO` witness on the base wire;
5. introduce a double cut around an empty selection in `guardBubble`, producing positive `closureOuter` and negative `closureInner`.

- [ ] **Step 3: Construct the positive antecedent without positive spawning**

1. iterate the base atom from `guardBubble` into `closureOuter`;
2. use `anchoredWireSplit` with the unfolded closed zero witness to move that copied endpoint onto a fresh `closureOuter`-scoped wire and duplicate the witness there;
3. use the duplicated witness as the existing `kOpen` seed to mint `SUCC(x)` in `closureOuter`;
4. fission/fold it through the existing `refoldSucc` sequence into a `succ` reference whose first argument is the fresh antecedent wire;
5. erase the temporary duplicated closed witness in positive `closureOuter`.

- [ ] **Step 4: Construct and connect the negative consequent**

Record `boundRelationSpawn` directly in negative `closureInner`, producing a fresh inner argument wire. Join that wire to the `succ` reference’s second-argument/output wire; the inner wire’s negative scope licenses `wireJoin`, and the merge retains the outer `closureOuter` scope. The result is exactly `¬(R(x) ∧ Succ(x,y) ∧ ¬R(y))` without any graphical splice.

- [ ] **Step 5: Replace both guard insertion calls**

Use `buildNatGuardSkeleton` in `deriveZeroIsNat` and `deriveSuccNat`. Since the helper unfolds the internal zero earlier than the old derivation, remove the later duplicate `relUnfold` step and continue from the returned `zeroWitness`, `baseWire`, and `baseAtom`. Preserve the existing conclusion-cut iteration, anchored split/contract, comprehension instantiation, guard folding, theorem boundaries, and names.

- [ ] **Step 6: Run guard and theory tests until GREEN**

Run: `npx vitest run --config vitest.config.ts tests/theories/frege.test.ts tests/theories/battery.test.ts tests/app/session.test.ts`

Expected: all bundled Frege theorems replay and verify; no step has rule `insertion`.

- [ ] **Step 7: Commit**

```bash
git add src/theories/frege.ts tests/theories/frege.test.ts tests/theories/battery.test.ts
git commit -m "refactor: derive Frege guards from atomic moves"
```

---

### Task 6: Remove residual insertion artifacts and regenerate authoritative outputs

**Files:**
- Delete or migrate every remaining source/test insertion reference found by `rg`
- Regenerate: `examples/frege.json`
- Modify: `tests/architecture/interaction-ownership.test.ts`
- Modify: `tests/architecture/layering.test.ts` if import boundaries changed
- Modify: `tests/scripts/emit-theories.test.ts` only when generated expectations change
- Append: `/tmp/visualproof-foundation-20260712-remove-graphical-insertion.md`

**Interfaces:**
- Prove the displaced model is absent and generated examples contain only atomic steps.

- [ ] **Step 1: Run the displacement audit and remove every hit**

Run:

```bash
rg -n "applyInsertion|rule: ['\"]insertion|case ['\"]insertion|#openTermInsertion|needsInput: ['\"]pattern|extractClosedPattern" src tests e2e scripts examples
```

Expected before cleanup: remaining obsolete hits. Delete or migrate them; do not whitelist any source, test, fixture, or generated file.

- [ ] **Step 2: Regenerate theory JSON**

Run: `npm run emit:theories`

Expected: `examples/frege.json` changes and contains `openTermSpawn`, `relationSpawn`, and `boundRelationSpawn` steps where used, with no `insertion` step.

- [ ] **Step 3: Run authoritative validation**

Run: `npm run typecheck`

Run: `npm test`

Run: `npx playwright test e2e/app.spec.ts e2e/construction.spec.ts --grep "proof spawn|bound relation|named relation|closed-term"`

Run the displacement audit again. Expected: typecheck passes; every ordinary test and targeted browser test passes; audit returns no obsolete insertion-model hits.

- [ ] **Step 4: Obtain pre-merge code review**

Review against `docs/superpowers/specs/2026-07-12-atomic-proof-spawning-design.md`. Repair every Critical and Important finding and rerun Step 3 after any change.

- [ ] **Step 5: Append foundation conformance**

Append `<conformance>` recording shared structural ownership, deleted insertion structures, migrated derivations/surfaces, generated outputs, exact validation commands/results, and proof that no legacy insertion model remains. Do not alter earlier foundation sections.

- [ ] **Step 6: Commit**

```bash
git add src tests e2e scripts examples docs/superpowers
git commit -m "chore: remove graphical insertion artifacts"
```

Do not attempt to add the `/tmp` foundation record to Git; it is session-local evidence and is appended separately.
