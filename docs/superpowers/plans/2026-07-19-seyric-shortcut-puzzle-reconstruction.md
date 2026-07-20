# Seyric Shortcut-Puzzle Reconstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the repeated empty-cut shortcut family with distinct Seyric problems that preserve each assigned point, while leaving `echoed-veil` untouched and adding a proper elementary deiteration introduction.

**Architecture:** Puzzle JSON remains the runtime authority and validation sidecars remain the proof authority. Reconstruction replaces complete puzzle bundles—diagram, witness, coverage, guidance, catalog prose, and prerequisites—rather than patching incumbent silhouettes. The content validator gains a structural shortcut audit; canonicalization continues to reject isomorphic starts, while a focused review receipt records the nearest experiential neighbor and the genuinely different player decision.

**Tech Stack:** TypeScript, Vitest, JSON Schema 2020-12, AJV, the existing existential-graph kernel, canonical `exploreForm` fingerprints, framework-free game content loading.

## Global Constraints

- Do not modify any `echoed-veil` authored surface: puzzle, validation, guidance, catalog, coverage, progression, or runtime projection.
- Preserve the point, puzzle ID, and artifact identity of reconstructed puzzles; topology, size, silhouette, witness, and prerequisites may change dramatically.
- Alternative proofs remain welcome. Do not enforce an intended solution or forbid a different valid route.
- For creative-rule puzzles, prove causal create/consume materiality on pre-existing content; do not require the authored route, rank it against alternatives, or reject another valid route for being shorter.
- No reconstructed puzzle may duplicate an existing canonical start or an existing player-facing decision.
- Permit the identified empty-cut shortcut only in `forked-veil`, unchanged `echoed-veil`, and the deliberately intimidating `atomic-fragment-erasure`.
- Keep every Seyric goal in the pure propositional culture boundary: arity-zero bubbles in negative context, atom nodes only, and no wires.
- Do not target or preserve a puzzle count.
- Do not change proof rules, proof physics, interaction mechanics, packaging, or Electron startup.
- Do not run `test:physics` or launch Electron.
- Finish every accepted task with a commit and an empty worktree.

---

### Task 1: Replace Frozen-Incumbent Tests and Add the Shortcut Detector

**Files:**
- Modify: `scripts/validate-game-content.ts`
- Modify: `tests/game/content-validation.test.ts`
- Modify: `tests/game/opening-content.test.ts`

**Interfaces:**
- Consumes: `Diagram`, `RegionId`, and `cutDepth(diagram, region)` from the kernel.
- Produces: `findEmptyCutShortcutHosts(diagram: Diagram): readonly RegionId[]`, a pure detector used by the final catalog audit.

- [ ] **Step 1: Delete the obsolete incumbent-preservation assertions**

Remove the tests named:

```text
preserves every incumbent Seyric bundle while adding onboarding beside it
prepends the additive onboarding spine and preserves every incumbent semantic start
```

They encode the displaced model that incumbent puzzle bytes and fingerprints are the authority. Retain the tests for closed propositional content, canonical uniqueness, coverage completeness, and progression ownership.

- [ ] **Step 2: Write the detector tests**

Add synthetic cases to `tests/game/content-validation.test.ts` using `DiagramBuilder`:

```ts
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { findEmptyCutShortcutHosts, validateGameContent } from '../../scripts/validate-game-content'

it('finds a negative host where an empty cut makes competing content disposable', () => {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const owner = builder.bubble(outer, 0)
  builder.atom(owner, owner)
  builder.cut(owner)

  expect(findEmptyCutShortcutHosts(builder.build())).toEqual([owner])
})

it('does not flag an empty cut without competing content', () => {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  builder.cut(outer)

  expect(findEmptyCutShortcutHosts(builder.build())).toEqual([])
})

it('does not flag a nonempty cut', () => {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const owner = builder.bubble(outer, 0)
  const marked = builder.cut(owner)
  builder.atom(marked, owner)
  builder.atom(owner, owner)

  expect(findEmptyCutShortcutHosts(builder.build())).toEqual([])
})
```

- [ ] **Step 3: Run the focused tests and observe the missing export**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL because `findEmptyCutShortcutHosts` is not exported.

- [ ] **Step 4: Implement the pure structural detector without enabling the catalog gate yet**

Add `Diagram` and `RegionId` type imports and this implementation to `scripts/validate-game-content.ts`:

```ts
const directChildRegions = (diagram: Diagram, parent: RegionId): RegionId[] =>
  Object.entries(diagram.regions)
    .filter(([, region]) => region.kind !== 'sheet' && region.parent === parent)
    .map(([id]) => id)

const directNodeCount = (diagram: Diagram, region: RegionId): number =>
  Object.values(diagram.nodes).filter((node) => node.region === region).length

const isEmptyCut = (diagram: Diagram, region: RegionId): boolean =>
  diagram.regions[region]?.kind === 'cut'
  && directChildRegions(diagram, region).length === 0
  && directNodeCount(diagram, region) === 0

export function findEmptyCutShortcutHosts(diagram: Diagram): readonly RegionId[] {
  const hosts: RegionId[] = []
  for (const id of Object.keys(diagram.regions)) {
    if (cutDepth(diagram, id) % 2 === 0) continue
    const children = directChildRegions(diagram, id)
    const emptyCuts = children.filter((child) => isEmptyCut(diagram, child))
    if (emptyCuts.length === 0) continue
    const competingRegions = children.filter((child) => !emptyCuts.includes(child))
    if (competingRegions.length > 0 || directNodeCount(diagram, id) > 0) hosts.push(id)
  }
  return hosts
}
```

Do not call it from `validateGameContent` yet; the production catalog intentionally remains red until reconstruction is complete.

- [ ] **Step 5: Run focused validation**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts tests/game/opening-content.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add scripts/validate-game-content.ts tests/game/content-validation.test.ts tests/game/opening-content.test.ts
git commit -m "test(game): detect empty-cut puzzle shortcuts"
```

---

### Task 2: Add the Elementary Marked-Echo Deiteration Puzzle

**Files:**
- Create: `content/puzzles/marked-echo-deiteration.json`
- Create: `content/validation/marked-echo-deiteration.json`
- Modify: `content/manifest.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/progression/core.json`
- Modify: `src/game/content/files.ts`
- Modify: `tests/game/opening-content.test.ts`
- Modify: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: the existing puzzle/validation/catalog/coverage/guidance/progression schemas.
- Produces: puzzle ID `marked-echo-deiteration` and a deiteration-first four-step witness.

- [ ] **Step 1: Write the failing catalog and ordering tests**

Add to `tests/game/opening-content.test.ts`:

```ts
it('introduces marked ancestor-supported deiteration after mark ownership', () => {
  const id = puzzleId('marked-echo-deiteration')
  const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
  expect(seyric.indexOf(id)).toBe(seyric.indexOf(puzzleId('single-mark-return')) + 1)
  expect(catalog.placement(id).prerequisites).toEqual([puzzleId('single-mark-return')])

  const diagram = catalog.puzzle(id).diagram
  expect(Object.values(diagram.regions).filter(({ kind }) => kind === 'bubble')).toHaveLength(1)
  expect(Object.values(diagram.nodes).filter(({ kind }) => kind === 'atom')).toHaveLength(2)
})
```

Add a content-validation assertion that the new witness starts with deiteration:

```ts
it('gives the marked echo an ordinary deiteration-first witness', () => {
  const evidence = readJson(resolve(
    process.cwd(), 'content/validation/marked-echo-deiteration.json',
  ))
  expect(evidence.solution.map(({ rule }: JsonRecord) => rule)).toEqual([
    'deiteration', 'erasure', 'vacuousElim', 'doubleCutElim',
  ])
})
```

- [ ] **Step 2: Run the focused tests and observe the missing bundle**

Run:

```bash
npm test -- --run tests/game/opening-content.test.ts tests/game/content-validation.test.ts
```

Expected: FAIL because `marked-echo-deiteration` and its validation sidecar do not exist.

- [ ] **Step 3: Add the exact puzzle and witness**

Create `content/puzzles/marked-echo-deiteration.json`:

```json
{
  "id": "marked-echo-deiteration",
  "diagram": {
    "root": "r0",
    "regions": {
      "r0": { "kind": "sheet" },
      "r1": { "kind": "cut", "parent": "r0" },
      "r2": { "kind": "bubble", "parent": "r1", "arity": 0 },
      "r3": { "kind": "cut", "parent": "r2" },
      "r4": { "kind": "cut", "parent": "r2" },
      "r5": { "kind": "cut", "parent": "r4" }
    },
    "nodes": {
      "n0": { "kind": "atom", "region": "r3", "binder": "r2" },
      "n1": { "kind": "atom", "region": "r5", "binder": "r2" }
    },
    "wires": {}
  }
}
```

Create `content/validation/marked-echo-deiteration.json`:

```json
{
  "puzzle": "marked-echo-deiteration",
  "solution": [
    {
      "rule": "deiteration",
      "sel": { "region": "r4", "regions": ["r5"], "nodes": [], "wires": [] },
      "fuel": 100
    },
    {
      "rule": "erasure",
      "sel": { "region": "r2", "regions": ["r3"], "nodes": [], "wires": [] }
    },
    { "rule": "vacuousElim", "region": "r2" },
    { "rule": "doubleCutElim", "region": "r1" }
  ],
  "availableArtifacts": [],
  "expectedRules": ["deiteration", "erasure", "vacuousElim", "doubleCutElim"],
  "recognizedStates": []
}
```

- [ ] **Step 4: Register the complete content bundle**

Make these exact semantic additions:

```json
// catalog artifact
{
  "puzzle": "marked-echo-deiteration",
  "name": {
    "professional": "Seyric Marked-Echo Practice Tablet",
    "curatorShorthand": "marked echo"
  },
  "provenance": {
    "summary": "A compact Seyric workshop tablet carrying the same owned mark in an older veil and in a deeper repeated veil.",
    "function": "Trained recognition that an exact descendant repetition may be lifted only while its older matching support remains."
  }
}

// coverage obligation
{
  "id": "marked-fragment-supported-deiteration",
  "kind": "onboarding",
  "family": "onboarding-structural-editing",
  "distinction": "Remove an exact marked descendant fragment supported by the same marked fragment in an ancestor field.",
  "stoppingRule": "Stop after one owner, one ancestor support, and one descendant echo isolate binder-preserving deiteration."
}

// coverage row
{
  "puzzle": "marked-echo-deiteration",
  "obligations": ["marked-fragment-supported-deiteration"],
  "visibleSituation": "One ring owns two identical marked veils: an older support and a repeated descendant inside a deeper field.",
  "defeats": "It defeats the hypothesis that visual similarity alone is enough: the removable occurrence is the exact descendant under the same owner and ancestor support.",
  "experientialNeighbors": ["echoed-veil", "single-mark-return", "transfer-duplication-recognition"]
}
```

Add one passive opening guidance page:

```json
{
  "puzzle": "marked-echo-deiteration",
  "interventions": [
    {
      "id": "opening-marked-echo-deiteration",
      "trigger": { "kind": "opening" },
      "repeat": "once",
      "pages": [
        "The deeper marked veil exactly repeats the older marked veil under the same ring. Because the older occurrence remains in an ancestor field, the descendant echo may be lifted."
      ]
    }
  ]
}
```

Insert the puzzle after `single-mark-return` in the manifest, Seyric culture order, and runtime content map. Add a placement with prerequisite `single-mark-return`. Do not alter any `echoed-veil` entry or the Myratic unlock requirement.

- [ ] **Step 5: Run content validation and focused tests**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/opening-content.test.ts tests/game/content-validation.test.ts tests/game/layered-content.test.ts
npm run typecheck
```

Expected: PASS, with the content receipt reporting one additional puzzle and solution.

- [ ] **Step 6: Commit**

```bash
git add content src/game/content/files.ts tests/game/opening-content.test.ts tests/game/content-validation.test.ts
git commit -m "feat(game): add marked-echo deiteration introduction"
```

---

### Task 3: Reconstruct the Atomic Edit and Polarity Problems

**Files:**
- Modify: `content/puzzles/shallow-edit-legality-contrast.json`
- Modify: `content/validation/shallow-edit-legality-contrast.json`
- Modify: `content/puzzles/atomic-content-insertion.json`
- Modify: `content/validation/atomic-content-insertion.json`
- Modify: `content/puzzles/atomic-double-cut-selection.json`
- Modify: `content/validation/atomic-double-cut-selection.json`
- Modify: `content/puzzles/polarity-bubble-contrast.json`
- Modify: `content/validation/polarity-bubble-contrast.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/progression/core.json`
- Test: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: `findEmptyCutShortcutHosts`, canonical puzzle fingerprints, and ordinary backward proof steps.
- Produces: four valid, shortcut-free, canonically distinct starts whose primary decisions are respectively host legality, atomic insertion, exact atomic wrapping, and parity through ownership rings.

**Post-review evidence amendment:** The first implementation proved that checking only
for a rule name is too weak. Three bounded implementation searches and five independent
evidence probes also proved that closure and proof-length dominance requirements are
both infeasible for the explored families and inconsistent with the established
open-problem model. This amendment governs Steps 1–3 wherever earlier text conflicts.

- [ ] **Step 1: Add failing per-point assertions**

Add a shared assertion to `tests/game/content-validation.test.ts`:

```ts
const shortcutFree = [
  'shallow-edit-legality-contrast',
  'atomic-content-insertion',
  'atomic-double-cut-selection',
  'polarity-bubble-contrast',
] as const

it('keeps reconstructed atomic and polarity problems free of empty-cut truth witnesses', () => {
  const catalog = loadGameContent(gameContentFiles)
  for (const id of shortcutFree) {
    expect(findEmptyCutShortcutHosts(catalog.puzzle(id as never).diagram), id).toEqual([])
  }
})
```

For each final topology, add a real-kernel causal counterfactual: its named consumer
on pre-existing puzzle content must fail immediately before the creative step,
succeed after it because of the created resource, and fail after the documented
nearby/wrong/larger counterfactual. Track semantic descendants rather than relying
only on a fresh serialized ID. Do not assert that no other proof exists or compare
proof lengths.

- [ ] **Step 2: Run the focused test and observe the missing causal evidence**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL because rule-name presence does not prove causal use and
`shallow-edit-legality-contrast` introduces and removes decoration without unlocking
work on pre-existing content. `polarity-bubble-contrast` remains approved.

- [ ] **Step 3: Reconstruct each complete bundle from its point**

Use the following non-negotiable structural contracts:

```text
shallow-edit-legality-contrast:
  Rebuild as an asymmetric shallow bridge. One legal insertion must create a
  downstream relationship and both compared hosts must contribute. Reject the
  reviewed destructive route that reduces the start to ancestor deiteration.

atomic-content-insertion:
  Insert one atom into a positive field inside an asymmetric compound or cyclic bridge.
  The atom must create an exact relationship consumed later.
  Do not use the disproven compact homologous-deficit family.
  No pre-existing false conjunct or independently sufficient branch is allowed.

atomic-double-cut-selection:
  Double-cut introduction must wrap one exact atom inside a compound interlock and
  create authority or an annulus used by a later constructive operation.
  A nearby atom and a larger selectable fragment must produce different consequences.
  Do not use a clean wrapper/match source that can be eliminated to expose the same authority.

polarity-bubble-contrast:
  Similar owned marks must appear at different cut parity through one or more bubbles.
  Both sides must be needed; removing either complete side may not leave a theorem.
```

For each candidate, use a temporary `npx tsx --eval` spike with `DiagramBuilder`, `applyStep(..., 'backward')`, and `isBlank` before replacing the JSON. Compare its `exploreForm` against every catalog start before accepting it. Prove the causal pre/post/counterfactual contract on pre-existing content; do not search for or rank every alternative proof. Then replace the puzzle diagram and entire validation witness, and rewrite its coverage `visibleSituation`, `defeats`, and `experientialNeighbors` to name the nearest real neighbors and the different player decision.

Set prerequisites exactly as follows and do not make the new puzzle part of the
Myratic unlock closure:

```text
shallow-edit-legality-contrast -> single-mark-return
atomic-content-insertion -> marked-echo-deiteration
atomic-double-cut-selection -> marked-echo-deiteration
polarity-bubble-contrast -> marked-echo-deiteration
```

- [ ] **Step 4: Run focused content verification**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/content-validation.test.ts tests/game/opening-content.test.ts tests/game/layered-content.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add content tests/game/content-validation.test.ts
git commit -m "feat(game): reconstruct atomic Seyric edit problems"
```

---

### Task 4: Reconstruct Compound Copy and Double-Cut Problems

**Files:**
- Modify: `content/puzzles/compound-copy-authority-contrast.json`
- Modify: `content/validation/compound-copy-authority-contrast.json`
- Modify: `content/puzzles/compound-double-cut-selection.json`
- Modify: `content/validation/compound-double-cut-selection.json`
- Modify: `content/puzzles/content-bearing-annulus-choice.json`
- Modify: `content/validation/content-bearing-annulus-choice.json`
- Modify: `content/puzzles/double-cut-insertion-workspace.json`
- Modify: `content/validation/double-cut-insertion-workspace.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/progression/core.json`
- Test: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: the shortcut detector and marked-echo deiteration prerequisite.
- Produces: four shortcut-free compound problems with different primary decisions.

- [ ] **Step 1: Extend the shortcut and materiality table**

Add these exact operation mappings to the Task 3 semantic test data:

```ts
const compoundPrimaryRule = new Map([
  ['compound-copy-authority-contrast', 'iteration'],
  ['compound-double-cut-selection', 'doubleCutIntro'],
  ['content-bearing-annulus-choice', 'doubleCutElim'],
  ['double-cut-insertion-workspace', 'insertion'],
])
```

Assert every listed start has no shortcut host. For each creative mapping, add the
same causal pre/post/counterfactual evidence on pre-existing content. For
`content-bearing-annulus-choice`, prove instead that the selected elimination
preserves content consumed later and that the obstructed near-match cannot perform
the same transition.

- [ ] **Step 2: Run the focused test and observe the current violations**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL for all four current starts.

- [ ] **Step 3: Reconstruct the four bundles with distinct decisions**

```text
compound-copy-authority-contrast:
  One coherent compound source has a legal descendant target and a similar-looking
  target without ancestor authority. The legal iteration supplies content consumed
  downstream. This is an authority decision, not an exact-duplicate removal problem.

compound-double-cut-selection:
  Wrapping an intact compound creates a needed workspace. Wrapping an internal atom
  cannot be repaired into the same state by one cleanup move. Internal grouping must
  remain relevant after the wrap.

content-bearing-annulus-choice:
  An eligible content-bearing double cut and an obstructed near-match coexist.
  Eliminating the eligible pair preserves content needed later. No empty cut proves
  the whole statement; annulus emptiness is only the local eligibility condition.

double-cut-insertion-workspace:
  Double-cut introduction creates an annulus with the polarity required for a useful
  insertion, and the inserted fragment participates in a later exact match or
  discharge. This differs from selection puzzles because the decision is why the
  temporary workspace is needed.
```

Prototype and replay each graph against the real kernel before editing JSON. Reject a candidate if its primary decision, nearest-error contrast, and downstream use match any existing puzzle even when its canonical form differs.

Set prerequisites exactly:

```text
compound-copy-authority-contrast -> marked-echo-deiteration
compound-double-cut-selection -> atomic-double-cut-selection
content-bearing-annulus-choice -> compound-double-cut-selection
double-cut-insertion-workspace -> atomic-double-cut-selection, atomic-content-insertion
```

- [ ] **Step 4: Run focused verification**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/content-validation.test.ts tests/game/catalog.test.ts tests/game/layered-content.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add content tests/game/content-validation.test.ts
git commit -m "feat(game): reconstruct compound Seyric workspace problems"
```

---

### Task 5: Reconstruct Grouped Construction and Vacuous Ownership

**Files:**
- Modify: `content/puzzles/grouped-branch-construction.json`
- Modify: `content/validation/grouped-branch-construction.json`
- Modify: `content/puzzles/useful-vacuous-owner-workspace.json`
- Modify: `content/validation/useful-vacuous-owner-workspace.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/progression/core.json`
- Test: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: existing insertion and vacuous-bubble rules without engine changes.
- Produces: two shortcut-free problems whose boundary types and downstream uses are distinct.

- [ ] **Step 1: Add failing assertions**

Extend the shortcut-free set and semantic operation table:

```ts
['grouped-branch-construction', 'insertion']
['useful-vacuous-owner-workspace', 'vacuousIntro']
```

Assert exact nearest neighbors:

```ts
const coverage = readJson(resolve(process.cwd(), 'content/coverage/seyric.json'))
const row = (id: string): JsonRecord => coverage.puzzles.find(
  ({ puzzle }: JsonRecord) => puzzle === id,
)
expect(row('grouped-branch-construction').experientialNeighbors).toEqual(
  expect.arrayContaining(['atomic-content-insertion', 'left-injection-introduction']),
)
expect(row('useful-vacuous-owner-workspace').experientialNeighbors).toEqual(
  expect.arrayContaining(['double-cut-insertion-workspace', 'nested-owner-introduction']),
)
```

Also add causal pre/post/counterfactual evidence for each created resource on
pre-existing content. A witness containing `insertion` or `vacuousIntro` is not
evidence by itself, and alternative proof length is not part of this test.

- [ ] **Step 2: Run the focused test and observe both violations**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL for both current starts.

- [ ] **Step 3: Rebuild both complete bundles**

```text
grouped-branch-construction:
  Insert a compound branch as one semantic unit into a genuine alternative or
  downstream consumer. Its internal conjunction must survive and matter. Reject any
  candidate equivalent to atomic insertion with two adjacent atoms.

useful-vacuous-owner-workspace:
  Introduce a vacuous bubble around selected content to enable an ownership-sensitive
  open-pattern operation unavailable beforehand. The later operation must use the
  bubble boundary itself. Reject any candidate whose bubble can be replaced by a
  double cut without changing the decision.
```

Prototype both witnesses with the real kernel, compare canonical starts with the full catalog, and rewrite their coverage and catalog prose around the final diagrams.

Set prerequisites exactly:

```text
grouped-branch-construction -> atomic-content-insertion, left-injection-introduction
useful-vacuous-owner-workspace -> empty-ring-release, marked-echo-deiteration
```

- [ ] **Step 4: Run focused verification**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/content-validation.test.ts tests/game/catalog.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add content tests/game/content-validation.test.ts
git commit -m "feat(game): reconstruct grouped and ownership puzzles"
```

---

### Task 6: Reauthor the Intimidating Whole-Fragment Erasure Puzzle

**Files:**
- Modify: `content/puzzles/atomic-fragment-erasure.json`
- Modify: `content/validation/atomic-fragment-erasure.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/progression/core.json`
- Test: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: the selected exception policy and existing whole-subgraph erasure.
- Produces: the one deliberately intimidating optional counterpart to `forked-veil`.

- [ ] **Step 1: Write the failing intentional-exception test**

Add:

```ts
it('keeps the intimidating erasure puzzle structurally distinct from forked-veil', () => {
  const catalog = loadGameContent(gameContentFiles)
  const intimidating = catalog.puzzle('atomic-fragment-erasure' as never).diagram
  const simple = catalog.puzzle('forked-veil' as never).diagram

  expect(catalog.puzzleFingerprint('atomic-fragment-erasure' as never))
    .not.toBe(catalog.puzzleFingerprint('forked-veil' as never))
  expect(Object.keys(intimidating.nodes).length).toBeGreaterThan(Object.keys(simple.nodes).length)
  expect(Object.keys(intimidating.regions).length).toBeGreaterThan(
    Object.keys(simple.regions).length + 4,
  )
  expect(findEmptyCutShortcutHosts(intimidating)).not.toEqual([])
})
```

- [ ] **Step 2: Run the test and observe that the current puzzle is not intimidating**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL on the required structural complexity.

- [ ] **Step 3: Rebuild the puzzle around deliberate recognition**

Construct one coherent compound semantic branch whose internal grouping suggests work
but whose entire root is irrelevant beside the small sufficient branch. The authored
witness must begin by erasing that complete compound fragment. Do not add repeated
operators merely to increase size; every internal component must belong to one
recognizable compound proposition.

Move it immediately after `compound-weakening-boundary` in Seyric folio order and set
its sole prerequisite to `compound-weakening-boundary`, so it remains optional after
whole-compound selection is familiar. Rewrite its coverage point from merely atomic deletion to intimidating
whole-fragment recognition, and name `forked-veil` as its experiential neighbor with
the contrast that the early puzzle erases one tiny veil while this puzzle requires
recognizing a large semantic unit as disposable.

- [ ] **Step 4: Run focused verification**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/content-validation.test.ts tests/game/opening-content.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add content tests/game/content-validation.test.ts
git commit -m "feat(game): reauthor intimidating fragment erasure"
```

---

### Task 7: Enable the Production Shortcut Gate and Record Experiential Review

**Files:**
- Modify: `scripts/validate-game-content.ts`
- Modify: `tests/game/content-validation.test.ts`
- Create: `docs/superpowers/receipts/2026-07-19-seyric-shortcut-puzzle-reconstruction.md`

**Interfaces:**
- Consumes: all reconstructed starts and `findEmptyCutShortcutHosts`.
- Produces: production content rejection for unapproved shortcut puzzles and a durable nearest-neighbor review.

- [ ] **Step 1: Write the failing production-gate mutation test**

Add a fixture mutation that inserts an empty cut into the negative bubble of
`single-mark-return` and expects validation to reject it:

```ts
it('rejects an unapproved empty-cut truth witness with competing content', () => {
  expect(() => validateFixture((root) => {
    const path = join(root, 'puzzles/single-mark-return.json')
    const puzzle = readJson(path)
    puzzle.diagram.regions.r_shortcut = { kind: 'cut', parent: 'r2' }
    writeJson(path, puzzle)
  })).toThrow(/empty-cut shortcut.*single-mark-return/i)
})
```

- [ ] **Step 2: Run the focused test and observe that validation still accepts it**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts
```

Expected: FAIL because `validateGameContent` does not call the detector.

- [ ] **Step 3: Enable the catalog gate**

After canonical duplicate validation, add:

```ts
const permittedShortcutPuzzles = new Set<PuzzleId>([
  puzzleId('forked-veil'),
  puzzleId('echoed-veil'),
  puzzleId('atomic-fragment-erasure'),
])
for (const id of seyricIds) {
  const hosts = findEmptyCutShortcutHosts(catalog.puzzle(id).diagram)
  if (hosts.length > 0 && !permittedShortcutPuzzles.has(id)) {
    throw new GameDomainError(
      `empty-cut shortcut in '${id}' at negative host(s): ${hosts.join(', ')}`,
    )
  }
}
```

- [ ] **Step 4: Perform the cross-catalog experiential review**

Create the receipt with one row for each reconstructed or new puzzle:

```markdown
| Puzzle | Preserved point | Nearest existing puzzle | Different initial situation | Different meaningful decision | Shortcut review |
|---|---|---|---|---|---|
```

Populate every cell from the final diagrams and coverage rows. A row fails review if
the difference is only owner renaming, operand count, larger internal syntax, or
layout. Revise the puzzle before accepting such a row. Include the independent
reviewer's verdict for each row and the final canonical fingerprint audit result.

- [ ] **Step 5: Prove `echoed-veil` remained untouched**

Run:

```bash
git diff 99d2d88 -- content/puzzles/echoed-veil.json content/validation/echoed-veil.json content/guidance/cursebreaker.json content/catalog/cursebreaker.json content/coverage/seyric.json content/progression/core.json
```

The shared files will contain unrelated puzzle edits, so inspect only the
`echoed-veil` entries in that diff. There must be no changed line inside any
`echoed-veil` object or progression position. Also compare the puzzle and validation
files directly; they must produce no diff.

- [ ] **Step 6: Run focused validation**

Run:

```bash
npm run content:validate
npm test -- --run tests/game/content-validation.test.ts tests/game/opening-content.test.ts tests/game/layered-content.test.ts tests/game/catalog.test.ts
npm run typecheck
```

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add scripts/validate-game-content.ts tests/game/content-validation.test.ts docs/superpowers/receipts/2026-07-19-seyric-shortcut-puzzle-reconstruction.md
git commit -m "test(game): enforce distinct Seyric puzzle structures"
```

---

### Task 8: Full Validation, Independent Review, and Clean Handoff

**Files:**
- Modify only files required to repair failures caused by Tasks 1–7.
- Append conformance evidence to `/tmp/cursebreaker-tautological-shortcut-redesign-foundation-20260719.md` outside the repository.

**Interfaces:**
- Consumes: the complete reconstructed content collection.
- Produces: a validated, reviewed, committed, clean branch.

- [ ] **Step 1: Run authoritative content and static validation**

Run:

```bash
npm run content:validate
npm run assets:validate
npm run typecheck
npm run build:renderer
git diff --check
```

Expected: all commands exit zero.

- [ ] **Step 2: Run the focused game-content suite**

Run:

```bash
npm test -- --run tests/game/content-validation.test.ts tests/game/opening-content.test.ts tests/game/layered-content.test.ts tests/game/catalog.test.ts tests/game/runtime-catalog-fixture.test.ts tests/game/progress.test.ts tests/game/save.test.ts
```

Expected: PASS.

- [ ] **Step 3: Run the complete non-physics suite**

Run:

```bash
npm test -- --maxWorkers=4 --minWorkers=1
```

Expected: every test passes. Do not run the dedicated physics battery.

- [ ] **Step 4: Request independent content and code review**

The reviewer must inspect:

```text
- every reconstructed diagram and witness against its preserved point;
- canonical uniqueness output;
- the experiential review receipt and nearest-neighbor comparisons;
- the shortcut allowlist and mutation test;
- progression dependencies and Myratic unlock closure;
- absence of any echoed-veil change;
- absence of padding-only complexity in atomic-fragment-erasure.
```

Repair every Critical or Important finding and rerun affected validation.

- [ ] **Step 5: Commit any review fixes**

```bash
git status --short
git add content scripts/validate-game-content.ts tests/game/content-validation.test.ts tests/game/opening-content.test.ts tests/game/layered-content.test.ts tests/game/catalog.test.ts docs/superpowers/receipts/2026-07-19-seyric-shortcut-puzzle-reconstruction.md
git commit -m "fix(game): address Seyric reconstruction review"
```

Skip this commit only when review produces no changes.

- [ ] **Step 6: Append foundation conformance and verify cleanliness**

Append a `<conformance>` section recording reconstructed owners, the unchanged
`echoed-veil` evidence, the new deiteration bundle, removed shortcut structures,
canonical and experiential review results, validation commands, commit IDs, and the
final clean status.

Run:

```bash
git status --short
```

Expected: no output.
