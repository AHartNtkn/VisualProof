# Cursebreaker Onboarding Spine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a trivial additive Seyric onboarding spine before the preserved current practice collection and make that spine the sole Seyric prerequisite closure for the first Myratic puzzle.

**Architecture:** Five new strict JSON puzzle bundles join the existing layered content package. Progression remains the only runtime authority for gates: the boundary exercises lead through `single-mark-return` and `nested-owner-introduction`, while `four-veils` is optional repetition and multi-owner practice depends on the nested-owner tutorial. Catalog, guidance, validation witnesses, and build-time coverage remain separate owners.

**Tech Stack:** TypeScript, strict JSON content, Vitest, existing diagram kernel and backward proof replay, Vite renderer build.

## Global Constraints

- Preserve every current puzzle core, witness, catalog entry, guidance entry, coverage row, and existing inter-practice prerequisite edge.
- Do not delete, replace, or rewrite any current puzzle.
- Add `two-veils`, `four-veils`, `forked-veil`, `echoed-veil`, and `empty-ring-release`.
- Mandatory Seyric closure: `two-veils -> forked-veil -> echoed-veil -> empty-ring-release -> single-mark-return -> nested-owner-introduction`.
- `four-veils` depends on `two-veils` and remains outside the Myratic closure.
- Every multi-owner optional Seyric puzzle depends transitively on `nested-owner-introduction`; single-owner practice may depend directly on `single-mark-return`.
- The first four added cut-topology records contain no nodes, bubbles, or wires. `empty-ring-release` contains one empty arity-zero bubble at odd cut depth.
- Guidance remains passive and ignorable; witnesses demonstrate feasibility and never prescribe a unique solution.
- No separate required/optional field and no authoritative puzzle count.
- Do not run the dedicated physics battery or launch the Electron desktop application.
- Do not commit changes in the existing dirty worktree.

---

### Task 1: Specify the onboarding and preservation contract

**Files:**
- Modify: `tests/game/opening-content.test.ts`
- Modify: `tests/game/catalog.test.ts`

**Interfaces:**
- Consumes: `GameCatalog`, `requiredPuzzles(catalog)`, content fingerprints, strict progression placements.
- Produces: failing executable requirements for order, topology, exact mandatory closure, optional repetition, practice-root gating, and preservation of the incumbent ID set.

- [x] **Step 1: Add a failing opening-content test**

Capture the current 100 Seyric IDs as the incumbent set, then assert the loaded culture begins with:

```ts
const onboarding = [
  'two-veils',
  'four-veils',
  'forked-veil',
  'echoed-veil',
  'empty-ring-release',
] as const

expect(catalog.puzzlesInCulture('seyric-horizon' as never).slice(0, 6)).toEqual([
  ...onboarding,
  'single-mark-return',
])
```

Assert `two-veils`, `four-veils`, `forked-veil`, and `echoed-veil` have no bubbles, nodes, or wires; `empty-ring-release` has one arity-zero bubble and no nodes or wires.

- [x] **Step 2: Add a failing progression test**

```ts
expect([...requiredPuzzles(catalog)].filter((id) => seyric.has(id))).toEqual([
  puzzleId('two-veils'),
  puzzleId('forked-veil'),
  puzzleId('echoed-veil'),
  puzzleId('empty-ring-release'),
  puzzleId('single-mark-return'),
])
expect(catalog.placement(puzzleId('four-veils')).prerequisites)
  .toEqual([puzzleId('two-veils')])
```

Assert each incumbent zero-prerequisite practice root except `single-mark-return` now has `single-mark-return` as its sole new prerequisite, while all incumbent non-root prerequisite arrays remain byte-for-byte equal to the preserved baseline inventory.

- [x] **Step 3: Run the focused tests and observe RED**

Run:

```bash
npm test -- --run tests/game/opening-content.test.ts tests/game/catalog.test.ts
```

Expected: failures reporting missing `two-veils` and the incumbent one-record mandatory closure.

---

### Task 2: Add strict semantic starts and replaying witnesses

**Files:**
- Create: `content/puzzles/two-veils.json`
- Create: `content/puzzles/four-veils.json`
- Create: `content/puzzles/forked-veil.json`
- Create: `content/puzzles/echoed-veil.json`
- Create: `content/puzzles/empty-ring-release.json`
- Create: `content/validation/two-veils.json`
- Create: `content/validation/four-veils.json`
- Create: `content/validation/forked-veil.json`
- Create: `content/validation/echoed-veil.json`
- Create: `content/validation/empty-ring-release.json`
- Modify: `content/manifest.json`
- Modify: `src/game/content/files.ts`

**Interfaces:**
- Consumes: strict diagram JSON and `ProofStep` JSON decoders.
- Produces: five new semantic puzzle IDs and five backward witnesses registered by both filesystem manifest and renderer static imports.

- [x] **Step 1: Add the cut-only starts**

Use the established historical shapes:

```text
two-veils: sheet -> cut -> cut
four-veils: sheet -> cut -> cut -> cut -> cut
forked-veil: sheet -> outer cut -> two sibling cuts
echoed-veil: sheet -> outer cut containing one leaf cut and one cut containing a leaf cut
```

Every `nodes` and `wires` object is empty.

- [x] **Step 2: Add the ring transition start**

```text
empty-ring-release: sheet -> cut -> arity-0 bubble -> cut
```

The bubble contains no bound atoms.

- [x] **Step 3: Add feasibility witnesses**

```text
two-veils: doubleCutElim
four-veils: doubleCutElim, doubleCutElim
forked-veil: erasure of either sibling, doubleCutElim
echoed-veil: deiteration of the descendant leaf cut, erasure of the remaining peer, doubleCutElim
empty-ring-release: vacuousElim, doubleCutElim
```

Set each `expectedRules` to the distinct rules in its stored witness and leave `availableArtifacts` and `recognizedStates` empty.

- [x] **Step 4: Register the files**

Prepend the five puzzle paths to `content/manifest.json`; add imports and keyed entries to `src/game/content/files.ts` without renumbering or changing existing imports.

---

### Task 3: Add layered presentation, coverage, and progression ownership

**Files:**
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/schemas/coverage.schema.json`
- Modify: `content/progression/core.json`

**Interfaces:**
- Consumes: the five new puzzle IDs and current progression graph.
- Produces: complete cross-layer bundles, passive tutorial pages, bounded onboarding coverage, folio order, practice prerequisites, and the Myratic gate.

- [x] **Step 1: Add catalog records**

Add concise finished Seyric artifact identities and provenance for the five new records without modifying any existing artifact entry.

- [x] **Step 2: Add passive guidance**

Add opening guidance that stages actual production interactions:

```text
two-veils: highlighting; selection/deselection/field clearing; double-cut elimination
forked-veil: erase one complete empty fragment; timeline rewind/branch explanation
echoed-veil: compare complete repeated cut forms and deiterate one supported echo
empty-ring-release: distinguish ring from veil; dissolve the empty ring; release the familiar pair
```

Give `four-veils` no mandatory instruction beyond optional repetition commentary. Do not change current guidance.

- [x] **Step 3: Add build-time onboarding coverage**

Extend the coverage obligation kind with `onboarding`, then add bounded obligations and rows for:

```text
bare-double-cut-elimination
repeated-double-cut-order-practice
negative-field-empty-fragment-erasure
cut-form-supported-deiteration
vacuous-ring-elimination
```

These claims document why the additive starts exist but never control runtime unlocking.

- [x] **Step 4: Rebuild progression edges**

Prepend the new IDs to the Seyric folio. Set:

```text
Seyric gateway = two-veils
two-veils prerequisites = []
four-veils prerequisites = [two-veils]
forked-veil prerequisites = [two-veils]
echoed-veil prerequisites = [forked-veil]
empty-ring-release prerequisites = [echoed-veil]
single-mark-return prerequisites = [empty-ring-release]
nested-owner-introduction prerequisites = [single-mark-return]
Myratic unlocksAfter = [nested-owner-introduction]
```

For each multi-owner Seyric root, add the minimal prerequisite edge needed to make it depend transitively on `nested-owner-introduction`. Preserve unrelated prerequisite edges.

- [x] **Step 5: Run focused tests and content validation**

Run:

```bash
npm test -- --run tests/game/opening-content.test.ts tests/game/catalog.test.ts tests/game/content-validation.test.ts tests/game/progress.test.ts
npm run content:validate
```

Expected: all focused tests pass and all 106 registered records replay successfully.

---

### Task 4: Prove preservation and runtime integration

**Files:**
- Modify: `tests/game/content-validation.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts` only if existing archive assertions do not exercise the new gateway order and passive pages.
- Modify: `docs/superpowers/specs/2026-07-19-seyric-first-principles-content-design.md`
- Modify: `docs/superpowers/receipts/2026-07-19-seyric-first-principles-content-reconstruction.md`

**Interfaces:**
- Consumes: the completed content package and its pre-change incumbent inventory evidence.
- Produces: direct preservation checks and documentation that distinguishes onboarding value from optional-practice value.

- [x] **Step 1: Add semantic preservation assertions**

Assert the incumbent 100 IDs all remain registered, their saved baseline fingerprints remain unchanged, and none of their core/validation/catalog/guidance/coverage records is missing. Assert no optional record appears in the first-Myratic prerequisite closure.

- [x] **Step 2: Add or update archive/guidance browser coverage**

Exercise fresh startup projection, the locked/unlocked onboarding sequence, passive multi-page guidance, and the persistence of the full current practice collection after `single-mark-return`. Do not launch Electron; use the existing headless browser harness.

- [x] **Step 3: Correct active design and receipt documentation**

State that empty cut topology is deliberate onboarding content, the five additive records precede the preserved practice collection, and the mandatory/practice distinction remains derived solely from progression.

- [x] **Step 4: Run final verification**

Run:

```bash
npm test -- --run tests/game/opening-content.test.ts tests/game/catalog.test.ts tests/game/content-validation.test.ts tests/game/progress.test.ts tests/game/authoritative-runtime-browser.test.ts
npm run content:validate
npm run typecheck
npm run build:renderer
git diff --check
```

Expected: every command exits zero; the browser test remains headless; no physics or Electron desktop command runs.
