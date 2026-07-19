# Seyric First-Principles Content Reconstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the quota-shaped Seyric inventory with one validated collection whose puzzles are justified by the approved isolated and mixed obligations, whose optional records never gate progress, and whose runtime data contains no curriculum-role authority.

**Architecture:** Perform the content judgment in scratch before mutating production: inventory current starts, classify them against the approved obligation model, construct only missing starts, and adversarially review the resulting collection. Then migrate the strict JSON package in one direction from curriculum v1 to progression/coverage v2, integrate only the accepted complete bundles, delete stale records and authorities, and validate the entire package directly.

**Tech Stack:** TypeScript 5.5, strict JSON, AJV 2020-12 schemas, Vitest, `tsx`, the existing diagram canonicalizer and backward proof replay, Vite renderer build.

## Global Constraints

- Puzzle count is an output only; no task may allocate, retain, delete, or add a record to approach a number.
- Existing IDs, folio positions, roadmap slots, role labels, and prior effort have no authority.
- Alternative solutions are welcome. A stored witness proves feasibility only.
- Optional practice never gates a puzzle, a culture, or a gateway.
- Canonical inequality does not prove experiential novelty.
- A mixed record is warranted only by a changed legality, dependency, scope, source/target choice, matching problem, consequence, or bounded-generalization threshold.
- Exchange and reassociation are recognition topics; do not invent a local transformation move.
- Manifested artifacts are ordinary diagram content; do not invent provenance or persistent causal identity.
- Do not change proof physics, logical moves, UI mechanics, desktop packaging, or unrelated presentation.
- Do not run `npm run test:physics` or launch the desktop application.
- Preserve all unrelated dirty-worktree changes. Shared production registries are edited only by the lead integrator.

---

### Task 1: Produce the current-content evidence inventory

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/current-inventory.json`
- Create in scratch: `/tmp/seyric-reconstruction/current-inventory.md`
- Create in scratch: `/tmp/seyric-reconstruction/inventory-probe.ts`

**Interfaces:**
- Consumes: `content/manifest.json`, every registered current puzzle and validation sidecar, `loadGameContent`, `exploreForm`, and the approved obligation tables in `docs/superpowers/specs/2026-07-19-seyric-first-principles-content-design.md`.
- Produces: one immutable row per current Seyric ID with `id`, `order`, `fingerprint`, `closed`, `propositional`, `witnessReplays`, `catalogFunction`, `currentRoles`, and exact duplicate group; plus a report grouping likely experiential neighbors by formula family and dependency topology.

- [ ] **Step 1: Write the scratch inventory probe**

The probe must load production content and emit rows in this shape:

```ts
type CurrentPuzzleRow = {
  id: string
  order: number
  fingerprint: string
  closed: boolean
  propositional: boolean
  witnessReplays: boolean
  catalogFunction: string
  currentRoles: readonly string[]
  exactDuplicates: readonly string[]
}
```

Use `catalog.puzzleFingerprint(id)` for canonical grouping and `validateGameContent()` for witness evidence. Do not infer acceptance from any boolean in this row.

- [ ] **Step 2: Run the probe**

Run: `npx tsx /tmp/seyric-reconstruction/inventory-probe.ts`

Expected: exit 0; every registered Seyric ID appears exactly once; `current-inventory.json` and `current-inventory.md` are written under `/tmp/seyric-reconstruction/`.

- [ ] **Step 3: Verify the inventory is observational**

Run:

```bash
rg -n "accept|retain|reject|target count|required total" /tmp/seyric-reconstruction/current-inventory.json
```

Expected: no matches. The inventory records facts only.

---

### Task 2: Derive the ideal-to-current classification

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/obligations.json`
- Create in scratch: `/tmp/seyric-reconstruction/classification.json`
- Create in scratch: `/tmp/seyric-reconstruction/classification.md`

**Interfaces:**
- Consumes: the approved isolated and mixed tables from the design spec and Task 1's factual inventory.
- Produces: a count-independent ideal obligation set and one classification per current ID: `equivalent`, `redundant`, `invalidForSeyric`, or `uncoveredByIdeal`. `equivalent` rows name visible obligations; `redundant` rows name the experiential neighbor that already provides equivalent value; `invalidForSeyric` rows name the violated fixed semantic boundary; `uncoveredByIdeal` rows explain why the incumbent record has no first-principles warrant.

- [ ] **Step 1: Encode the approved obligations without current IDs**

Each obligation uses this exact shape:

```json
{
  "id": "projection-compound",
  "kind": "isolated",
  "family": "projection",
  "distinction": "Project a grouped conjunct as one intact proposition.",
  "stoppingRule": "Further internal complexity adds no new selection decision."
}
```

Write all obligations before reading `current-inventory.json`. Do not include puzzle IDs, roles, counts, or planned folio positions in `obligations.json`.

- [ ] **Step 2: Classify current rows against the frozen obligations**

Each row uses:

```ts
type Classification = {
  id: string
  disposition: 'equivalent' | 'redundant' | 'invalidForSeyric' | 'uncoveredByIdeal'
  obligations: readonly string[]
  visibleSituation: string
  defeats: string
  experientialNeighbors: readonly string[]
  reason: string
}
```

No row may cite an incumbent role, ID stability, current prerequisite, catalog prose, prior effort, or inventory size as a reason.

- [ ] **Step 3: Run two independent adversarial reviews**

Dispatch one logical-domain reviewer and one experiential-redundancy reviewer. Neither reviewer receives the proposed dispositions before independently inspecting the frozen obligations and current starts. Record concrete disagreements and their resolutions in `classification.md`; resolve by evidence, not vote count.

- [ ] **Step 4: Validate classification completeness**

Run a scratch check asserting:

```ts
assert.deepEqual(
  new Set(classification.map((row) => row.id)),
  new Set(inventory.map((row) => row.id)),
)
for (const row of classification) {
  assert.ok(row.reason.length > 0)
  if (row.disposition === 'equivalent') assert.ok(row.obligations.length > 0)
}
```

Expected: exit 0 with every current ID classified once.

---

### Task 3: Define the accepted collection and missing authoring briefs

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/accepted-inventory.json`
- Create in scratch: `/tmp/seyric-reconstruction/authoring-briefs.json`
- Create in scratch: `/tmp/seyric-reconstruction/coverage-matrix.md`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces: the exact accepted existing IDs, the exact obligations they cover, missing-obligation briefs with new semantic IDs but no artificial role suffixes, and a provisional partial order based only on readability, actual core dependencies, and artifact availability.

- [ ] **Step 1: Consolidate equivalent exposure**

For every obligation, choose the clearest existing equivalent start when one exists. A record may cover several obligations. Do not choose one record per obligation automatically.

- [ ] **Step 2: Write missing authoring briefs**

Each missing brief contains:

```json
{
  "id": "product-to-sum-handoff",
  "obligations": ["mixed-product-to-sum"],
  "requiredVisibleSituation": "A selected conjunct is also the useful disjunctive branch.",
  "stoppingRule": "One grouped handoff; no larger arity variant.",
  "mustDifferFrom": ["projection-compound-source-id", "injection-compound-source-id"],
  "artifactDependencies": [],
  "guidanceNeed": "optional"
}
```

IDs describe the semantic problem, never `practice`, `retrieval`, `challenge`, `remediation`, `transfer`, a batch number, or a desired position.

- [ ] **Step 3: Establish optional non-gating status**

Mark a record optional only when it adds worthwhile extra exposure but no unique core obligation. Assert that no accepted record or culture gateway depends on an optional ID. Do not make optionality synonymous with difficulty.

- [ ] **Step 4: Review coverage and ordering**

The lead reviews `coverage-matrix.md` for every approved obligation, every accepted ID, every missing brief, and every optional edge. Any uncovered obligation must have an authoring brief or a fixed-semantics rejection from the design spec.

---

### Task 4: Author missing primitive and structural bundles in parallel

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/author-primitive/<puzzle-id>/bundle.json`
- Create in scratch: `/tmp/seyric-reconstruction/author-primitive/<puzzle-id>/probe.ts`
- Create in scratch: `/tmp/seyric-reconstruction/author-structural/<puzzle-id>/bundle.json`
- Create in scratch: `/tmp/seyric-reconstruction/author-structural/<puzzle-id>/probe.ts`

**Interfaces:**
- Consumes: Task 3 briefs whose obligation families are hosted, primitive, structural, or primitive/structural mixed.
- Produces: complete candidate bundles containing `core`, `placement`, `artifact`, `coverage`, optional `guidance`, `validation`, and `reviewNote`.

- [ ] **Step 1: Dispatch disjoint author batches**

Authors receive only their briefs, fixed proof semantics, nearby accepted starts, and the bundle contract. They write only under their assigned scratch directory.

- [ ] **Step 2: Require complete bundles**

Each bundle uses:

```ts
type CandidateBundle = {
  core: { id: string; diagram: unknown }
  placement: { puzzle: string; prerequisites: string[]; optional: boolean }
  artifact: { puzzle: string; name: object; provenance: object }
  coverage: {
    puzzle: string
    obligations: string[]
    visibleSituation: string
    defeats: string
    experientialNeighbors: string[]
  }
  guidance: { puzzle: string; interventions: unknown[] }
  validation: {
    puzzle: string
    solution: unknown[]
    availableArtifacts: string[]
    expectedRules: string[]
    recognizedStates: unknown[]
  }
  reviewNote: { alternativeSolutionsWelcome: true; stoppingRule: string }
}
```

- [ ] **Step 3: Replay every candidate**

Run each candidate `probe.ts` with `npx tsx`.

Expected: JSON round-trip succeeds and the stored backward witness reaches canonical blank. A failed candidate returns to its author; no partial bundle proceeds.

---

### Task 5: Author missing constructive and classical bundles in parallel

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/author-constructive/<puzzle-id>/bundle.json`
- Create in scratch: `/tmp/seyric-reconstruction/author-constructive/<puzzle-id>/probe.ts`
- Create in scratch: `/tmp/seyric-reconstruction/author-classical/<puzzle-id>/bundle.json`
- Create in scratch: `/tmp/seyric-reconstruction/author-classical/<puzzle-id>/probe.ts`

**Interfaces:**
- Consumes: Task 3 constructive, classical, and mixed briefs.
- Produces: the same complete bundle contract as Task 4.

- [ ] **Step 1: Dispatch constructive and classical authors independently**

Constructive briefs include composition, lifting, mapping, case, distribution/factoring, absorption, and their approved interactions. Classical briefs include contraposition, excluded middle, De Morgan, reductio, Peirce isolation, consensus, and approved cross-topic interactions.

- [ ] **Step 2: Enforce bounded generalization**

Every candidate beyond a base case must quote the brief's false hypothesis and stopping rule in `reviewNote`. Reject fourth-variable excluded middle, post-saturation branch/chain growth, and automatic dual multiplication.

- [ ] **Step 3: Replay every candidate**

Run every sibling `probe.ts` with `npx tsx`.

Expected: each exits 0 at canonical blank with no change to proof physics.

---

### Task 6: Author missing artifact bundles and adversarially audit all candidates

**Files:**
- Create in scratch: `/tmp/seyric-reconstruction/author-artifact/<puzzle-id>/bundle.json`
- Create in scratch: `/tmp/seyric-reconstruction/author-artifact/<puzzle-id>/probe.ts`
- Create in scratch: `/tmp/seyric-reconstruction/reviews/logical.json`
- Create in scratch: `/tmp/seyric-reconstruction/reviews/experiential.json`
- Create in scratch: `/tmp/seyric-reconstruction/final-inventory.json`

**Interfaces:**
- Consumes: Tasks 3–5 and actual artifact theorem semantics.
- Produces: complete artifact candidates, two independent reviews of every accepted existing or new start, and the exact final inventory used by production integration.

- [ ] **Step 1: Author artifact candidates**

Use only ordinary verified theorem behavior: backward manifestation in a legal negative host, backward dissolution of an exact occurrence in a legal positive host, and ordinary ancestry after content is manifested. Do not encode artifact provenance as proof state.

- [ ] **Step 2: Run artifact probes**

Each probe constructs the completed-artifact authority from actual prerequisite IDs and validates the stored witness through `applyGameStep`.

Expected: every probe exits 0; missing, inexact, or wrong-polarity artifact use remains refused.

- [ ] **Step 3: Run independent logical and experiential audits**

Logical review checks closedness, propositional purity, theorem validity, witness replay, and artifact availability. Experiential review checks visible obligation, nearest neighbors, saturation, open-endedness, and optional non-gating status. Reviewers list defects by ID; they do not approve by count.

- [ ] **Step 4: Produce the final inventory**

The lead resolves defects, reruns affected probes, and writes `final-inventory.json` containing exact culture order, placements, optional flags, puzzle file sources, artifact records, coverage rows, guidance rows, and validation sidecars. No production file changes before this inventory is complete.

---

### Task 7: Replace curriculum runtime ownership with progression v2

**Files:**
- Create: `content/schemas/progression.schema.json`
- Create: `content/schemas/coverage.schema.json`
- Create: `content/progression/core.json`
- Create: `content/coverage/seyric.json`
- Modify: `content/schemas/manifest.schema.json`
- Modify: `content/schemas/guidance.schema.json`
- Modify: `content/manifest.json`
- Modify: `src/game/types.ts`
- Modify: `src/game/content-loader.ts`
- Modify: `src/game/content/files.ts`
- Modify: `tests/game/layered-content.test.ts`
- Modify: `tests/game/catalog-fixture.ts`
- Delete: `content/schemas/curriculum.schema.json`
- Delete: `content/curriculum/core.json`

**Interfaces:**
- Consumes: Task 6 `final-inventory.json`.
- Produces: manifest format version 2; runtime `PuzzlePlacement` with `{ puzzle, culture, prerequisites, optional }`; runtime `ProgressionCultureDefinition`; no `PerformanceId`, `PerformanceDefinition`, `CurriculumLearning`, `CurriculumPlacement`, or performance accessor.

- [ ] **Step 1: Write failing v2 loader tests**

Update the portable fixture to use:

```ts
'manifest.json': {
  format: 'cursebreaker-content', version: 2,
  puzzles: ['puzzles/two-veils.json'], definitions: [],
  progression: 'progression/core.json', coverage: 'coverage/seyric.json',
  catalog: 'catalog/cursebreaker.json', guidance: 'guidance/cursebreaker.json',
},
'progression/core.json': {
  cultures: [{
    id: 'seyric-horizon', order: 0, unlocksAfter: [], gateway: 'two-veils',
    puzzles: ['two-veils'],
  }],
  placements: [{ puzzle: 'two-veils', prerequisites: [], optional: false }],
},
```

Assert that v1 `curriculum`, performance objects, learning-role arrays, and guidance `performance` fields are rejected.

- [ ] **Step 2: Run the loader test and verify failure**

Run: `npx vitest run tests/game/layered-content.test.ts`

Expected: FAIL because the loader still requires manifest v1 curriculum data.

- [ ] **Step 3: Implement the v2 types and decoder**

Replace curriculum types with:

```ts
export type PuzzlePlacement = {
  readonly puzzle: PuzzleId
  readonly culture: CultureId
  readonly prerequisites: readonly PuzzleId[]
  readonly optional: boolean
}

export type ProgressionCultureDefinition = {
  readonly id: CultureId
  readonly order: number
  readonly unlocksAfter: readonly PuzzleId[]
  readonly gateway: PuzzleId
  readonly puzzles: readonly PuzzleId[]
}
```

Change `PortableGameCatalog.placement` to return `PuzzlePlacement`; remove the performance accessor and all performance graph validation. Parse `progression` and permit the manifest's `coverage` path without importing its build-only contents. Parse guidance without a performance field.

- [ ] **Step 4: Generate production progression and coverage from the final inventory**

Write the exact Task 6 data into `content/progression/core.json` and `content/coverage/seyric.json`. Do not mechanically preserve discarded rows.

- [ ] **Step 5: Run focused loader tests**

Run:

```bash
npx vitest run tests/game/layered-content.test.ts tests/game/catalog.test.ts tests/game/progress.test.ts tests/game/teaching.test.ts
```

Expected: all pass with no runtime performance or curriculum API.

- [ ] **Step 6: Commit the ownership replacement**

Commit only Task 7 files with message: `refactor: replace curriculum content ownership`.

---

### Task 8: Integrate the reconstructed puzzle collection

**Files:**
- Modify/Create/Delete according to Task 6 exact inventory: `content/puzzles/*.json`
- Modify/Create/Delete according to Task 6 exact inventory: `content/validation/*.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/guidance/cursebreaker.json`
- Modify: `content/manifest.json`
- Modify: `src/game/content/files.ts`
- Modify: `tests/game/opening-content.test.ts`
- Modify: `tests/game/content-validation.test.ts`

**Interfaces:**
- Consumes: Task 6 complete reviewed bundles and Task 7 v2 loader.
- Produces: one production record for every final ID and no production reference to any discarded ID.

- [ ] **Step 1: Write failing final-inventory tests**

Add assertions that the production ID set equals Task 6's accepted IDs, every placement optional flag obeys non-gating rules, every Seyric start is propositional, and canonical fingerprints are unique. Do not assert a numeric total.

- [ ] **Step 2: Run tests and verify failure**

Run: `npx vitest run tests/game/opening-content.test.ts tests/game/content-validation.test.ts`

Expected: FAIL because production still contains discarded rows and lacks newly accepted bundles.

- [ ] **Step 3: Integrate complete bundles and remove discarded rows**

Copy accepted/new core and validation JSON exactly from reviewed bundles. Rebuild catalog, guidance, manifest puzzle paths, and static imports from `final-inventory.json`. Remove every discarded core, validation, catalog, guidance, placement, manifest, and import entry. Do not leave aliases or tombstones.

- [ ] **Step 4: Run focused content tests**

Run:

```bash
npx vitest run tests/game/opening-content.test.ts tests/game/content-validation.test.ts tests/game/layered-content.test.ts tests/game/catalog.test.ts tests/game/progress.test.ts tests/game/teaching.test.ts tests/game/artifact-theorem.test.ts tests/game/artifact-drop.test.ts
```

Expected: all pass; no test derives value from old roles or an exact total.

- [ ] **Step 5: Commit the reconstructed collection**

Commit Task 8 files with message: `feat: reconstruct Seyric puzzle collection`.

---

### Task 9: Rebuild build-time validation around obligations and non-gating practice

**Files:**
- Modify: `scripts/validate-game-content.ts`
- Modify: `tests/game/content-validation.test.ts`
- Modify: `tests/game/layered-content.test.ts`
- Modify: `package.json`

**Interfaces:**
- Consumes: progression v2, coverage schema/data, final runtime catalog, and validation sidecars.
- Produces: direct semantic validation of coverage completeness, canonical uniqueness, optional non-gating, artifact availability, witness replay, and recognized-state replay.

- [ ] **Step 1: Write failing coverage validation tests**

Add negative fixtures for:

```ts
expect(() => validateFixture({ missingCoverage: 'two-veils' })).toThrow(/no coverage row/)
expect(() => validateFixture({ duplicateFingerprint: true })).toThrow(/duplicate canonical start/)
expect(() => validateFixture({ optionalPrerequisite: true })).toThrow(/optional puzzle .* gates/)
expect(() => validateFixture({ unknownObligation: true })).toThrow(/unknown obligation/)
expect(() => validateFixture({ uncoveredObligation: true })).toThrow(/uncovered obligation/)
```

- [ ] **Step 2: Run tests and verify failure**

Run: `npx vitest run tests/game/content-validation.test.ts`

Expected: FAIL because the current validator does not parse coverage or optional flags.

- [ ] **Step 3: Implement direct validators**

Parse `content/coverage/seyric.json` with AJV. Verify one coverage row per Seyric puzzle, all obligations referenced and covered, all experiential neighbors exist, every coverage string is nonempty, every optional puzzle has no dependent and is not a gateway/unlock gate, and canonical start groups have size one. Keep witness and recognized-state replay unchanged.

- [ ] **Step 4: Run validation**

Run:

```bash
npm run content:validate
npx vitest run tests/game/content-validation.test.ts tests/game/layered-content.test.ts
```

Expected: exit 0; reported totals are observational only.

- [ ] **Step 5: Commit validation**

Commit Task 9 files with message: `test: validate principled Seyric coverage`.

---

### Task 10: Delete displaced authorities and update documentation

**Files:**
- Delete: `docs/superpowers/specs/2026-07-18-seyric-content-production-design.md`
- Delete: `docs/superpowers/plans/2026-07-18-seyric-parallel-content-batch.md`
- Delete: `docs/superpowers/receipts/2026-07-18-seyric-inventory-normalization.md`
- Modify: `docs/game-content-format.md`
- Modify: `docs/superpowers/specs/2026-07-19-seyric-first-principles-content-design.md` only if implementation details require factual correction
- Modify/Delete: tests and docs containing stale discarded IDs or curriculum-role authority

**Interfaces:**
- Consumes: Tasks 7–9.
- Produces: one durable first-principles design, one current implementation plan, and content-format documentation matching manifest v2.

- [ ] **Step 1: Delete obsolete authorities**

Remove the three named documents entirely. Do not preserve summaries, migration notes, compatibility tables, or historical count receipts.

- [ ] **Step 2: Rewrite the content-format documentation**

Document puzzles, progression, build-only coverage, catalog, guidance, validation, manifest v2, puzzle fingerprints, optional non-gating, and the authoring bundle. State explicitly that coverage metadata cannot generate or gate records.

- [ ] **Step 3: Run displaced-model searches**

Run:

```bash
rg -n "Total emitted puzzles|Emitted snapshot|normalized inventory|inventory-preservation|introduces|practices|retrieves|assesses|masteryEvidence|PerformanceId|CurriculumPlacement" content src/game tests/game scripts docs --glob '!docs/superpowers/plans/2026-07-19-seyric-first-principles-content-reconstruction.md'
```

Expected: no active curriculum-role or quota authority. Any unrelated prose match must be inspected and documented rather than suppressed.

- [ ] **Step 4: Commit documentation cleanup**

Commit Task 10 files with message: `docs: remove obsolete Seyric inventory authority`.

---

### Task 11: Run final authoritative validation and record conformance

**Files:**
- Create: `docs/superpowers/receipts/2026-07-19-seyric-first-principles-content-reconstruction.md`
- Append: `/tmp/cursebreaker-seyric-cross-topic.6ZBmHQ/foundation-v2.md`

**Interfaces:**
- Consumes: all previous tasks.
- Produces: authoritative validation evidence and the required foundation `<conformance>` record.

- [ ] **Step 1: Run the focused unit and content suite**

Run:

```bash
npx vitest run tests/game/layered-content.test.ts tests/game/content-validation.test.ts tests/game/opening-content.test.ts tests/game/catalog.test.ts tests/game/progress.test.ts tests/game/teaching.test.ts tests/game/artifact-theorem.test.ts tests/game/artifact-drop.test.ts tests/game/controller.test.ts tests/game/save.test.ts
npm run content:validate
npm run typecheck
npm run build:renderer
```

Expected: every command exits 0. Do not run the dedicated physics battery.

- [ ] **Step 2: Run direct absence and integrity checks**

Run:

```bash
rg -n "Total emitted puzzles|Emitted snapshot|normalized inventory|inventory-preservation|PerformanceId|CurriculumPlacement|masteryEvidence" content src/game tests/game scripts docs
git diff --check
git status --short
```

Expected: no displaced authority; diff check exits 0; status contains only intended reconstruction files plus preserved unrelated changes.

- [ ] **Step 3: Write the final receipt**

Record every obligation and its covering puzzle or fixed-semantics rejection, every discarded ID and absence proof, every new puzzle and witness/review evidence, observed final/optional totals, exact commands, and exact pass results. Do not call an observed total a target or baseline.

- [ ] **Step 4: Append foundation conformance**

Append `<conformance>` to the existing foundation record without altering prior sections. Name implemented owners, deleted structures, migrated dependents, validation, and evidence that the old model is absent.

- [ ] **Step 5: Request final independent code/content review**

Use `superpowers:requesting-code-review` for the complete diff. Repair every in-scope defect and rerun the affected checks before reporting completion.
