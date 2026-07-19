# Seyric Inventory Normalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the inconsistent temporary atlas with one exact content-owned baseline inventory containing 49 skills and 186 uniquely identified Seyric puzzles.

**Architecture:** Three independent stage audits normalize structural, connective, and classical/reference rows into disjoint scratch fragments. The coordinator assembles those fragments into one strict JSON roadmap, derives requiredness from the final-transfer prerequisite closure, and adds direct tests that prove every approved count and evidence relationship.

**Tech Stack:** Strict JSON, TypeScript, Vitest, existing Cursebreaker content IDs and prerequisite conventions.

## Global Constraints

- This plan creates inventory content and direct inventory validation only.
- Preserve all 49 approved skill rows and all six existing Seyric puzzle IDs.
- The baseline contains exactly 186 unique puzzles: 64 structural, 51 connective, and 71 classical/reference.
- The baseline final-transfer prerequisite closure contains exactly 140 puzzles; its complement contains exactly 46.
- Warranted puzzles beyond the baseline are allowed later, but this plan first recovers the approved baseline exactly.
- A shared puzzle ID is counted once. Internal labels such as `contrast inside I-*` are not puzzle IDs.
- No production puzzle diagrams, solutions, catalog copy, guidance, or adjacent-system files change in this plan.
- The temporary source atlas is `/tmp/cursebreaker-seyric-graph-review-20260718/index.html`.
- The controlling normalization evidence is `/tmp/cursebreaker-seyric-graph-puzzle-granularity-foundation-20260718-01.md`.

---

## Roadmap data contract

Create `content/roadmaps/seyric.json` with this exact shape:

```ts
type SeyricRoadmap = {
  readonly format: 'cursebreaker-seyric-roadmap'
  readonly version: 1
  readonly finalTransfer: string
  readonly stages: readonly [
    { readonly id: 'structural'; readonly order: 0; readonly baselinePuzzles: 64 },
    { readonly id: 'connective'; readonly order: 1; readonly baselinePuzzles: 51 },
    { readonly id: 'classical'; readonly order: 2; readonly baselinePuzzles: 71 },
  ]
  readonly skills: readonly SeyricSkill[]
  readonly puzzles: readonly SeyricRoadmapPuzzle[]
  readonly internalLabels: readonly InternalAtlasLabel[]
}

type SeyricStage = 'structural' | 'connective' | 'classical'
type SeyricEvidenceRole =
  | 'introduction'
  | 'contrast'
  | 'application'
  | 'retrieval'
  | 'mixed'
  | 'transfer'
  | 'remediation'
  | 'challenge'

type SeyricSkill = {
  readonly id: string
  readonly label: string
  readonly stage: SeyricStage
  readonly mode: 'move' | 'recognition'
  readonly prerequisites: readonly string[]
}

type SeyricRoadmapPuzzle = {
  readonly id: string
  readonly stage: SeyricStage
  readonly folioOrder: number
  readonly prerequisites: readonly string[]
  readonly evidence: readonly [{
    readonly skill: string
    readonly role: SeyricEvidenceRole
    readonly primary: true
  }, ...Array<{
    readonly skill: string
    readonly role: SeyricEvidenceRole
    readonly primary?: false
  }>]
  readonly sourceLabels: readonly string[]
}

type InternalAtlasLabel = {
  readonly label: string
  readonly puzzle: string
  readonly reason: string
}
```

Evidence is stored once on puzzle records. Per-skill evidence tables are derived during validation so the roadmap has no competing relationship list.

---

### Task 1: Write the direct roadmap contract test

**Files:**
- Create: `tests/game/seyric-roadmap.test.ts`
- Create: `content/roadmaps/seyric.json`

**Interfaces:**
- Consumes: the roadmap data contract above.
- Produces: direct executable assertions used by all stage-normalization tasks.

- [ ] **Step 1: Create an empty roadmap shell**

Create `content/roadmaps/seyric.json`:

```json
{
  "format": "cursebreaker-seyric-roadmap",
  "version": 1,
  "finalTransfer": "",
  "stages": [
    { "id": "structural", "order": 0, "baselinePuzzles": 64 },
    { "id": "connective", "order": 1, "baselinePuzzles": 51 },
    { "id": "classical", "order": 2, "baselinePuzzles": 71 }
  ],
  "skills": [],
  "puzzles": [],
  "internalLabels": []
}
```

- [ ] **Step 2: Write the failing contract test**

Create `tests/game/seyric-roadmap.test.ts` with this complete content:

```ts
import { describe, expect, it } from 'vitest'
import roadmapJson from '../../content/roadmaps/seyric.json'

type Stage = 'structural' | 'connective' | 'classical'
type Role =
  | 'introduction' | 'contrast' | 'application' | 'retrieval'
  | 'mixed' | 'transfer' | 'remediation' | 'challenge'
type Skill = {
  readonly id: string
  readonly label: string
  readonly stage: Stage
  readonly mode: 'move' | 'recognition'
  readonly prerequisites: readonly string[]
}
type Evidence = { readonly skill: string; readonly role: Role; readonly primary?: boolean }
type Puzzle = {
  readonly id: string
  readonly stage: Stage
  readonly folioOrder: number
  readonly prerequisites: readonly string[]
  readonly evidence: readonly [Evidence, ...Evidence[]]
  readonly sourceLabels: readonly string[]
}
type Roadmap = {
  readonly format: 'cursebreaker-seyric-roadmap'
  readonly version: 1
  readonly finalTransfer: string
  readonly stages: readonly { readonly id: Stage; readonly order: number; readonly baselinePuzzles: number }[]
  readonly skills: readonly Skill[]
  readonly puzzles: readonly Puzzle[]
  readonly internalLabels: readonly { readonly label: string; readonly puzzle: string; readonly reason: string }[]
}

const roadmap = roadmapJson as Roadmap
const unique = (values: readonly string[]): boolean => new Set(values).size === values.length
const countByStage = (puzzles: readonly Puzzle[]): Record<Stage, number> => {
  const counts: Record<Stage, number> = { structural: 0, connective: 0, classical: 0 }
  for (const puzzle of puzzles) counts[puzzle.stage] += 1
  return counts
}

const findCycle = (nodes: readonly { readonly id: string; readonly prerequisites: readonly string[] }[]): readonly string[] | null => {
  const prerequisites = new Map(nodes.map(({ id, prerequisites }) => [id, prerequisites] as const))
  const visited = new Set<string>()
  const visiting = new Set<string>()
  const path: string[] = []
  const visit = (id: string): readonly string[] | null => {
    if (visiting.has(id)) return [...path.slice(path.indexOf(id)), id]
    if (visited.has(id)) return null
    visiting.add(id)
    path.push(id)
    for (const parent of prerequisites.get(id) ?? []) {
      const cycle = visit(parent)
      if (cycle !== null) return cycle
    }
    path.pop()
    visiting.delete(id)
    visited.add(id)
    return null
  }
  for (const { id } of nodes) {
    const cycle = visit(id)
    if (cycle !== null) return cycle
  }
  return null
}

type SkillEvidence = { readonly puzzle: string; readonly role: Role }
const evidenceBySkill = (puzzles: readonly Puzzle[]): ReadonlyMap<string, readonly SkillEvidence[]> => {
  const out = new Map<string, SkillEvidence[]>()
  for (const puzzle of puzzles) {
    for (const evidence of puzzle.evidence) {
      const rows = out.get(evidence.skill) ?? []
      rows.push({ puzzle: puzzle.id, role: evidence.role })
      out.set(evidence.skill, rows)
    }
  }
  return out
}
const idsFor = (rows: readonly SkillEvidence[], role: Role): readonly string[] =>
  [...new Set(rows.filter((row) => row.role === role).map(({ puzzle }) => puzzle))]

const prerequisiteClosure = (target: string, puzzles: readonly Puzzle[]): ReadonlySet<string> => {
  const byId = new Map(puzzles.map((puzzle) => [puzzle.id, puzzle] as const))
  const closure = new Set<string>()
  const add = (id: string): void => {
    if (closure.has(id)) return
    const puzzle = byId.get(id)
    if (puzzle === undefined) throw new Error(`unknown puzzle '${id}'`)
    closure.add(id)
    for (const parent of puzzle.prerequisites) add(parent)
  }
  add(target)
  return closure
}

describe('normalized Seyric roadmap', () => {
  it('owns the approved baseline counts and unique identities', () => {
    expect(roadmap.format).toBe('cursebreaker-seyric-roadmap')
    expect(roadmap.version).toBe(1)
    expect(roadmap.stages).toEqual([
      { id: 'structural', order: 0, baselinePuzzles: 64 },
      { id: 'connective', order: 1, baselinePuzzles: 51 },
      { id: 'classical', order: 2, baselinePuzzles: 71 },
    ])
    expect(roadmap.skills).toHaveLength(49)
    expect(roadmap.puzzles).toHaveLength(186)
    expect(unique(roadmap.skills.map(({ id }) => id))).toBe(true)
    expect(unique(roadmap.puzzles.map(({ id }) => id))).toBe(true)
    expect(countByStage(roadmap.puzzles)).toEqual({
      structural: 64, connective: 51, classical: 71,
    })
  })

  it('gives every puzzle one primary evidence role and a stable folio position', () => {
    expect(roadmap.puzzles.map(({ folioOrder }) => folioOrder).sort((a, b) => a - b))
      .toEqual(Array.from({ length: 186 }, (_, index) => index))
    for (const puzzle of roadmap.puzzles) {
      expect(puzzle.evidence.filter(({ primary }) => primary)).toHaveLength(1)
      expect(puzzle.evidence[0]?.primary).toBe(true)
      expect(puzzle.sourceLabels.length).toBeGreaterThan(0)
    }
  })

  it('contains only resolved skill and puzzle references and has no cycles', () => {
    const skills = new Set(roadmap.skills.map(({ id }) => id))
    const puzzles = new Set(roadmap.puzzles.map(({ id }) => id))
    for (const skill of roadmap.skills) {
      expect(skill.prerequisites.every((id) => skills.has(id))).toBe(true)
    }
    expect(skills.has('distinguish-nested-owners')).toBe(true)
    expect(puzzles.has('two-mark-projection')).toBe(true)
    for (const puzzle of roadmap.puzzles) {
      expect(puzzle.prerequisites.every((id) => puzzles.has(id))).toBe(true)
      expect(puzzle.evidence.every(({ skill }) => skills.has(skill))).toBe(true)
    }
    expect(findCycle(roadmap.skills.map(({ id, prerequisites }) => ({ id, prerequisites }))))
      .toBeNull()
    expect(findCycle(roadmap.puzzles.map(({ id, prerequisites }) => ({ id, prerequisites }))))
      .toBeNull()
  })

  it('supplies complete mastery evidence for every skill', () => {
    const evidence = evidenceBySkill(roadmap.puzzles)
    for (const skill of roadmap.skills) {
      const rows = evidence.get(skill.id) ?? []
      expect(idsFor(rows, 'introduction').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'contrast').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'application').length).toBeGreaterThanOrEqual(2)
      expect(idsFor(rows, 'retrieval').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'mixed').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'transfer').length).toBeGreaterThanOrEqual(1)
    }
  })

  it('derives the approved required and optional baseline from final transfer', () => {
    const required = prerequisiteClosure(roadmap.finalTransfer, roadmap.puzzles)
    expect(required.size).toBe(140)
    expect(roadmap.puzzles.length - required.size).toBe(46)
    expect(required.has(roadmap.finalTransfer)).toBe(true)
  })

  it('classifies every non-puzzle atlas label against a real puzzle', () => {
    const puzzles = new Set(roadmap.puzzles.map(({ id }) => id))
    for (const item of roadmap.internalLabels) {
      expect(item.label.trim()).not.toBe('')
      expect(item.reason.trim()).not.toBe('')
      expect(puzzles.has(item.puzzle)).toBe(true)
      expect(puzzles.has(item.label)).toBe(false)
    }
  })
})
```

- [ ] **Step 3: Run the test and verify the shell fails for missing content**

Run:

```bash
npx vitest run tests/game/seyric-roadmap.test.ts
```

Expected: FAIL on the first count assertion with `expected [] to have a length of 49`.

Do not commit the empty shell.

---

### Task 2: Normalize the opening and structural stage

**Files:**
- Read: `/tmp/cursebreaker-seyric-graph-review-20260718/index.html`
- Read: `/tmp/cursebreaker-seyric-graph-puzzle-granularity-foundation-20260718-01.md`
- Scratch output: a JSON fragment containing 23 skills and 64 unique puzzles.

**Interfaces:**
- Consumes: the roadmap data contract and structural skill rows in the atlas.
- Produces: `skills`, `puzzles`, and `internalLabels` arrays for stage `structural`.

- [ ] **Step 1: Extract the 23 structural skill rows**

Record each atlas `skill('structural', ...)` call as one `SeyricSkill`. Preserve its stable skill ID, visible label, `move`/`recognition` mode, and prerequisite skill IDs. Replace prose prerequisite phrases with the exact skill IDs they name; do not create family-heading skills.

- [ ] **Step 2: Normalize structural evidence labels**

For every structural row, classify each label in introduction, contrast, variants, retrieval, transfer, and optional cells as one of:

- a unique puzzle ID;
- a reference to a shared puzzle already counted once;
- an internal decision belonging to another named puzzle.

Give every unique puzzle one primary evidence entry. Add secondary evidence entries where a shared puzzle is load-bearing for another skill. Preserve these opening IDs exactly:

```text
two-veils
four-veils
forked-veil
echoed-veil
single-mark-return
two-mark-projection
```

The required nested-owner introduction must remain distinct from optional `two-mark-projection`.

- [ ] **Step 3: Assign structural prerequisites and folio order**

Assign acyclic puzzle prerequisites so introductions precede contrasts and applications, both applications precede delayed retrieval, and independent introductions precede shared mixed puzzles. Assign structural `folioOrder` values `0` through `63`.

- [ ] **Step 4: Verify the scratch fragment**

The fragment must contain exactly:

```text
skills: 23
puzzles: 64
unique puzzle IDs: 64
folio orders: 0..63
existing Seyric IDs preserved: 6/6
```

Return the fragment and a list of every raw label classified as internal rather than a puzzle.

---

### Task 3: Normalize the connective/compositional stage

**Files:**
- Read: `/tmp/cursebreaker-seyric-graph-review-20260718/index.html`
- Scratch output: a JSON fragment containing 13 skills and 51 unique puzzles.

**Interfaces:**
- Consumes: the roadmap data contract and the accepted structural skill IDs.
- Produces: `skills`, `puzzles`, and `internalLabels` arrays for stage `connective`.

- [ ] **Step 1: Extract the 13 connective skill rows**

Preserve separate skills for three-link composition, four-link composition, composition with side premises, conjunction lifting, disjunction mapping, binary cases, three-way cases, both distribution expansions, both factoring directions, and both absorption directions.

- [ ] **Step 2: Classify inline contrasts correctly**

Every label matching `contrast inside I-*` is an internal decision in the named introduction puzzle. Add it to `internalLabels`; do not count it as a puzzle. Shared `B*`, `R*`, and `T*` IDs are counted once and receive multiple evidence entries where appropriate.

- [ ] **Step 3: Assign connective prerequisites and folio order**

Use accepted structural skill and puzzle IDs for cross-stage prerequisites. Within the stage, ensure composition precedes lifting/cases, cases precede distribution, and distribution/idempotence evidence precedes absorption. Assign `folioOrder` values `64` through `114`.

- [ ] **Step 4: Verify the scratch fragment**

The fragment must contain exactly:

```text
skills: 13
puzzles: 51
unique puzzle IDs: 51
folio orders: 64..114
inline contrast labels counted as puzzles: 0
```

Return the fragment and the complete internal-label classification.

---

### Task 4: Normalize the polarity/classical/reference stage

**Files:**
- Read: `/tmp/cursebreaker-seyric-graph-review-20260718/index.html`
- Scratch output: a JSON fragment containing 13 skills and 71 unique puzzles.

**Interfaces:**
- Consumes: the roadmap data contract plus accepted structural and connective skill IDs.
- Produces: `skills`, `puzzles`, and `internalLabels` arrays for stage `classical`.

- [ ] **Step 1: Extract the 13 classical/reference skill rows**

Preserve separate skills for direct contraposition, four De Morgan directions, content-bearing double-negation elimination, excluded middle, reductio, Peirce-style feedback, exact artifact selection, manifestation, dissolution, and structural-variant transfer.

- [ ] **Step 2: Normalize shared retrieval and transfer IDs**

Count each shared `SEY-DM-R*`, `SEY-CL-R*`, `SEY-XFER-R*`, `SEY-XFER-V*`, and `SEY-XFER-T*` ID once. Record every additional skill/evidence role on that one puzzle record. Keep remediation and challenge IDs distinct unless the raw ID is exactly shared.

- [ ] **Step 3: Assign prerequisites, final transfer, and folio order**

Make classical introductions depend on their actual structural/connective prerequisites. Make exact artifact use depend on prior completed artifacts. Set `finalTransfer` to the one unfamiliar mixed transfer puzzle that receives final transfer evidence across the curriculum. Assign `folioOrder` values `115` through `185`.

- [ ] **Step 4: Verify the scratch fragment**

The fragment must contain exactly:

```text
skills: 13
puzzles: 71
unique puzzle IDs: 71
folio orders: 115..185
final transfer IDs: 1
```

Return the fragment and all shared-ID classifications.

---

### Task 5: Assemble and reconcile the canonical roadmap

**Files:**
- Modify: `content/roadmaps/seyric.json`
- Test: `tests/game/seyric-roadmap.test.ts`

**Interfaces:**
- Consumes: the three accepted stage fragments.
- Produces: the sole normalized baseline roadmap.

- [ ] **Step 1: Merge the disjoint stage fragments**

Replace the empty arrays in `content/roadmaps/seyric.json` with the three stage fragments ordered by stage and `folioOrder`. Set the accepted final-transfer ID. Merge and sort `internalLabels` by `label` then `puzzle`.

- [ ] **Step 2: Run the direct roadmap test**

Run:

```bash
npx vitest run tests/game/seyric-roadmap.test.ts
```

Expected: all six roadmap tests pass. If the closure is not 140/46, correct prerequisite edges based on the evidence-shared spiral; do not mark requiredness separately.

- [ ] **Step 3: Run existing content validation**

Run:

```bash
npm run content:validate
```

Expected: the existing seven production puzzles remain valid. The roadmap is authoring content and does not alter the current runtime catalog.

- [ ] **Step 4: Commit the normalized roadmap and its direct test**

```bash
git add content/roadmaps/seyric.json tests/game/seyric-roadmap.test.ts
git commit -m "content: normalize Seyric puzzle inventory"
```

---

### Task 6: Produce the normalization receipt

**Files:**
- Create: `docs/superpowers/receipts/2026-07-18-seyric-inventory-normalization.md`

**Interfaces:**
- Consumes: the passing roadmap and direct test output.
- Produces: the review evidence required before the feasibility-content plan.

- [ ] **Step 1: Record exact normalization results**

The receipt contains these emitted counts:

```text
skills: 49
structural skills/puzzles: 23/64
connective skills/puzzles: 13/51
classical skills/puzzles: 13/71
total baseline puzzles: 186
required final-transfer closure: 140
optional complement: 46
duplicate puzzle IDs: 0
unclassified source labels: 0
missing evidence categories: 0
graph cycles: 0
```

List every internal atlas label and the puzzle that owns it. List every shared puzzle ID with all skills and roles it supports. State the final-transfer ID.

- [ ] **Step 2: Self-audit against the approved design**

Confirm explicitly that:

- no family heading became a puzzle;
- all six existing Seyric IDs remain stable;
- nested-owner required evidence does not rely on optional `two-mark-projection`;
- each skill has introduction, contrast, two applications, retrieval, mixed, and transfer evidence;
- optional puzzles are outside the final-transfer closure;
- no production puzzle content was authored in this normalization plan.

- [ ] **Step 3: Commit the receipt**

```bash
git add docs/superpowers/receipts/2026-07-18-seyric-inventory-normalization.md
git commit -m "docs: record Seyric inventory normalization"
```

- [ ] **Step 4: Run the final focused verification**

Run:

```bash
npx vitest run tests/game/seyric-roadmap.test.ts tests/game/content-validation.test.ts tests/game/layered-content.test.ts
npm run content:validate
git diff --check
```

Expected: all focused tests and content validation pass, and `git diff --check` prints nothing.
