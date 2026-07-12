# Opening Cultures and Content Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace campaign grouping with culture authority and ship the approved seven-artifact opening catalog with verified backward witnesses, derived required/elective progression, and structured learning metadata.

**Architecture:** Reconstruct `src/game` around immutable culture, performance, artifact, and teacher-intervention records while retaining the existing kernel-backed session, vellum, and save authorities. Catalog validation owns combined culture/artifact reachability, witness replay, proof-state intervention reachability, learning metadata, exact rule-use claims, and fingerprints; progression derives culture unlocks and required artifacts from that verified graph. The shipped opening catalog is a separate `src/game/content` package that depends only on public game and kernel construction APIs. Invalid-action thoughts remain exclusively in interaction refusal and are not content metadata.

**Tech Stack:** TypeScript 5.5 strict mode, Vitest 2, existing immutable diagram kernel and canonical explorer.

## Global Constraints

- Replace `CampaignId`, `CampaignDefinition`, `campaignId`, `campaign`, and `campaigns`; do not preserve aliases or a parallel campaign model.
- The tutorial spans cultures through approximately the fixed-point theorem; this plan authors only the approved seven-artifact initial batch.
- Artifacts 1–5 form the initial required spine, artifact 6 is elective, and artifact 7 is the required gateway of culture 2.
- The first culture contains only pure-propositional and outer-universal proposition content; the existential proposition appears only in culture 2.
- Artifact display names use an approved professional name plus optional curator shorthand. Formula labels are validation metadata, never display titles.
- Exact culture names, artifact names, provenance, and final teacher copy require the named review gate before shipped content is written.
- Invalid actions produce interaction-owned pointer thoughts and never content-authored misconception feedback. Valid committed states may trigger separately authored teacher interventions.
- Every goal is closed and every witness replays backward to canonical blank through already player-authorable interactions.
- `src/game` imports neither `src/app`, `src/theories`, nor filesystem authority.
- No game-only proof interaction, visual styling, physics change, or placeholder future culture is introduced.
- Run focused game, kernel, architecture, and type checks only. Physics tests remain excluded because physics is untouched.

## File Structure

Production:

- Modify `src/game/types.ts` — culture, nomenclature, performance, teacher-intervention, and artifact source types.
- Modify `src/game/catalog.ts` — immutable snapshot, graph validation, metadata validation, witness and intervention-demonstration replay, lookup, and fingerprint.
- Create `src/game/teaching.ts` — pure matching of lifecycle, stalled, and canonical proof-state teacher interventions.
- Modify `src/game/progress.ts` — culture unlocks, artifact unlocks, and derived required/elective status.
- Modify `src/game/index.ts` — export the new content API.
- Create `src/game/content/opening.ts` — two cultures, performance graph, seven permanent artifacts, and diagram builders/witnesses.
- Create `src/game/content/index.ts` — `openingCatalogSource()` and `openingCatalog()`.

Tests and documentation:

- Create `tests/game/catalog-fixture.ts` — one complete minimal culture/performance/artifact source.
- Modify `tests/game/{catalog,progress,save,session,vellum}.test.ts`.
- Create `tests/game/opening-content.test.ts`.
- Create `tests/game/teaching.test.ts`.
- Modify `tests/architecture/game-boundary.test.ts`.
- Mark the completed domain-foundation plan as a historical record superseded by culture authority.

---

### Task 1: Replace Campaign Vocabulary with Culture Vocabulary

**Files:**
- Modify: `src/game/types.ts`
- Create: `tests/game/catalog-fixture.ts`
- Modify: `tests/game/catalog.test.ts`
- Modify: `tests/game/progress.test.ts`
- Modify: `tests/game/save.test.ts`
- Modify: `tests/game/session.test.ts`
- Modify: `tests/game/vellum.test.ts`
- Modify: `docs/superpowers/plans/2026-07-11-cursebreaker-game-domain-foundation.md`

**Interfaces:**
- Produces: `CultureId`, `cultureId(value: string): CultureId`, `CultureDefinition`, `PuzzleDefinition.culture`, and `GameCatalogSource.cultures`.
- Removes: every campaign type, constructor, property, collection, error message, fixture, and test expectation.

- [ ] **Step 1: Add a compile-failing culture fixture**

Create `tests/game/catalog-fixture.ts` with the intended minimal API:

```ts
import { cultureId, puzzleId, type GameCatalogSource, type PuzzleDefinition } from '../../src/game/types'
import { twoVeils } from './fixtures'

export const fixtureCultureId = cultureId('oldest-tradition')

export function minimalPuzzle(overrides: Partial<PuzzleDefinition> = {}): PuzzleDefinition {
  const fixture = twoVeils()
  return {
    id: puzzleId('two-veils'), culture: fixtureCultureId, title: 'Fixture artifact',
    goal: fixture.goal, prerequisites: [], grantsVellum: true,
    witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
    ...overrides,
  }
}

export function minimalSource(): GameCatalogSource {
  return {
    cultures: [{ id: fixtureCultureId, name: 'Fixture culture' }],
    puzzles: [minimalPuzzle()], context: { relations: new Map() },
  }
}
```

- [ ] **Step 2: Run typecheck to verify the culture API is missing**

Run: `npm run typecheck`

Expected: FAIL because `cultureId`, `culture`, and `cultures` do not exist.

- [ ] **Step 3: Replace the campaign types in `src/game/types.ts`**

```ts
export type PuzzleId = string & { readonly __puzzleId: unique symbol }
export type CultureId = string & { readonly __cultureId: unique symbol }

export const cultureId = (value: string): CultureId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid culture id '${value}'`)
  }
  return value as CultureId
}

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly culture: CultureId
  readonly title: string
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly grantsVellum: boolean
  readonly witness: readonly GameStep[]
}

export type CultureDefinition = { readonly id: CultureId; readonly name: string }
export type GameCatalogSource = {
  readonly cultures: readonly CultureDefinition[]
  readonly puzzles: readonly PuzzleDefinition[]
  readonly context: GameRuleContext
}
```

Delete every campaign type and export. Do not retain deprecated aliases.

- [ ] **Step 4: Migrate catalog validation and every domain fixture**

In `src/game/catalog.ts`, rename collection and field access to `cultures` and
`puzzle.culture`, and change diagnostics to “culture”. In every listed game
test, import `cultureId`, use `culture`, and build `{ cultures, puzzles,
context }`. Use `minimalPuzzle` and `minimalSource` where custom topology is not
part of the test.

Add this header to the completed foundation plan:

```md
> **Historical implementation record:** The title-only campaign vocabulary in
> this completed plan was replaced by culture authority in
> `2026-07-11-opening-cultures-content-design.md`. It is not a current API or
> product model.
```

- [ ] **Step 5: Prove the displaced vocabulary is absent**

Run:

```bash
! rg -n "CampaignId|CampaignDefinition|campaignId|campaigns|\.campaign\b" src/game tests/game
npx vitest run tests/game
npm run typecheck
```

Expected: grep has no output; game tests pass; typecheck exits 0.

- [ ] **Step 6: Commit the migration**

```bash
git add src/game tests/game docs/superpowers/plans/2026-07-11-cursebreaker-game-domain-foundation.md
git commit -m "refactor(game): replace campaigns with cultures"
```

---

### Task 2: Make Culture Gates and Requiredness Graph-Derived

**Files:**
- Modify: `src/game/types.ts`
- Modify: `src/game/catalog.ts`
- Modify: `src/game/progress.ts`
- Modify: `tests/game/catalog-fixture.ts`
- Modify: `tests/game/catalog.test.ts`
- Modify: `tests/game/progress.test.ts`

**Interfaces:**
- Produces: `CultureDefinition.unlocksAfter`, `CultureDefinition.gateway`, `GameCatalog.culture`, `isCultureUnlocked`, `requiredPuzzles`, and `isRequired`.
- Consumes: immutable catalog snapshots and the artifact prerequisite DAG.

- [ ] **Step 1: Write failing culture-gate and elective-status tests**

Construct two cultures and seven fixture puzzle identities. Assert:

```ts
expect(isCultureUnlocked(catalog, emptyProgress(), secondCulture.id)).toBe(false)
const afterGate = recordCompletion(emptyProgress(), fifth.id)
expect(isCultureUnlocked(catalog, afterGate, secondCulture.id)).toBe(true)
expect(isUnlocked(catalog, afterGate, seventh.id)).toBe(true)
expect(isRequired(catalog, sixth.id)).toBe(false)
for (const puzzle of [first, second, third, fourth, fifth, seventh]) {
  expect(isRequired(catalog, puzzle.id)).toBe(true)
}
```

Add catalog refusals for a missing gateway, a gateway belonging to another
culture, a missing unlock artifact, and a culture depending on an artifact in
itself.

- [ ] **Step 2: Run focused tests and verify missing APIs**

Run: `npx vitest run tests/game/catalog.test.ts tests/game/progress.test.ts`

Expected: FAIL because culture gates and requiredness do not exist.

- [ ] **Step 3: Extend culture and catalog interfaces**

```ts
export type CultureDefinition = {
  readonly id: CultureId
  readonly name: string
  readonly unlocksAfter: readonly PuzzleId[]
  readonly gateway: PuzzleId
}

export type GameCatalog = {
  readonly source: GameCatalogSource
  readonly fingerprint: string
  puzzle(id: PuzzleId): PuzzleDefinition
  culture(id: CultureId): CultureDefinition
}
```

In `buildCatalog`, verify gateways and unlock identities exist; a gateway
belongs to its culture; unlock lists contain no duplicates; puzzle prerequisites
remain acyclic; and culture dependency edges—from an unlock artifact's culture
to the unlocked culture—are acyclic and contain no self-edge.

- [ ] **Step 4: Implement progression derivation**

```ts
export function isCultureUnlocked(catalog: GameCatalog, progress: GameProgress, id: CultureId): boolean {
  return catalog.culture(id).unlocksAfter.every((puzzle) => progress.completed.has(puzzle))
}

export function isUnlocked(catalog: GameCatalog, progress: GameProgress, id: PuzzleId): boolean {
  const puzzle = catalog.puzzle(id)
  return isCultureUnlocked(catalog, progress, puzzle.culture)
    && puzzle.prerequisites.every((parent) => progress.completed.has(parent))
}

export function requiredPuzzles(catalog: GameCatalog): ReadonlySet<PuzzleId> {
  const required = new Set<PuzzleId>()
  const add = (id: PuzzleId): void => {
    if (required.has(id)) return
    required.add(id)
    for (const parent of catalog.puzzle(id).prerequisites) add(parent)
  }
  for (const culture of catalog.source.cultures) {
    add(culture.gateway)
    for (const gate of culture.unlocksAfter) add(gate)
  }
  return required
}

export const isRequired = (catalog: GameCatalog, id: PuzzleId): boolean =>
  requiredPuzzles(catalog).has(id)
```

- [ ] **Step 5: Run focused and save tests**

Run:

```bash
npx vitest run tests/game/catalog.test.ts tests/game/progress.test.ts tests/game/save.test.ts
npm run typecheck
```

Expected: selected tests pass and typecheck exits 0.

- [ ] **Step 6: Commit culture progression**

```bash
git add src/game/types.ts src/game/catalog.ts src/game/progress.ts tests/game
git commit -m "feat(game): derive culture progression"
```

---

### Task 3: Add Nomenclature and Learning Authorities

**Files:**
- Modify: `src/game/types.ts`
- Modify: `src/game/catalog.ts`
- Modify: `tests/game/catalog-fixture.ts`
- Modify: `tests/game/catalog.test.ts`

**Interfaces:**
- Produces: performance, knowledge-point, artifact-name, provenance, and puzzle-learning records.
- Catalog validation owns string completeness, knowledge-point bounds, performance DAG, referenced-performance existence, role uniqueness, exact rule-use equality, and fingerprint inclusion.

- [ ] **Step 1: Write failing metadata-validation tests**

Add cases rejecting blank professional names; missing provenance summaries;
empty sealing vocabulary; performance nodes outside the two-to-five
knowledge-point bound; missing performance prerequisites; performance cycles;
unknown puzzle performance references; duplicate learning-role entries; and
`rulesUsed` that omits or invents a witness rule. Assert fingerprint changes
when professional naming, performance content, or cultural history changes.

- [ ] **Step 2: Run catalog tests and verify missing metadata**

Run: `npx vitest run tests/game/catalog.test.ts`

Expected: FAIL because the new types and validators do not exist.

- [ ] **Step 3: Define the structured metadata**

```ts
export type PerformanceId = string & { readonly __performanceId: unique symbol }
export const performanceId = (value: string): PerformanceId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid performance id '${value}'`)
  }
  return value as PerformanceId
}

export type KnowledgePoint = {
  readonly id: string
  readonly instruction: string
  readonly commonError: string
  readonly correction: string
}
export type PerformanceDefinition = {
  readonly id: PerformanceId
  readonly description: string
  readonly prerequisites: readonly PerformanceId[]
  readonly knowledgePoints: readonly KnowledgePoint[]
  readonly masteryEvidence: string
  readonly remediation: readonly PerformanceId[]
}
export type ArtifactName = {
  readonly professional: string
  readonly curatorShorthand?: string
  readonly accession?: string
}
export type ArtifactProvenance = {
  readonly summary: string
  readonly function: string
  readonly findspot?: string
  readonly attributedTo?: string
}
export type PuzzleLearning = {
  readonly introduces: readonly PerformanceId[]
  readonly practices: readonly PerformanceId[]
  readonly retrieves: readonly PerformanceId[]
  readonly assesses: readonly PerformanceId[]
  readonly rulesUsed: readonly GameStep['rule'][]
}
```

Extend `CultureDefinition` with these exact fields:

```ts
readonly relativeAge: number
readonly historicalSummary: string
readonly lineage: readonly CultureId[]
readonly isolation: 'connected' | 'isolated' | 'uncertain'
readonly sealingVocabulary: readonly string[]
```

Replace `PuzzleDefinition.title` with `name: ArtifactName`, then add `provenance`,
and `learning`. Add `performances: readonly PerformanceDefinition[]` to
`GameCatalogSource`. Task 4 adds the separately owned teacher-intervention
authority after its trigger semantics and reachability evidence are available.

- [ ] **Step 4: Validate and fingerprint the metadata**

Require trimmed nonempty strings; distinct nonnegative `relativeAge` values;
two-to-five knowledge points per performance; unique knowledge-point IDs;
acyclic performance prerequisites; present performance references; unique
entries within every learning role; and exact set equality between `rulesUsed`
and `new Set(witness.map(step => step.rule))`.
Require culture lineage identities to exist and reject lineage cycles.
Include every field in deterministic fingerprint input, sorting identity sets
while preserving knowledge-point order.

- [ ] **Step 5: Run catalog and full game tests**

Run:

```bash
npx vitest run tests/game
npm run typecheck
```

Expected: game tests pass and typecheck exits 0.

- [ ] **Step 6: Commit metadata authority**

```bash
git add src/game/types.ts src/game/catalog.ts tests/game
git commit -m "feat(game): validate cultural learning metadata"
```

---

### Task 4: Separate Interaction Thoughts from Teacher Interventions

**Files:**
- Modify: `src/game/types.ts`
- Modify: `src/game/catalog.ts`
- Create: `src/game/teaching.ts`
- Modify: `src/game/index.ts`
- Modify: `tests/game/catalog-fixture.ts`
- Modify: `tests/game/catalog.test.ts`
- Create: `tests/game/teaching.test.ts`

**Interfaces:**
- Replaces: `MisconceptionCue`, `PuzzleDefinition.misconceptions`, and
  content-authored `thought` fields.
- Produces: `TeacherTrigger`, `TeacherIntervention`, `TeacherSignal`, and
  `teacherInterventionsFor(puzzle, signal, seen)`.
- Consumes: canonical diagram exploration, the existing kernel-backed game
  session, and the same prerequisite-scoped authority used to verify witnesses.

- [ ] **Step 1: Write failing catalog tests for the replacement model**

In `tests/game/catalog.test.ts`, remove the test that requires a misconception
thought. Add a four-veil fixture whose first legal elimination reaches the
canonical two-veil state:

```ts
const four = fourVeils()
const reachedTwoVeils: TeacherIntervention = {
  id: 'inner-pair-removed',
  performance: fixturePerformanceId,
  trigger: {
    kind: 'proofState',
    state: twoVeils().goal,
    demonstration: [{ rule: 'doubleCutElim', region: four.eliminations[0]! }],
  },
  text: 'That route leaves the older paired form.',
  repeat: 'once',
  recovery: 'timeline',
}
const fourPuzzle = minimalPuzzle({
  goal: four.goal,
  witness: [
    { rule: 'doubleCutElim', region: four.eliminations[0]! },
    { rule: 'doubleCutElim', region: four.eliminations[1]! },
  ],
  teacher: [reachedTwoVeils],
})
expect(() => buildCatalog({ ...minimalSource(), puzzles: [fourPuzzle] })).not.toThrow()
```

Add refusals for duplicate intervention IDs, blank `id` or `text`, an unknown
optional performance, a stalled level outside `1..3`, an empty proof-state
demonstration, an open trigger state, a demonstration containing an invalid
step, and a legal demonstration whose result does not canonically equal its
declared state. Assert that removing or changing the proof-state intervention
changes the catalog fingerprint.

- [ ] **Step 2: Run the focused catalog test and verify the old model fails the contract**

Run:

```bash
npx vitest run tests/game/catalog.test.ts
```

Expected: FAIL because `TeacherIntervention` and structured triggers do not
exist and the fixture still requires the displaced `misconceptions` field.

- [ ] **Step 3: Replace the metadata types completely**

In `src/game/types.ts`, delete `MisconceptionCue` and replace `TeacherBeat` with:

```ts
export type TeacherTrigger =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'stalled'; readonly level: 1 | 2 | 3 }
  | {
      readonly kind: 'proofState'
      readonly state: DiagramWithBoundary
      readonly demonstration: readonly GameStep[]
    }

export type TeacherIntervention = {
  readonly id: string
  readonly performance?: PerformanceId
  readonly trigger: TeacherTrigger
  readonly text: string
  readonly repeat: 'once' | 'repeatable'
  readonly recovery?: 'timeline'
}
```

Change `PuzzleDefinition.teacher` to
`readonly teacher: readonly TeacherIntervention[]` and delete
`PuzzleDefinition.misconceptions`. Do not retain aliases, deprecated types,
optional compatibility properties, or a second content-authored thought path.

Update `tests/game/catalog-fixture.ts` to use:

```ts
teacher: [{
  id: 'opening-pair',
  performance: fixturePerformanceId,
  trigger: { kind: 'opening' },
  text: 'Look for the nested pair.',
  repeat: 'once',
}],
```

- [ ] **Step 4: Validate static intervention metadata**

In `buildCatalog`, require unique intervention IDs within each puzzle; trimmed
nonempty IDs and text; present optional performance references; and a safe
integer stalled level from 1 through 3. Use an exhaustive switch on
`intervention.trigger.kind`. For a `proofState` trigger, require a nonempty
demonstration and call `assertClosedGoal(trigger.state)`. Reject canonical blank
as a proof-state trigger because completion owns that event.

Delete every validation branch and error message mentioning misconceptions or
thoughts.

- [ ] **Step 5: Prove proof-state triggers are legally reachable**

In the existing dependency-ordered catalog verification loop, reuse the exact
prerequisite-scoped `authority` created for the puzzle witness. For every
proof-state intervention, start a fresh puzzle session, replay its
`demonstration` through `applyGameStep`, and compare:

```ts
const reached = exploreForm(currentDiagram(session))
const declared = exploreForm(intervention.trigger.state.diagram)
if (reached !== declared) {
  throw new GameDomainError(
    `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' demonstration does not reach its declared proof state`,
  )
}
```

Do not catch or convert invalid game steps into a success-shaped fallback. A
bad demonstration must make catalog construction fail.

- [ ] **Step 6: Fingerprint the complete replacement authority**

Replace the old `teacher` and `misconceptions` fingerprint entries with one
ordered `teacher` entry. Include `id`, optional performance, text, repeat,
recovery, trigger kind, stalled level when present, the canonical explored form
of a proof-state diagram, and no raw demonstration-step IDs. The demonstration
is validation evidence rather than player-visible content: two legal traces to
the same canonical trigger state must yield the same content fingerprint.
Preserve authored intervention order.

- [ ] **Step 7: Write failing runtime matching tests**

Create `tests/game/teaching.test.ts`. Construct the four-veil puzzle and the
`reachedTwoVeils` intervention from Step 1. Assert:

```ts
expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set()))
  .toEqual([opening])
expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set([opening.id])))
  .toEqual([])

const transition = applyGameStep(
  startPuzzle(puzzle),
  { rule: 'doubleCutElim', region: four.eliminations[0]! },
  authority,
)
expect(teacherInterventionsFor(
  puzzle,
  { kind: 'proofState', diagram: currentDiagram(transition.session) },
  new Set(),
)).toEqual([reachedTwoVeils])
```

Also assert that a different valid state does not match, stalled levels match
only the exact authored level, completion matches only completion, a seen
`once` intervention is suppressed, and a seen `repeatable` intervention remains
available.

Finally attempt an invalid game step against an unchanged session, assert it
throws and the original current diagram remains identical, and do not emit a
teacher signal. This proves refusal remains outside the teacher path; rendering
the red thought stays with the interaction layer.

- [ ] **Step 8: Implement the pure teacher matcher and export it**

Create `src/game/teaching.ts`:

```ts
import type { Diagram } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { PuzzleDefinition, TeacherIntervention } from './types'

export type TeacherSignal =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'stalled'; readonly level: 1 | 2 | 3 }
  | { readonly kind: 'proofState'; readonly diagram: Diagram }

export function teacherInterventionsFor(
  puzzle: PuzzleDefinition,
  signal: TeacherSignal,
  seen: ReadonlySet<string>,
): readonly TeacherIntervention[] {
  return puzzle.teacher.filter((intervention) => {
    if (intervention.repeat === 'once' && seen.has(intervention.id)) return false
    const trigger = intervention.trigger
    if (trigger.kind !== signal.kind) return false
    switch (trigger.kind) {
      case 'opening':
      case 'completion': return true
      case 'stalled': return signal.kind === 'stalled' && trigger.level === signal.level
      case 'proofState':
        return signal.kind === 'proofState'
          && exploreForm(trigger.state.diagram) === exploreForm(signal.diagram)
    }
  })
}
```

Export the new module from `src/game/index.ts`. Keep this function pure; seen-ID
persistence and visual presentation belong to the later interface task.

- [ ] **Step 9: Run focused and full game verification**

Run:

```bash
npx vitest run tests/game/catalog.test.ts tests/game/teaching.test.ts tests/game
npm run typecheck
! rg -n "MisconceptionCue|misconceptions|\.thought\b" src/game tests/game
```

Expected: all game tests pass, typecheck exits 0, and the displaced content
model grep has no output. Do not run physics tests.

- [ ] **Step 10: Commit the corrected authority**

```bash
git add src/game/types.ts src/game/catalog.ts src/game/teaching.ts src/game/index.ts tests/game
git commit -m "refactor(game): separate thoughts from teaching"
```

---

## Required Naming and Copy Review Gate

Before Task 5 changes production content, invoke `superpowers:brainstorming` and
present two or three coherent naming systems for both cultures and all seven
artifacts. Each option must show professional names, curator shorthand,
provenance/function, linguistic mutation rationale, and representative teacher
voice. Important artifacts 1, 5, and 7 should be memorable; elective artifact
6 may use a plainer catalogue designation. Record the approved exact strings in
`docs/superpowers/specs/2026-07-11-opening-cultures-content-design.md`, commit
that documentation, and obtain user review before starting Task 5.

Gate satisfied before production content: the exact culture names, artifact
names, curator shorthand, provenance, provisional language bible, performance
graph, teacher interventions, and recognized Orra trap are recorded in
`docs/superpowers/specs/2026-07-11-opening-cultures-content-design.md` and
`docs/superpowers/specs/2026-07-11-cursebreaker-game-design.md`. The written
copy was committed in `5b8fa49` and approved by the user on 2026-07-12. Task 5
must consume those exact strings and may not invent replacements locally.

---

### Task 5: Author the Seven Permanent Opening Artifacts

**Files:**
- Create: `src/game/content/opening.ts`
- Create: `src/game/content/index.ts`
- Modify: `src/game/index.ts`
- Create: `tests/game/opening-content.test.ts`

**Interfaces:**
- Produces: `openingCatalogSource(): GameCatalogSource` and `openingCatalog(): GameCatalog`.
- Consumes: approved names/copy, `DiagramBuilder`, `mkDiagramWithBoundary`, `mkSelection`, and the public culture/learning types.

- [ ] **Step 1: Write the failing opening-catalog contract test**

Assert exact counts and roles:

```ts
const catalog = openingCatalog()
expect(catalog.source.cultures).toHaveLength(2)
expect(catalog.source.puzzles).toHaveLength(7)
expect(catalog.source.performances.length).toBeGreaterThanOrEqual(7)

const ids = catalog.source.puzzles.map((puzzle) => puzzle.id)
expect(ids).toEqual([
  puzzleId('two-veils'), puzzleId('four-veils'), puzzleId('forked-veil'),
  puzzleId('echoed-veil'), puzzleId('single-mark-return'),
  puzzleId('two-mark-projection'), puzzleId('blank-witness'),
])
expect(isRequired(catalog, puzzleId('two-mark-projection'))).toBe(false)
for (const id of ids.filter((id) => id !== puzzleId('two-mark-projection'))) {
  expect(isRequired(catalog, id)).toBe(true)
}
```

Replay every witness with `startPuzzle` and `applyGameStep`, assert canonical
blank, and pin exact rules:

```ts
expect(rules('two-veils')).toEqual(['doubleCutElim'])
expect(rules('four-veils')).toEqual(['doubleCutElim', 'doubleCutElim'])
expect(rules('forked-veil')).toEqual(['erasure', 'doubleCutElim'])
expect(rules('echoed-veil')).toEqual(['deiteration', 'erasure', 'doubleCutElim'])
expect(rules('single-mark-return')).toEqual([
  'deiteration', 'erasure', 'vacuousElim', 'doubleCutElim',
])
expect(rules('two-mark-projection')).toEqual([
  'deiteration', 'erasure', 'erasure', 'vacuousElim', 'vacuousElim', 'doubleCutElim',
])
expect(rules('blank-witness')).toEqual(['comprehensionInstantiate'])
```

Also assert exact region-kind counts, bubble arities, atom-to-binder ownership,
and absence of term/ref nodes for each goal. These structural assertions are the
independent statement check; successful replay alone does not prove the intended
formula was authored.

- [ ] **Step 2: Run the opening test and verify the module is missing**

Run: `npx vitest run tests/game/opening-content.test.ts`

Expected: FAIL because `src/game/content` does not exist.

- [ ] **Step 3: Implement the seven diagrams and witnesses**

Use one private builder per artifact and these proven structures:

```ts
const closed = (builder: DiagramBuilder) => mkDiagramWithBoundary(builder.build(), [])
```

- `two-veils`: root cut containing one cut.
- `four-veils`: four nested cuts; eliminate the inner pair then outer pair.
- `forked-veil`: root cut containing two empty sibling cuts; erase one sibling, then eliminate the remaining pair.
- `echoed-veil`: root cut containing an empty ancestor cut and another cut containing its empty-cut copy; deiterate the copy, erase the ancestor, eliminate the pair.
- `single-mark-return`: root cut → arity-zero bubble → premise atom plus cut containing the same bound atom; deiterate conclusion, erase premise, dissolve bubble, eliminate pair.
- `two-mark-projection`: root cut → nested arity-zero P/Q bubbles → P and Q premise atoms plus cut containing P; deiterate conclusion, erase Q and P, dissolve Q then P, eliminate pair.
- `blank-witness`: positive root arity-zero bubble containing its atom; instantiate it with `mkDiagramWithBoundary(new DiagramBuilder().build(), [])`.

Construct every `SubgraphSelection` against the exact diagram state where its
step runs. Do not guess promoted IDs or duplicate kernel transformation logic.

- [ ] **Step 4: Add approved cultures, performances, and copy**

Use only exact strings approved at the review gate. Culture 1 has no unlock
artifacts and gateway `two-veils`; culture 2 unlocks after
`single-mark-return` and has gateway `blank-witness`. Puzzle prerequisites form
the 1→2→3→4→5 spine; puzzle 6 depends on 5; puzzle 7 relies on its culture gate
and has no duplicate puzzle prerequisite.

Return fresh source structures from `openingCatalogSource()` and pass them to
`buildCatalog` in `openingCatalog()`.

- [ ] **Step 5: Run content, game, kernel-rule, and type checks**

Run:

```bash
npx vitest run tests/game/opening-content.test.ts tests/game tests/kernel/rules/doublecut.test.ts tests/kernel/rules/erasure.test.ts tests/kernel/rules/iteration.test.ts tests/kernel/rules/comprehension-instantiate.test.ts
npm run typecheck
```

Expected: selected tests pass and typecheck exits 0.

- [ ] **Step 6: Commit shipped opening content**

```bash
git add src/game/content src/game/index.ts tests/game/opening-content.test.ts
git commit -m "feat(game): add opening cultural artifacts"
```

---

### Task 6: Prove Save, Boundary, and Displaced-Model Conformance

**Files:**
- Modify: `tests/game/save.test.ts`
- Modify: `tests/architecture/game-boundary.test.ts`
- Modify: `docs/superpowers/plans/2026-07-11-opening-cultures-content.md`

**Interfaces:**
- Validates: fingerprints include culture/content metadata; saves replay opening artifacts; content stays inside the game/kernel boundary; no campaign model remains.

- [ ] **Step 1: Add save and architecture assertions**

Round-trip an active `four-veils` session from `openingCatalog()`, rewound after
both steps, and assert all three states reconstruct. Change one culture history
string in a source clone and assert the old save is refused by fingerprint
drift.

Extend the architecture test:

```ts
const production = tsFilesUnder('src/game')
  .map((file) => readFileSync(file, 'utf8'))
  .join('\n')
expect(production).not.toMatch(/CampaignId|CampaignDefinition|campaignId|\bcampaigns\b/)
expect(production).not.toMatch(/MisconceptionCue|misconceptions|\.thought\b/)
```

- [ ] **Step 2: Run the new assertions**

Run: `npx vitest run tests/game/save.test.ts tests/architecture/game-boundary.test.ts`

Expected: PASS after Tasks 1–5. Repair any failure at its owning source.

- [ ] **Step 3: Run decisive non-physics verification**

Run:

```bash
npx vitest run tests/game tests/architecture/game-boundary.test.ts tests/kernel/rules/doublecut.test.ts tests/kernel/rules/erasure.test.ts tests/kernel/rules/iteration.test.ts tests/kernel/rules/comprehension-instantiate.test.ts
npm run typecheck
git diff --check
! git diff --name-only | rg 'src/view|physics|wirephys|relax'
! rg -n "CampaignId|CampaignDefinition|campaignId|campaigns|\.campaign\b" src/game tests/game
! rg -n "MisconceptionCue|misconceptions|\.thought\b" src/game tests/game
```

Expected: tests pass; typecheck and diff check exit 0; all scope greps have no
output. Do not run the physics battery.

- [ ] **Step 4: Append implementation evidence to this plan**

Mark completed checkboxes and append exact test counts, typecheck result, commit
identities, the approved naming record, and confirmation that campaign and
physics diffs are absent.

- [ ] **Step 5: Commit conformance evidence**

```bash
git add tests/game/save.test.ts tests/architecture/game-boundary.test.ts docs/superpowers/plans/2026-07-11-opening-cultures-content.md
git commit -m "test(game): verify opening culture content"
```
