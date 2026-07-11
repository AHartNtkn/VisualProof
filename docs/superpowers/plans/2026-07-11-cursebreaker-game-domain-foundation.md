# Cursebreaker Game Domain Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the headless game-native authority for closed backward puzzles, exact solved-seal vellums, immutable timelines, durable progression, catalog verification, and versioned active-session saves.

**Architecture:** Add a new `src/game` package that depends only on `src/kernel`, never on the incumbent proof-assistant `src/app` or bundled `src/theories`. Kernel proof primitives remain the soundness authority, while the game package narrows them to non-theorem backward steps and owns exact closed-seal invocation. This plan intentionally does not integrate UI or author the apprenticeship catalog; those follow after the game domain and representative content spikes are validated.

**Tech Stack:** TypeScript 5.5 strict mode, Vitest 2, existing immutable diagram kernel and canonical explorer.

## Global Constraints

- The game is the sole eventual product on `game/cursebreaker`; this foundation must create no sibling entry point or feature flag.
- Every game puzzle is one closed zero-boundary theorem whose implicit source is blank.
- Runtime play is backward-only; no game API may accept forward orientation or a general theorem step.
- A vellum may only manifest one complete solved seal or dissolve one exact canonical occurrence.
- Timeline rewind retains future states; applying from the past truncates the abandoned future.
- First completion is durable and independent of the current timeline cursor.
- Saves contain only versioned game progress, settings-ready metadata, and replayable active-session state; no external theories or arbitrary authored diagrams.
- Existing user changes and unrelated baseline failures remain untouched.
- Production code follows TDD: write one failing behavior test, observe the expected failure, implement minimally, and rerun focused plus relevant broader tests.

---

## File Structure

### New production files

- `src/game/types.ts` — branded identifiers, puzzle/catalog values, game-step types, and shared validation errors.
- `src/game/blank.ts` — the unique blank diagram and canonical blank comparison.
- `src/game/vellum.ts` — exact whole-seal manifestation and dissolution.
- `src/game/session.ts` — backward-only step application, immutable retained timeline, cursor movement, branch truncation, and completion detection.
- `src/game/progress.ts` — durable completion set, unlock derivation, and available vellums.
- `src/game/catalog.ts` — catalog construction, dependency validation, witness replay, and content fingerprints.
- `src/game/save.ts` — version-1 save serialization, validation, replay, and drift refusal.
- `src/game/index.ts` — the only public barrel for this package.

### New test files

- `tests/game/fixtures.ts` — deterministic blank, two-veil, and four-veil fixtures.
- `tests/game/blank.test.ts`
- `tests/game/vellum.test.ts`
- `tests/game/session.test.ts`
- `tests/game/progress.test.ts`
- `tests/game/catalog.test.ts`
- `tests/game/save.test.ts`
- `tests/architecture/game-boundary.test.ts`

No existing production file is modified until Task 6 adds the package boundary test and public export verification. The current application remains runnable during this foundation plan; its deletion and consumer migration belong to the later product-layer plan.

---

### Task 1: Closed Puzzle Vocabulary and Blank Authority

**Files:**
- Create: `src/game/types.ts`
- Create: `src/game/blank.ts`
- Create: `tests/game/fixtures.ts`
- Create: `tests/game/blank.test.ts`

**Interfaces:**
- Produces: `PuzzleId`, `CampaignId`, `GameKernelStep`, `GameStep`, `PuzzleDefinition`, `GameCatalogSource`, `GameRuleContext`, `GameDomainError`.
- Produces: `blankDiagram(): Diagram`, `isBlank(diagram: Diagram): boolean`, `assertClosedGoal(goal: DiagramWithBoundary): void`.
- Consumes: kernel `Diagram`, `DiagramWithBoundary`, `ProofStep`, and relation definitions.

- [ ] **Step 1: Write deterministic fixture builders**

Create `tests/game/fixtures.ts`:

```ts
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { RegionId } from '../../src/kernel/diagram/diagram'

export type VeilFixture = {
  readonly goal: DiagramWithBoundary
  readonly eliminations: readonly RegionId[]
}

export function twoVeils(): VeilFixture {
  const b = new DiagramBuilder()
  const outer = b.cut(b.root)
  b.cut(outer)
  return { goal: mkDiagramWithBoundary(b.build(), []), eliminations: [outer] }
}

export function fourVeils(): VeilFixture {
  const b = new DiagramBuilder()
  const outer = b.cut(b.root)
  const second = b.cut(outer)
  const third = b.cut(second)
  b.cut(third)
  return { goal: mkDiagramWithBoundary(b.build(), []), eliminations: [third, outer] }
}
```

- [ ] **Step 2: Write failing blank and closed-goal tests**

Create `tests/game/blank.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { blankDiagram, isBlank, assertClosedGoal } from '../../src/game/blank'
import { twoVeils } from './fixtures'

describe('game blank authority', () => {
  it('recognizes blank canonically and rejects nonblank diagrams', () => {
    expect(isBlank(blankDiagram())).toBe(true)
    expect(isBlank(twoVeils().goal.diagram)).toBe(false)
  })

  it('accepts only zero-boundary puzzle goals', () => {
    const b = new DiagramBuilder()
    const wire = b.wire(b.root, [])
    expect(() => assertClosedGoal(mkDiagramWithBoundary(b.build(), [wire])))
      .toThrow(/puzzle goal must be closed/)
    expect(() => assertClosedGoal(twoVeils().goal)).not.toThrow()
  })
})
```

- [ ] **Step 3: Run the focused test and verify the expected failure**

Run: `npx vitest run tests/game/blank.test.ts`

Expected: FAIL because `src/game/blank.ts` does not exist.

- [ ] **Step 4: Implement the game vocabulary**

Create `src/game/types.ts`:

```ts
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofStep, ProofContext } from '../kernel/proof/step'

export type PuzzleId = string & { readonly __puzzleId: unique symbol }
export type CampaignId = string & { readonly __campaignId: unique symbol }

export const puzzleId = (value: string): PuzzleId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid puzzle id '${value}'`)
  }
  return value as PuzzleId
}

export const campaignId = (value: string): CampaignId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid campaign id '${value}'`)
  }
  return value as CampaignId
}

export class GameDomainError extends Error {}

export type GameKernelStep = Exclude<ProofStep, { readonly rule: 'theorem' }>

export type VellumStep =
  | { readonly rule: 'vellumManifest'; readonly puzzle: PuzzleId; readonly region: RegionId }
  | { readonly rule: 'vellumDissolve'; readonly puzzle: PuzzleId; readonly selection: SubgraphSelection }

export type GameStep = GameKernelStep | VellumStep

export type GameRuleContext = Pick<ProofContext, 'relations'>

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly campaign: CampaignId
  readonly title: string
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly grantsVellum: boolean
  readonly witness: readonly GameStep[]
}

export type CampaignDefinition = {
  readonly id: CampaignId
  readonly title: string
}

export type GameCatalogSource = {
  readonly campaigns: readonly CampaignDefinition[]
  readonly puzzles: readonly PuzzleDefinition[]
  readonly context: GameRuleContext
}
```

- [ ] **Step 5: Implement canonical blank comparison**

Create `src/game/blank.ts`:

```ts
import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { GameDomainError } from './types'

const blank = new DiagramBuilder().build()
const blankForm = exploreForm(blank)

export function blankDiagram(): Diagram {
  return blank
}

export function isBlank(diagram: Diagram): boolean {
  return exploreForm(diagram) === blankForm
}

export function assertClosedGoal(goal: DiagramWithBoundary): void {
  if (goal.boundary.length !== 0) {
    throw new GameDomainError(`puzzle goal must be closed; received boundary arity ${goal.boundary.length}`)
  }
}
```

- [ ] **Step 6: Run focused tests and typecheck**

Run: `npx vitest run tests/game/blank.test.ts && npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add src/game/types.ts src/game/blank.ts tests/game/fixtures.ts tests/game/blank.test.ts
git commit -m "feat(game): define closed puzzle vocabulary"
```

---

### Task 2: Exact Whole-Seal Vellum Operations

**Files:**
- Create: `src/game/vellum.ts`
- Create: `tests/game/vellum.test.ts`

**Interfaces:**
- Consumes: `PuzzleDefinition`, `Diagram`, `RegionId`, `SubgraphSelection`.
- Produces: `manifestSeal(host, region, puzzle): Diagram` and `dissolveSeal(host, selection, puzzle): Diagram`.
- Guarantees: only zero-boundary goals; no host attachments; no external binder capture; exact canonical whole-seal equality.

- [ ] **Step 1: Write failing exactness tests**

Create `tests/game/vellum.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { campaignId, puzzleId, type PuzzleDefinition } from '../../src/game/types'
import { manifestSeal, dissolveSeal } from '../../src/game/vellum'
import { twoVeils } from './fixtures'

const fixture = twoVeils()
const seal: PuzzleDefinition = {
  id: puzzleId('two-veils'), campaign: campaignId('apprenticeship'), title: 'Two Veils',
  goal: fixture.goal, prerequisites: [], grantsVellum: true,
  witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
}

describe('exact solved-seal vellums', () => {
  it('manifests one whole closed seal in a chosen region', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    expect(exploreForm(manifested)).toBe(exploreForm(seal.goal.diagram))
  })

  it('dissolves only an exact whole occurrence', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    const outer = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === manifested.root)![0]
    const selection = mkSelection(manifested, { region: manifested.root, regions: [outer], nodes: [], wires: [] })
    expect(isBlank(dissolveSeal(manifested, selection, seal))).toBe(true)
  })

  it('refuses a strict subgraph and leaves the caller-owned diagram unchanged', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    const outer = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === manifested.root)![0]
    const inner = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === outer)![0]
    const selection = mkSelection(manifested, { region: outer, regions: [inner], nodes: [], wires: [] })
    const before = exploreForm(manifested)
    expect(() => dissolveSeal(manifested, selection, seal)).toThrow(/not an exact occurrence/)
    expect(exploreForm(manifested)).toBe(before)
  })
})
```

- [ ] **Step 2: Run the focused test and verify the expected failure**

Run: `npx vitest run tests/game/vellum.test.ts`

Expected: FAIL because `src/game/vellum.ts` does not exist.

- [ ] **Step 3: Implement exact manifestation and dissolution**

Create `src/game/vellum.ts`:

```ts
import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../kernel/diagram/subgraph/splice'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { assertClosedGoal } from './blank'
import { GameDomainError, type PuzzleDefinition } from './types'

export function manifestSeal(host: Diagram, region: RegionId, puzzle: PuzzleDefinition): Diagram {
  assertClosedGoal(puzzle.goal)
  return spliceSubgraph(host, region, puzzle.goal, [])
}

export function dissolveSeal(
  host: Diagram,
  selection: SubgraphSelection,
  puzzle: PuzzleDefinition,
): Diagram {
  assertClosedGoal(puzzle.goal)
  const extraction = extractSubgraph(host, selection)
  if (extraction.attachments.length !== 0 || extraction.binderStubs.length !== 0
    || exploreForm(extraction.pattern.diagram) !== exploreForm(puzzle.goal.diagram)) {
    throw new GameDomainError(`selection is not an exact occurrence of solved seal '${puzzle.id}'`)
  }
  return removeSubgraph(host, selection)
}
```

- [ ] **Step 4: Run focused and canonical-subgraph tests**

Run: `npx vitest run tests/game/vellum.test.ts tests/kernel/diagram/extract.test.ts tests/kernel/diagram/splice.test.ts`

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/game/vellum.ts tests/game/vellum.test.ts
git commit -m "feat(game): add exact solved-seal vellums"
```

---

### Task 3: Backward-Only Retained Timeline

**Files:**
- Create: `src/game/session.ts`
- Create: `tests/game/session.test.ts`

**Interfaces:**
- Produces: `GameTimeline`, `GameSession`, `GameTransition`.
- Produces: `startPuzzle`, `currentDiagram`, `moveCursor`, `applyGameStep`.
- Consumes: puzzle lookup and solved-vellum availability through `GameRuntimeAuthority`.

- [ ] **Step 1: Write failing session tests**

Create `tests/game/session.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { campaignId, puzzleId, type PuzzleDefinition } from '../../src/game/types'
import { applyGameStep, currentDiagram, moveCursor, startPuzzle } from '../../src/game/session'
import { isBlank } from '../../src/game/blank'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle: PuzzleDefinition = {
  id: puzzleId('four-veils'), campaign: campaignId('apprenticeship'), title: 'Four Veils',
  goal: fixture.goal, prerequisites: [], grantsVellum: true,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
}
const authority = {
  context: { relations: new Map() },
  puzzle(id: string) { if (id !== puzzle.id) throw new Error('unknown fixture puzzle'); return puzzle },
  canUseVellum() { return false },
}

describe('backward game session', () => {
  it('applies only backward kernel moves and completes on canonical blank', () => {
    const start = startPuzzle(puzzle)
    const first = applyGameStep(start, puzzle.witness[0]!, authority)
    expect(first.completedNow).toBe(false)
    const second = applyGameStep(first.session, puzzle.witness[1]!, authority)
    expect(second.completedNow).toBe(true)
    expect(isBlank(currentDiagram(second.session))).toBe(true)
  })

  it('retains future while scrubbing and truncates it on a new continuation', () => {
    const first = applyGameStep(startPuzzle(puzzle), puzzle.witness[0]!, authority).session
    const solved = applyGameStep(first, puzzle.witness[1]!, authority).session
    const rewound = moveCursor(solved, 0)
    expect(rewound.timeline.states).toHaveLength(3)
    const branched = applyGameStep(rewound, puzzle.witness[0]!, authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.steps).toHaveLength(1)
    expect(branched.timeline.cursor).toBe(1)
  })

  it('refuses a general theorem step at the type boundary', () => {
    // @ts-expect-error game sessions do not accept proof-assistant theorem rewrites
    applyGameStep(startPuzzle(puzzle), { rule: 'theorem', name: 'x', direction: 'forward', at: {} }, authority)
  })
})
```

- [ ] **Step 2: Run the focused test and verify the expected failure**

Run: `npx vitest run tests/game/session.test.ts`

Expected: FAIL because `src/game/session.ts` does not exist.

- [ ] **Step 3: Implement the backward timeline**

Create `src/game/session.ts`:

```ts
import type { Diagram } from '../kernel/diagram/diagram'
import { applyStep } from '../kernel/proof/step'
import { isBlank } from './blank'
import { dissolveSeal, manifestSeal } from './vellum'
import { GameDomainError, type GameRuleContext, type GameStep, type PuzzleDefinition, type PuzzleId } from './types'

export type GameTimeline = {
  readonly states: readonly Diagram[]
  readonly steps: readonly GameStep[]
  readonly cursor: number
}

export type GameSession = {
  readonly puzzle: PuzzleId
  readonly timeline: GameTimeline
}

export type GameTransition = {
  readonly session: GameSession
  readonly completedNow: boolean
}

export type GameRuntimeAuthority = {
  readonly context: GameRuleContext
  puzzle(id: PuzzleId): PuzzleDefinition
  canUseVellum(id: PuzzleId): boolean
}

export function startPuzzle(puzzle: PuzzleDefinition): GameSession {
  return { puzzle: puzzle.id, timeline: { states: [puzzle.goal.diagram], steps: [], cursor: 0 } }
}

export function currentDiagram(session: GameSession): Diagram {
  const diagram = session.timeline.states[session.timeline.cursor]
  if (diagram === undefined) throw new GameDomainError('game timeline cursor is out of bounds')
  return diagram
}

export function moveCursor(session: GameSession, cursor: number): GameSession {
  if (!Number.isInteger(cursor) || cursor < 0 || cursor >= session.timeline.states.length) {
    throw new GameDomainError(`timeline position ${cursor} is outside 0..${session.timeline.states.length - 1}`)
  }
  return { ...session, timeline: { ...session.timeline, cursor } }
}

export function applyGameStep(
  session: GameSession,
  step: GameStep,
  authority: GameRuntimeAuthority,
): GameTransition {
  const current = currentDiagram(session)
  let next: Diagram
  if (step.rule === 'vellumManifest' || step.rule === 'vellumDissolve') {
    if (!authority.canUseVellum(step.puzzle)) {
      throw new GameDomainError(`solved seal '${step.puzzle}' is not available`)
    }
    const puzzle = authority.puzzle(step.puzzle)
    next = step.rule === 'vellumManifest'
      ? manifestSeal(current, step.region, puzzle)
      : dissolveSeal(current, step.selection, puzzle)
  } else {
    next = applyStep(current, step, { theorems: new Map(), relations: authority.context.relations }, 'backward')
  }
  const states = session.timeline.states.slice(0, session.timeline.cursor + 1)
  const steps = session.timeline.steps.slice(0, session.timeline.cursor)
  const updated: GameSession = {
    ...session,
    timeline: { states: [...states, next], steps: [...steps, step], cursor: steps.length + 1 },
  }
  return { session: updated, completedNow: !isBlank(current) && isBlank(next) }
}
```

- [ ] **Step 4: Run focused tests and typecheck**

Run: `npx vitest run tests/game/session.test.ts && npm run typecheck`

Expected: PASS, including the `@ts-expect-error` assertion.

- [ ] **Step 5: Commit**

```bash
git add src/game/session.ts tests/game/session.test.ts
git commit -m "feat(game): add backward retained timeline"
```

---

### Task 4: Verified Catalog and Durable Progression

**Files:**
- Create: `src/game/catalog.ts`
- Create: `src/game/progress.ts`
- Create: `tests/game/catalog.test.ts`
- Create: `tests/game/progress.test.ts`

**Interfaces:**
- Produces: `GameCatalog` with a stable `fingerprint` field and `buildCatalog(source)`.
- Produces: `GameProgress`, `emptyProgress`, `recordCompletion`, `isUnlocked`, `availableVellums`.
- Catalog witness replay uses only prerequisite vellums and must finish at blank.

- [ ] **Step 1: Write failing catalog tests**

Create `tests/game/catalog.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { campaignId, puzzleId } from '../../src/game/types'
import { twoVeils } from './fixtures'

const fixture = twoVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const puzzle = {
  id: puzzleId('two-veils'), campaign: campaign.id, title: 'Two Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: [{ rule: 'doubleCutElim' as const, region: fixture.eliminations[0]! }],
}

describe('verified game catalog', () => {
  it('accepts a closed puzzle whose backward witness reaches blank', () => {
    const catalog = buildCatalog({ campaigns: [campaign], puzzles: [puzzle], context: { relations: new Map() } })
    expect(catalog.puzzle(puzzle.id)).toBe(puzzle)
  })

  it('rejects missing prerequisites and dependency cycles', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzleId('missing')] }],
    })).toThrow(/missing prerequisite/)
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzle.id] }],
    })).toThrow(/dependency cycle/)
  })

  it('rejects a witness that does not reach blank', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, witness: [] }],
    })).toThrow(/witness does not reach blank/)
  })
})
```

- [ ] **Step 2: Write failing progression tests**

Create `tests/game/progress.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { availableVellums, emptyProgress, isUnlocked, recordCompletion } from '../../src/game/progress'
import { campaignId, puzzleId, type PuzzleDefinition } from '../../src/game/types'
import { twoVeils } from './fixtures'

const fixture = twoVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const first: PuzzleDefinition = {
  id: puzzleId('two-veils'), campaign: campaign.id, title: 'Two Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
}
const second: PuzzleDefinition = {
  ...first, id: puzzleId('veil-retrieval'), title: 'Veil Retrieval',
  prerequisites: [first.id], grantsVellum: false,
}
const catalog = buildCatalog({ campaigns: [campaign], puzzles: [first, second], context: { relations: new Map() } })

describe('durable game progression', () => {
  it('records first completion immutably and makes repetition idempotent', () => {
    const empty = emptyProgress()
    const completed = recordCompletion(empty, first.id)
    expect(empty.completed.has(first.id)).toBe(false)
    expect(completed.completed.has(first.id)).toBe(true)
    expect(recordCompletion(completed, first.id)).toBe(completed)
  })

  it('unlocks a puzzle only after every prerequisite is complete', () => {
    expect(isUnlocked(catalog, emptyProgress(), first.id)).toBe(true)
    expect(isUnlocked(catalog, emptyProgress(), second.id)).toBe(false)
    expect(isUnlocked(catalog, recordCompletion(emptyProgress(), first.id), second.id)).toBe(true)
  })

  it('offers vellums only for completed puzzles that grant them', () => {
    let progress = recordCompletion(emptyProgress(), first.id)
    progress = recordCompletion(progress, second.id)
    expect([...availableVellums(catalog, progress)]).toEqual([first.id])
  })
})
```

- [ ] **Step 3: Run both tests and verify missing-module failures**

Run: `npx vitest run tests/game/catalog.test.ts tests/game/progress.test.ts`

Expected: FAIL because catalog and progress modules do not exist.

- [ ] **Step 4: Implement catalog validation**

Create `src/game/catalog.ts`:

```ts
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { assertClosedGoal, isBlank } from './blank'
import { applyGameStep, currentDiagram, startPuzzle } from './session'
import { GameDomainError, type GameCatalogSource, type PuzzleDefinition, type PuzzleId } from './types'

export type GameCatalog = {
  readonly source: GameCatalogSource
  readonly fingerprint: string
  puzzle(id: PuzzleId): PuzzleDefinition
}

const unique = <T>(values: readonly T[], label: string): void => {
  const seen = new Set<T>()
  for (const value of values) {
    if (seen.has(value)) throw new GameDomainError(`duplicate ${label} '${String(value)}'`)
    seen.add(value)
  }
}

const hash = (text: string): string => {
  let value = 0x811c9dc5
  for (let i = 0; i < text.length; i++) {
    value ^= text.charCodeAt(i)
    value = Math.imul(value, 0x01000193)
  }
  return (value >>> 0).toString(16).padStart(8, '0')
}

export function buildCatalog(source: GameCatalogSource): GameCatalog {
  unique(source.campaigns.map((campaign) => campaign.id), 'campaign id')
  unique(source.puzzles.map((puzzle) => puzzle.id), 'puzzle id')
  const campaigns = new Set(source.campaigns.map((campaign) => campaign.id))
  const byId = new Map(source.puzzles.map((puzzle) => [puzzle.id, puzzle] as const))
  for (const puzzle of source.puzzles) {
    assertClosedGoal(puzzle.goal)
    if (!campaigns.has(puzzle.campaign)) {
      throw new GameDomainError(`puzzle '${puzzle.id}' names unknown campaign '${puzzle.campaign}'`)
    }
    unique(puzzle.prerequisites, `prerequisite of puzzle '${puzzle.id}'`)
    for (const prerequisite of puzzle.prerequisites) {
      if (!byId.has(prerequisite)) {
        throw new GameDomainError(`puzzle '${puzzle.id}' has missing prerequisite '${prerequisite}'`)
      }
    }
  }

  const visiting = new Set<PuzzleId>()
  const visited = new Set<PuzzleId>()
  const order: PuzzleDefinition[] = []
  const visit = (id: PuzzleId): void => {
    if (visiting.has(id)) throw new GameDomainError(`puzzle dependency cycle includes '${id}'`)
    if (visited.has(id)) return
    visiting.add(id)
    const puzzle = byId.get(id)!
    for (const prerequisite of puzzle.prerequisites) visit(prerequisite)
    visiting.delete(id)
    visited.add(id)
    order.push(puzzle)
  }
  for (const puzzle of source.puzzles) visit(puzzle.id)

  const verified = new Set<PuzzleId>()
  const prerequisiteClosure = (puzzle: PuzzleDefinition): ReadonlySet<PuzzleId> => {
    const closure = new Set<PuzzleId>()
    const add = (id: PuzzleId): void => {
      if (closure.has(id)) return
      closure.add(id)
      for (const parent of byId.get(id)!.prerequisites) add(parent)
    }
    for (const id of puzzle.prerequisites) add(id)
    return closure
  }
  for (const puzzle of order) {
    const allowed = prerequisiteClosure(puzzle)
    const authority = {
      context: source.context,
      puzzle(id: PuzzleId) {
        const found = byId.get(id)
        if (found === undefined) throw new GameDomainError(`unknown puzzle '${id}'`)
        return found
      },
      canUseVellum(id: PuzzleId) {
        return allowed.has(id) && verified.has(id) && byId.get(id)?.grantsVellum === true
      },
    }
    let session = startPuzzle(puzzle)
    for (const step of puzzle.witness) session = applyGameStep(session, step, authority).session
    if (!isBlank(currentDiagram(session))) {
      throw new GameDomainError(`puzzle '${puzzle.id}' witness does not reach blank`)
    }
    verified.add(puzzle.id)
  }

  const fingerprintInput = {
    campaigns: [...source.campaigns]
      .map((campaign) => ({ id: campaign.id, title: campaign.title }))
      .sort((a, b) => a.id.localeCompare(b.id)),
    puzzles: [...source.puzzles]
      .map((puzzle) => ({
        id: puzzle.id, campaign: puzzle.campaign, title: puzzle.title,
        prerequisites: [...puzzle.prerequisites].sort(), grantsVellum: puzzle.grantsVellum,
        goal: exploreForm(puzzle.goal.diagram), witness: puzzle.witness,
      }))
      .sort((a, b) => a.id.localeCompare(b.id)),
  }
  return {
    source,
    fingerprint: hash(JSON.stringify(fingerprintInput)),
    puzzle(id: PuzzleId) {
      const puzzle = byId.get(id)
      if (puzzle === undefined) throw new GameDomainError(`unknown puzzle '${id}'`)
      return puzzle
    },
  }
}
```

- [ ] **Step 5: Implement immutable progression**

Create `src/game/progress.ts`:

```ts
import type { GameCatalog } from './catalog'
import { GameDomainError, type PuzzleDefinition, type PuzzleId } from './types'

export type GameProgress = { readonly completed: ReadonlySet<PuzzleId> }
export const emptyProgress = (): GameProgress => ({ completed: new Set() })

export function recordCompletion(progress: GameProgress, id: PuzzleId): GameProgress {
  if (progress.completed.has(id)) return progress
  return { completed: new Set([...progress.completed, id]) }
}

export function isUnlocked(catalog: GameCatalog, progress: GameProgress, id: PuzzleId): boolean {
  return catalog.puzzle(id).prerequisites.every((prerequisite) => progress.completed.has(prerequisite))
}

export function availableVellums(catalog: GameCatalog, progress: GameProgress): ReadonlySet<PuzzleId> {
  const available = new Set<PuzzleId>()
  for (const id of progress.completed) {
    let puzzle: PuzzleDefinition
    try { puzzle = catalog.puzzle(id) } catch { throw new GameDomainError(`progress names unknown puzzle '${id}'`) }
    if (puzzle.grantsVellum) available.add(id)
  }
  return available
}
```

- [ ] **Step 6: Run focused tests and typecheck**

Run: `npx vitest run tests/game/catalog.test.ts tests/game/progress.test.ts && npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add src/game/catalog.ts src/game/progress.ts tests/game/catalog.test.ts tests/game/progress.test.ts
git commit -m "feat(game): verify catalog and progression"
```

---

### Task 5: Versioned Replayable Save Format

**Files:**
- Create: `src/game/save.ts`
- Create: `tests/game/save.test.ts`

**Interfaces:**
- Produces: `GameSaveV1`, `saveGame`, `loadGame`.
- Saves retained `steps` plus `cursor`, not redundant diagram states.
- Load replay reconstructs all states and refuses catalog drift, unknown completions, malformed cursors, unavailable vellums, or invalid steps.

- [ ] **Step 1: Write failing round-trip and refusal tests**

Create `tests/game/save.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { recordCompletion, emptyProgress } from '../../src/game/progress'
import { applyGameStep, moveCursor, startPuzzle } from '../../src/game/session'
import { loadGame, saveGame } from '../../src/game/save'
import { campaignId, puzzleId, type PuzzleDefinition, type PuzzleId } from '../../src/game/types'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const puzzle: PuzzleDefinition = {
  id: puzzleId('four-veils'), campaign: campaign.id, title: 'Four Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
}
const catalog = buildCatalog({ campaigns: [campaign], puzzles: [puzzle], context: { relations: new Map() } })
const authority = {
  context: catalog.source.context,
  puzzle: (id: PuzzleId) => catalog.puzzle(id),
  canUseVellum: () => false,
}

describe('versioned game save', () => {
  it('round-trips sorted completion ids and a rewound retained timeline', () => {
    let session = startPuzzle(puzzle)
    for (const step of puzzle.witness) session = applyGameStep(session, step, authority).session
    session = moveCursor(session, 1)
    const progress = recordCompletion(emptyProgress(), puzzle.id)
    const encoded = saveGame(catalog, progress, session)
    expect(encoded.completed).toEqual([puzzle.id])
    const loaded = loadGame(catalog, JSON.parse(JSON.stringify(encoded)))
    expect([...loaded.progress.completed]).toEqual([puzzle.id])
    expect(loaded.active?.timeline.states).toHaveLength(3)
    expect(loaded.active?.timeline.cursor).toBe(1)
  })

  it('refuses catalog drift and unknown completion ids', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, { ...encoded, catalogFingerprint: 'drifted' }))
      .toThrow(/catalog fingerprint does not match/)
    expect(() => loadGame(catalog, { ...encoded, completed: ['unknown-puzzle'] }))
      .toThrow(/unknown puzzle/)
  })

  it('refuses an invalid cursor and a forged proof-assistant step', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: { puzzle: puzzle.id, steps: [], cursor: 2 },
    })).toThrow(/active cursor/)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: {
        puzzle: puzzle.id, cursor: 1,
        steps: [{ rule: 'theorem', name: 'forged', direction: 'forward', at: {} }],
      },
    })).toThrow(/unknown theorem|invalid game step/)
  })
})
```

- [ ] **Step 2: Run the focused test and verify the missing-module failure**

Run: `npx vitest run tests/game/save.test.ts`

Expected: FAIL because `src/game/save.ts` does not exist.

- [ ] **Step 3: Implement the save schema and serializer**

Create `src/game/save.ts`:

```ts
import type { GameCatalog } from './catalog'
import { emptyProgress, isUnlocked, recordCompletion, type GameProgress } from './progress'
import { applyGameStep, moveCursor, startPuzzle, type GameRuntimeAuthority, type GameSession } from './session'
import { GameDomainError, type GameStep, type PuzzleId } from './types'

export type GameSaveV1 = {
  readonly format: 'cursebreaker-save'
  readonly version: 1
  readonly catalogFingerprint: string
  readonly completed: readonly PuzzleId[]
  readonly active?: {
    readonly puzzle: PuzzleId
    readonly steps: readonly GameStep[]
    readonly cursor: number
  }
}

export type LoadedGame = {
  readonly progress: GameProgress
  readonly active: GameSession | null
}

const record = (value: unknown, label: string): Record<string, unknown> => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  return value as Record<string, unknown>
}

export function saveGame(
  catalog: GameCatalog,
  progress: GameProgress,
  active: GameSession | null,
): GameSaveV1 {
  const base = {
    format: 'cursebreaker-save' as const,
    version: 1 as const,
    catalogFingerprint: catalog.fingerprint,
    completed: [...progress.completed].sort(),
  }
  return active === null ? base : {
    ...base,
    active: {
      puzzle: active.puzzle,
      steps: active.timeline.steps,
      cursor: active.timeline.cursor,
    },
  }
}

export function loadGame(catalog: GameCatalog, value: unknown): LoadedGame {
  const root = record(value, 'save')
  if (root.format !== 'cursebreaker-save' || root.version !== 1) {
    throw new GameDomainError('unsupported game save format or version')
  }
  if (root.catalogFingerprint !== catalog.fingerprint) {
    throw new GameDomainError('save catalog fingerprint does not match the bundled catalog')
  }
  if (!Array.isArray(root.completed) || !root.completed.every((id) => typeof id === 'string')) {
    throw new GameDomainError('save completed must be an array of puzzle ids')
  }
  let progress = emptyProgress()
  for (const raw of root.completed) {
    const id = raw as PuzzleId
    catalog.puzzle(id)
    progress = recordCompletion(progress, id)
  }
  if (root.active === undefined) return { progress, active: null }

  const active = record(root.active, 'save active session')
  if (typeof active.puzzle !== 'string' || !Array.isArray(active.steps)
    || typeof active.cursor !== 'number' || !Number.isInteger(active.cursor)) {
    throw new GameDomainError('save active session has invalid puzzle, steps, or cursor')
  }
  const puzzle = catalog.puzzle(active.puzzle as PuzzleId)
  if (!isUnlocked(catalog, progress, puzzle.id)) {
    throw new GameDomainError(`active puzzle '${puzzle.id}' is locked by incomplete prerequisites`)
  }
  const steps = active.steps.map((step, index) => {
    if (typeof step !== 'object' || step === null || Array.isArray(step)
      || typeof (step as Record<string, unknown>).rule !== 'string') {
      throw new GameDomainError(`invalid game step at index ${index}`)
    }
    return step as GameStep
  })
  const authority: GameRuntimeAuthority = {
    context: catalog.source.context,
    puzzle: (id) => catalog.puzzle(id),
    canUseVellum: (id) => progress.completed.has(id) && catalog.puzzle(id).grantsVellum,
  }
  let session = startPuzzle(puzzle)
  for (const step of steps) session = applyGameStep(session, step, authority).session
  const cursor = active.cursor as number
  if (cursor < 0 || cursor > steps.length) {
    throw new GameDomainError(`save active cursor ${cursor} is outside 0..${steps.length}`)
  }
  session = moveCursor(session, cursor)
  return { progress, active: session }
}
```

- [ ] **Step 4: Run focused tests, JSON kernel tests, and typecheck**

Run: `npx vitest run tests/game/save.test.ts tests/kernel/proof/json.test.ts && npm run typecheck`

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/game/save.ts tests/game/save.test.ts
git commit -m "feat(game): add replayable local save format"
```

---

### Task 6: Public Boundary and Foundation Verification

**Files:**
- Create: `src/game/index.ts`
- Create: `tests/architecture/game-boundary.test.ts`
- Modify: `docs/superpowers/plans/2026-07-11-cursebreaker-game-domain-foundation.md`

**Interfaces:**
- `src/game/index.ts` exports only the Task 1–5 public game APIs.
- No `src/game` file imports `src/app`, `src/theories`, filesystem access, or proof-assistant theorem/store modules.

- [ ] **Step 1: Write the failing architecture test**

Create `tests/architecture/game-boundary.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { readFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'

describe('game package boundary', () => {
  it('never imports proof-assistant product or bundled prototype theories', () => {
    const files = execFileSync('rg', ['--files', 'src/game'], { encoding: 'utf8' }).trim().split('\n')
    const offenders = files.filter((file) => {
      const source = readFileSync(file, 'utf8')
      return /from ['"]\.\.\/app\//.test(source)
        || /from ['"]\.\.\/theories\//.test(source)
        || /kernel\/proof\/(theorem|store)/.test(source)
        || /fsaccess/.test(source)
    })
    expect(offenders).toEqual([])
  })
})
```

- [ ] **Step 2: Run the architecture test before adding the barrel**

Run: `npx vitest run tests/architecture/game-boundary.test.ts`

Expected: PASS. The package currently has no forbidden imports; the next step establishes its deliberate public surface.

- [ ] **Step 3: Create the public barrel**

Create `src/game/index.ts` exporting:

```ts
export * from './types'
export * from './blank'
export * from './vellum'
export * from './session'
export * from './progress'
export * from './catalog'
export * from './save'
```

- [ ] **Step 4: Run the full new foundation suite**

Run:

```bash
npx vitest run tests/game tests/architecture/game-boundary.test.ts
npm run typecheck
```

Expected: every game-domain and boundary test passes with no warnings.

- [ ] **Step 5: Run the complete existing unit suite and record the inherited baseline**

Run: `npm test`

Expected: all new game tests pass. Compare existing failures with the recorded baseline of one `tests/architecture/layering.test.ts` failure and three `tests/app/session.test.ts` failures. This plan must introduce no additional failures; it does not repair product-layer failures scheduled for later replacement.

- [ ] **Step 6: Mark this plan's checkboxes complete and commit**

```bash
git add src/game/index.ts tests/architecture/game-boundary.test.ts docs/superpowers/plans/2026-07-11-cursebreaker-game-domain-foundation.md
git commit -m "test(game): verify domain foundation boundary"
```

---

## Plan Completion Gate

This plan is complete only when:

- the headless game-domain tests pass;
- strict typecheck passes;
- no new full-suite failure appears beyond the recorded inherited baseline;
- no game package import reaches proof-assistant product, theory-store, or general-theorem authority;
- catalog witnesses replay strictly backward to blank;
- vellum operations are exact whole-seal operations;
- save load reconstructs retained future and cursor solely by replay.

After this gate, replace the foundation record with the evidence learned from the game-domain implementation before writing the curriculum-feasibility/content plan. Do not treat the test fixtures as shipped apprenticeship content.
