# Game Structural Delete Selection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make game Delete/Backspace structural eliminations honor exact highlighted intent while preserving the existing atomic multi-vacuous macro.

**Architecture:** Keep canonical `absorbHits` selection construction for ordinary proof rules, but filter game-owned `doubleCutElim` and singleton `vacuousElim` descriptors using the original exact hits inside `discoverGameProofActions`. Keep `vacuousEliminationChainSteps` unchanged and narrow only the failed-batch recognizer so mixed content reaches ordinary deletion.

**Tech Stack:** TypeScript, Vitest, `GameProofMoveController`, authenticated `ProofAction` steps.

## Global Constraints

- Modify only game interaction code and game interaction tests on `game/cursebreaker`.
- Preserve double-cut eligibility for exactly the outer rim or outer-plus-inner rims.
- Preserve singleton vacuous elimination for exactly one vacuous bubble rim.
- Preserve the existing distinct, gapless, deepest-first, preflighted atomic multi-vacuous macro.
- Mixed interior content suppresses structural elimination and falls through to existing later rules.
- Do not run the physics suite; authoritative validation is focused game tests, typecheck, and the ordinary non-physics suite.

---

## File Structure

- `src/game/interface/proof-moves.ts` owns exact game selection intent, valid macro recognition, failed-macro refusal, and controller dispatch.
- `tests/game/game-proof-controller-routes.test.ts` owns direct discovery, keyboard, menu, fallback, and macro regression evidence.

### Task 1: Preserve exact structural deletion intent

**Files:**
- Modify: `src/game/interface/proof-moves.ts:89-150,350-390`
- Test: `tests/game/game-proof-controller-routes.test.ts:1-340`

**Interfaces:**
- Consumes: `discoverGameProofActions(diagram: Diagram, hits: readonly Hit[], context: ProofContext): Discovery | null`, `vacuousEliminationChainSteps(...)`, `GameProofMoveController.keyDown(...)`, and `GameProofMoveController.contextMenu(...)`.
- Produces: the same public signatures, with `Discovery.actions` filtered by exact structural intent and failed macro refusal limited to all-bubble selections.

- [ ] **Step 1: Write failing exact-intent regressions**

Import `discoverGameProofActions` and `Hit` in `tests/game/game-proof-controller-routes.test.ts`. Add this focused block; the fallback fixtures live inside a negative enclosing cut so ordinary backward erasure is available after structural candidates are filtered.

```ts
describe('exact structural deletion intent', () => {
  const deleteSteps = (diagram: Diagram, hits: readonly Hit[]): readonly ProofStep[] => {
    const applied: ProofAction[] = []
    const selection = { value: hits }
    const controller = controllerFor(diagram, selection, applied, [])
    expect(controller.keyDown(key({ key: 'Delete' }))).toBe(true)
    return stepsFrom(applied)
  }

  it('offers double-cut elimination only for the outer rim or outer-plus-inner rims', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const inner = builder.cut(outer)
    const node = builder.termNode(inner, parseTerm('x'))
    const diagram = builder.build()
    const kinds = (hits: readonly Hit[]) => discoverGameProofActions(
      diagram, hits, EMPTY_PROOF_CONTEXT,
    )!.actions.map(({ kind }) => kind)

    expect(kinds([{ kind: 'region', id: outer }])).toContain('doubleCutElim')
    expect(kinds([
      { kind: 'region', id: inner },
      { kind: 'region', id: outer },
    ])).toContain('doubleCutElim')
    expect(kinds([
      { kind: 'region', id: outer },
      { kind: 'node', id: node },
    ])).not.toContain('doubleCutElim')

    for (const hits of [
      [{ kind: 'region' as const, id: outer }],
      [{ kind: 'region' as const, id: inner }, { kind: 'region' as const, id: outer }],
    ]) expect(deleteSteps(diagram, hits).map(({ rule }) => rule)).toEqual(['doubleCutElim'])
  })

  it('offers singleton vacuous elimination only for the bubble rim', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const node = builder.termNode(bubble, parseTerm('x'))
    const diagram = builder.build()
    const kinds = (hits: readonly Hit[]) => discoverGameProofActions(
      diagram, hits, EMPTY_PROOF_CONTEXT,
    )!.actions.map(({ kind }) => kind)

    expect(kinds([{ kind: 'region', id: bubble }])).toContain('vacuousElim')
    expect(kinds([
      { kind: 'region', id: bubble },
      { kind: 'node', id: node },
    ])).not.toContain('vacuousElim')

    expect(deleteSteps(diagram, [{ kind: 'region', id: bubble }]).map(({ rule }) => rule))
      .toEqual(['vacuousElim'])
  })

  it('falls through to erasure for a selected double cut plus interior content', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const outer = builder.cut(enclosing)
    const inner = builder.cut(outer)
    const node = builder.termNode(inner, parseTerm('x'))
    const diagram = builder.build()

    expect(deleteSteps(diagram, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: node },
    ]).map(({ rule }) => rule)).toEqual(['erasure'])
  })

  it('falls through to erasure for a selected vacuous bubble plus interior content', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const bubble = builder.bubble(enclosing, 0)
    const node = builder.termNode(bubble, parseTerm('x'))
    const diagram = builder.build()

    expect(deleteSteps(diagram, [
      { kind: 'region', id: bubble },
      { kind: 'node', id: node },
    ]).map(({ rule }) => rule)).toEqual(['erasure'])
  })

  it('falls through to erasure for a selected vacuous chain plus interior content', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const outer = builder.bubble(enclosing, 0)
    const inner = builder.bubble(outer, 0)
    const node = builder.termNode(inner, parseTerm('x'))
    const diagram = builder.build()

    expect(deleteSteps(diagram, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: node },
    ]).map(({ rule }) => rule)).toEqual(['erasure'])
  })

  it('omits mixed-selection structural actions from the context menu', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const outer = builder.cut(enclosing)
    const inner = builder.cut(outer)
    const cutNode = builder.termNode(inner, parseTerm('x'))
    const bubble = builder.bubble(enclosing, 0)
    const bubbleNode = builder.termNode(bubble, parseTerm('y'))
    const diagram = builder.build()
    const labels = (hits: readonly Hit[]): readonly string[] => {
      const document = new MenuDocument()
      const host = new MenuElement(document)
      const controller = new GameProofMoveController({
        host: host as unknown as HTMLElement,
        active: () => true,
        diagram: () => diagram,
        engine: () => mkEngine(diagram, []),
        viewScale: () => 1,
        selection: () => hits,
        setSelection: () => undefined,
        context: () => EMPTY_PROOF_CONTEXT,
        apply: () => undefined,
        refuse: (message) => { throw new Error(message) },
        theme: () => DARK,
        fuel: () => 256,
        openConstruction: () => undefined,
      })
      expect(controller.contextMenu(pointerSample(hits[0]!))).toBe(true)
      return host.querySelectorAll<MenuElement>('.curse-context-menu__action')
        .map(({ textContent }) => textContent)
    }

    const doubleCutLabels = labels([
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: cutNode },
    ])
    expect(doubleCutLabels).not.toContain('Eliminate the double cut')
    expect(doubleCutLabels).toContain('Erase (negative region)')

    const bubbleLabels = labels([
      { kind: 'region', id: bubble },
      { kind: 'node', id: bubbleNode },
    ])
    expect(bubbleLabels).not.toContain('Dissolve the vacuous bubble')
    expect(bubbleLabels).toContain('Erase (negative region)')
  })
})
```

Use `Diagram` and `ProofStep` type imports for `deleteSteps`. Reuse the existing `controllerFor`, `MenuDocument`, `MenuElement`, `pointerSample`, and `stepsFrom` helpers; do not introduce mocks of discovery or dispatch.

- [ ] **Step 2: Run the focused tests and verify RED**

Run:

```bash
npx vitest run tests/game/game-proof-controller-routes.test.ts -t "exact structural deletion intent"
```

Expected: failures show `doubleCutElim` and `vacuousElim` remain present for mixed selections, mixed multi-bubble selection refuses as a batch request, and the menu still contains the structural labels.

- [ ] **Step 3: Filter structural descriptors using exact hits**

Add private game-owned predicates beside `discoverGameProofActions`:

```ts
function exactDoubleCutIntent(
  diagram: Diagram,
  hits: readonly Hit[],
  selection: SubgraphSelection,
): boolean {
  const outer = selection.regions.length === 1 ? selection.regions[0] : undefined
  if (outer === undefined || hits.some((hit) => hit.kind !== 'region')) return false
  const ids = hits.map((hit) => hit.id)
  if (new Set(ids).size !== ids.length || !ids.includes(outer)) return false
  if (ids.length === 1) return true
  if (ids.length !== 2) return false
  const inner = ids.find((id) => id !== outer)!
  const region = diagram.regions[inner]
  return region?.kind === 'cut' && region.parent === outer
}

function exactSingletonRegionIntent(hits: readonly Hit[], region: RegionId): boolean {
  return hits.length === 1 && hits[0]?.kind === 'region' && hits[0].id === region
}
```

Build the canonical selection and ordinary descriptor list exactly once, then filter only the two intent-sensitive actions:

```ts
const actions = applicableActions(diagram, selection, context, true)
  .filter((action) => action.kind !== 'citeTheorem')
  .filter((action) => {
    if (action.kind === 'doubleCutElim') return exactDoubleCutIntent(diagram, hits, selection)
    if (action.kind === 'vacuousElim') {
      return selection.regions.length === 1
        && exactSingletonRegionIntent(hits, selection.regions[0]!)
    }
    return true
  })
return { selection, actions }
```

Do not change `applicableActions`, `absorbHits`, kernel appliers, contextual precedence, or `vacuousEliminationChainSteps`.

- [ ] **Step 4: Let mixed multi-bubble selections fall through**

Replace the broad count in `isVacuousBatchRequest` with an exact all-bubble request predicate:

```ts
const isVacuousBatchRequest = (diagram: Diagram, hits: readonly Hit[]): boolean =>
  hits.length >= 2 && hits.every((hit) =>
    hit.kind === 'region' && diagram.regions[hit.id]?.kind === 'bubble')
```

This retains the focused refusal for invalid all-bubble selections while allowing any mixed-content selection to reach filtered ordinary discovery.

- [ ] **Step 5: Run focused GREEN and existing macro tests**

Run:

```bash
npx vitest run tests/game/game-proof-controller-routes.test.ts
```

Expected: the exact-intent regressions pass together with the existing macro tests proving gapless recognition, deepest-first ordering, atomic history, one selection clear, and invalid-chain refusal.

- [ ] **Step 6: Run proportional validation**

Run:

```bash
npm run typecheck
npm test
```

Expected: typecheck exits 0 and the ordinary Vitest configuration passes while excluding `tests/physics/**/*.test.ts` through `vitest.suites.ts`.

- [ ] **Step 7: Inspect the final diff and commit**

Run:

```bash
git diff --check
git diff -- src/game/interface/proof-moves.ts tests/game/game-proof-controller-routes.test.ts
git status --short
git add src/game/interface/proof-moves.ts tests/game/game-proof-controller-routes.test.ts docs/superpowers/plans/2026-07-22-game-structural-delete-selection.md
git commit -m "fix(game): respect structural delete selection intent"
```

Expected: only the game proof controller, its focused tests, and this plan are committed; no shared non-game or physics files change.
