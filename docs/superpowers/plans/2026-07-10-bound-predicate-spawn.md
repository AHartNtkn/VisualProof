# Bound-Predicate Spawn Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add semantically bound predicate atoms to the existing contextual spawn cascade, with binder-colored menu circles and hover highlighting of the chosen bubble.

**Architecture:** The kernel's existing atom model remains authoritative. A pure spawn helper derives eligible enclosing bubbles from the invocation region, the edit layer performs one validated atom construction, the cascade presents and dispatches those options, and the shell owns the transient highlighted-binder state and commits through its existing history/placement path.

**Tech Stack:** TypeScript 5.5, Vitest 2, Playwright 1.60, existing immutable diagram kernel, DOM-based spawn cascade, canvas renderer.

## Global Constraints

- Bound predicates and named relation references remain distinct creation requests.
- An atom stores only `region` and `binder`; arity, ports, and color derive from the selected bubble.
- Eligible binders are bubble regions on the invocation region's ancestor chain, ordered innermost first.
- With no eligible binder, no bound-predicate menu section appears.
- Color is not the only discriminator: nested entries also show deterministic nesting position and arity.
- Hover emphasis is view-only and clears on leave, selection, close, outside dismissal, Escape, replacement, and disposal.
- Accepted creation uses existing edit history and click-local body placement; refusal keeps the cascade open.
- No physics source or physics test is touched.

## File Structure

- `src/app/edit.ts`: authoritative construction helper for one bound atom and its arity-derived singleton wires.
- `src/app/interact/spawn.ts`: pure eligible-binder derivation plus cascade types, DOM rows, colored circles, and hover lifecycle.
- `src/app/shell.ts`: request routing, binder color lookup, transient hover ownership, rendering overlay, and debug evidence.
- `tests/app/edit.test.ts`: construction semantics and validation.
- `tests/app/spawn.test.ts`: pure binder-option derivation and preservation of named-relation catalog behavior.
- `e2e/construction.spec.ts`: actual-app menu, swatch, hover, creation, semantic binder/arity, and undo workflow.
- `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`: completion receipt after all validation passes.

---

### Task 1: Validated bound-atom construction

**Files:**
- Modify: `src/app/edit.ts`
- Test: `tests/app/edit.test.ts`

**Interfaces:**
- Consumes: `Diagram`, `RegionId`, `NodeId`, `DiagramNode`, `Wire`, `WireId`, `requiredPorts`, `freshId`, and `mkDiagram`.
- Produces: `addAtomNode(d: Diagram, region: RegionId, binder: RegionId): { diagram: Diagram; node: NodeId }`.

- [ ] **Step 1: Write the failing semantic tests**

Add imports for `addAtomNode` and tests covering a two-argument binder and invalid ancestry:

```ts
it('adds an atom bound to an enclosing bubble with one scoped singleton wire per derived argument', () => {
  const b = new DiagramBuilder()
  const bubble = b.bubble(b.root, 2)
  const cut = b.cut(bubble)
  const d = b.build()

  const { diagram, node } = addAtomNode(d, cut, bubble)

  expect(diagram.nodes[node]).toEqual({ kind: 'atom', region: cut, binder: bubble })
  expect(Object.values(diagram.wires).filter((wire) =>
    wire.endpoints.some((endpoint) => endpoint.node === node),
  )).toEqual([
    { scope: cut, endpoints: [{ node, port: { kind: 'arg', index: 0 } }] },
    { scope: cut, endpoints: [{ node, port: { kind: 'arg', index: 1 } }] },
  ])
})

it('rejects an atom whose chosen bubble does not enclose the invocation region', () => {
  const b = new DiagramBuilder()
  const left = b.bubble(b.root, 1)
  const right = b.cut(b.root)
  const d = b.build()

  expect(() => addAtomNode(d, right, left)).toThrow(/must lie inside its binder bubble/)
})
```

- [ ] **Step 2: Run the focused test and verify RED**

Run: `npm test -- tests/app/edit.test.ts`

Expected: FAIL because `addAtomNode` is not exported.

- [ ] **Step 3: Implement the minimal validated constructor**

Add beside `addRefNode`:

```ts
export function addAtomNode(d: Diagram, region: RegionId, binder: RegionId): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const atom: DiagramNode = { kind: 'atom', region, binder }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, atom)) {
    const wire = freshId(takenWires, 'w')
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return {
    node,
    diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }),
  }
}
```

Do not pre-validate ancestry locally; `mkDiagram` remains the sole structural validator.

- [ ] **Step 4: Run the focused test and verify GREEN**

Run: `npm test -- tests/app/edit.test.ts`

Expected: all tests in `tests/app/edit.test.ts` pass.

- [ ] **Step 5: Commit the independently validated edit primitive**

```bash
git add src/app/edit.ts tests/app/edit.test.ts
git commit -m "feat: construct bound predicate atoms"
```

---

### Task 2: Derive and present contextual binder options

**Files:**
- Modify: `src/app/interact/spawn.ts`
- Test: `tests/app/spawn.test.ts`

**Interfaces:**
- Consumes: `Diagram`, `RegionId`, the existing `SpawnInvocation`, and named-relation catalog.
- Produces:
  - `SpawnBoundPredicateOption = { binder: RegionId; arity: number; position: number; total: number }`
  - `boundPredicateOptions(d: Diagram, region: RegionId): readonly SpawnBoundPredicateOption[]`
  - `SpawnBoundPredicateRequest = { binder: RegionId; invocation: SpawnInvocation }`
  - `SpawnCascadeOptions.spawnBoundPredicate(request): boolean | void`
  - `SpawnCascadeOptions.binderColor(binder): string`
  - `SpawnCascadeOptions.hoverBinder?(binder: RegionId | null): void`
  - `SpawnCascade.open(invocation, relations, boundPredicates)`

- [ ] **Step 1: Write failing pure option tests**

Add `DiagramBuilder` and `boundPredicateOptions` imports, then:

```ts
describe('bound predicate spawn options', () => {
  it('returns none outside bubbles and every enclosing bubble innermost first', () => {
    const b = new DiagramBuilder()
    const outer = b.bubble(b.root, 1)
    const cut = b.cut(outer)
    const inner = b.bubble(cut, 3)
    const leaf = b.cut(inner)
    const d = b.build()

    expect(boundPredicateOptions(d, b.root)).toEqual([])
    expect(boundPredicateOptions(d, leaf)).toEqual([
      { binder: inner, arity: 3, position: 1, total: 2 },
      { binder: outer, arity: 1, position: 2, total: 2 },
    ])
  })

  it('rejects an unknown invocation region instead of silently returning no options', () => {
    const d = new DiagramBuilder().build()
    expect(() => boundPredicateOptions(d, 'missing')).toThrow(/unknown region 'missing'/)
  })
})
```

- [ ] **Step 2: Run the focused test and verify RED**

Run: `npm test -- tests/app/spawn.test.ts`

Expected: FAIL because `boundPredicateOptions` is not exported.

- [ ] **Step 3: Implement pure ancestor-chain derivation**

Add the diagram imports, types, and helper:

```ts
export type SpawnBoundPredicateOption = {
  readonly binder: RegionId
  readonly arity: number
  readonly position: number
  readonly total: number
}

export function boundPredicateOptions(d: Diagram, region: RegionId): readonly SpawnBoundPredicateOption[] {
  const found: { binder: RegionId; arity: number }[] = []
  let current = region
  for (;;) {
    const value = d.regions[current]
    if (value === undefined) throw new Error(`unknown region '${current}'`)
    if (value.kind === 'bubble') found.push({ binder: current, arity: value.arity })
    if (value.kind === 'sheet') break
    current = value.parent
  }
  return Object.freeze(found.map((option, index) => Object.freeze({
    ...option,
    position: index + 1,
    total: found.length,
  })))
}
```

- [ ] **Step 4: Run the focused test and verify the derivation GREEN**

Run: `npm test -- tests/app/spawn.test.ts`

Expected: all existing catalog/recents tests and new binder-option tests pass.

- [ ] **Step 5: Extend the cascade contract and write the presentation before production wiring**

Add the request and callbacks:

```ts
export type SpawnBoundPredicateRequest = {
  readonly binder: RegionId
  readonly invocation: SpawnInvocation
}

// In SpawnCascadeOptions:
readonly spawnBoundPredicate: (request: SpawnBoundPredicateRequest) => boolean | void
readonly binderColor: (binder: RegionId) => string
readonly hoverBinder?: (binder: RegionId | null) => void
```

Store these callbacks in `SpawnCascade`, extend `open` with `boundPredicates: readonly SpawnBoundPredicateOption[]`, and centralize hover cleanup:

```ts
#setHoveredBinder(binder: RegionId | null): void {
  this.#hoverBinder?.(binder)
}

close(): boolean {
  this.#setHoveredBinder(null)
  // existing idempotent DOM teardown follows
}
```

Render bound entries immediately after `λ term…` and before recents/namespaces. Use a real button row with `.vpa-spawn-bound-predicate`, a child `.vpa-spawn-binder-swatch`, and these labels:

```ts
const binderLabel = (entry: SpawnBoundPredicateOption): string => entry.total === 1
  ? 'Bound predicate'
  : entry.position === 1
    ? 'Binder 1 (innermost)'
    : entry.position === entry.total
      ? `Binder ${entry.position} (outermost)`
      : `Binder ${entry.position}`
```

Set the swatch's `backgroundColor` from `this.#binderColor(entry.binder)`. On `pointerenter`, request `entry.binder`; on `pointerleave`, request `null`. On click, call `spawnBoundPredicate({ binder: entry.binder, invocation: snapshot })`; close only when the result is not `false`. Bound entries never enter `SpawnRecents` or `searchSpawnCatalog`.

- [ ] **Step 6: Update lifecycle tests for the required constructor contract**

Every test-created cascade supplies inert semantic callbacks:

```ts
const cascade = new SpawnCascade({
  host,
  spawnTerm: () => {},
  spawnRelation: () => {},
  spawnBoundPredicate: () => {},
  binderColor: () => 'rgb(1, 2, 3)',
})
```

Keep the disposed/open assertion, passing `[]` as the third `open` argument. This is a compile-time contract check; actual DOM behavior is exercised in Task 3's real-browser test.

- [ ] **Step 7: Run the focused test and type checker**

Run: `npm test -- tests/app/spawn.test.ts && npm run typecheck`

Expected: spawn tests pass; typecheck may still report the shell's old constructor/open signatures until Task 3. If so, confirm every error is confined to `src/app/shell.ts`, then continue immediately to Task 3 without claiming the repository is green.

- [ ] **Step 8: Do not commit a knowingly type-broken intermediate state**

Task 2 and Task 3 share an interface boundary. Leave these changes uncommitted until the shell consumer and browser regression are green, then commit them together in Task 3.

---

### Task 3: Wire hover, color, semantic creation, history, and actual-app evidence

**Files:**
- Modify: `src/app/shell.ts`
- Modify: `e2e/construction.spec.ts`
- Include uncommitted Task 2 files: `src/app/interact/spawn.ts`, `tests/app/spawn.test.ts`

**Interfaces:**
- Consumes: `addAtomNode`, `boundPredicateOptions`, `bubbleHues`, `highlightGroup`, and Task 2's cascade callbacks.
- Produces: one application-owned `spawnHoverBinder: RegionId | null` overlay state and an actual working bound-predicate spawn path.

- [ ] **Step 1: Write the failing actual-app test**

Extend the test's debug diagram node shape with `binder: string | null` and its rendered-region shape with `parent: string | null`. Add a focused Playwright test that:

```ts
test('spawns, identifies, highlights, and undoes a predicate bound to the enclosing bubble', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const term = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const termAt = await bodyPoint(page, term)
  await page.mouse.click(termAt.x, termAt.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('2')
  await page.getByLabel('Bubble arity').press('Enter')
  const bubble = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!)
  const openAt = await pagePoint(page, { x: bubble.x + bubble.r * 0.55, y: bubble.y })
  await page.mouse.click(openAt.x, openAt.y, { button: 'right' })

  const option = page.locator('.vpa-spawn-bound-predicate')
  await expect(option).toHaveCount(1)
  await expect(option).toContainText('Bound predicate')
  await expect(option).toContainText('/2')
  await expect(page.locator('.vpa-spawn-binder-swatch')).toHaveCSS('background-color', /rgb/)
  await option.hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(bubble.id)
  await option.click()

  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.diagram().nodes.filter((node) => node.kind === 'atom'))).toEqual([
    expect.objectContaining({ kind: 'atom', region: bubble.id, binder: bubble.id }),
  ])
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  expect((await page.evaluate(() => window.__vpaDebug!.diagram())).wires.filter((wire) => wire.scope === bubble.id && wire.endpoints === 1)).toHaveLength(3)

  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.diagram().nodes.some((node) => node.kind === 'atom'))).toBe(false)
})
```

Account for the term's existing singleton wire when asserting the bubble's scoped one-endpoint wires; exactly two additional wires belong to the atom.

- [ ] **Step 2: Run the browser test and verify RED**

Run: `npx playwright test e2e/construction.spec.ts --grep "spawns, identifies, highlights"`

Expected: FAIL because no `.vpa-spawn-bound-predicate` entry exists.

- [ ] **Step 3: Route semantic construction through the existing transaction**

Import `addAtomNode`, `boundPredicateOptions`, and ensure `bubbleHues` is imported with existing paint helpers. Add:

```ts
let spawnHoverBinder: RegionId | null = null
```

Configure the cascade:

```ts
spawnBoundPredicate: ({ binder, invocation }) => {
  try {
    const added = addAtomNode(editDiagram, invocation.region, binder)
    pushEdit(added.diagram, { node: added.node, at: invocation.world }, true)
    return true
  } catch (error) {
    refuse(error instanceof Error ? error.message : String(error), invocation.screen)
    return false
  }
},
binderColor: (binder) => bubbleHues(editDiagram, theme.bubbleLightness).get(binder)
  ?? theme.interaction.refusal,
hoverBinder: (binder) => { spawnHoverBinder = binder },
```

The color fallback is only defensive against a diagram mutation while a menu is open; accepted creation still validates the exact binder.

Open with the invocation's current semantic options:

```ts
spawnCascade.open(
  { screen: sample.client, world: sample.world, region },
  ctx.relations,
  boundPredicateOptions(editDiagram, region),
)
```

- [ ] **Step 4: Render and expose transient binder emphasis**

Before ordinary pointer hover in `frame`, add:

```ts
if (spawnHoverBinder !== null) {
  shapes.push(...highlightGroup(engine, theme, spawnHoverBinder))
} else {
  const hov = interaction.hover
  if (hov !== null) {
    const binder = hoverGroupBinder(hov)
    if (binder !== null) shapes.push(...highlightGroup(engine, theme, binder))
    else shapes.push(...itemShapes(hov, isHitSelected(interaction.selection, hov)
      ? theme.interaction.selectedHover
      : theme.interaction.hover))
  }
}
```

Extend the debug seam only with evidence already owned by the app:

```ts
spawnBinderHover(): string | null { return spawnHoverBinder },
```

Add `binder` to serialized debug nodes:

```ts
binder: node.kind === 'atom' ? node.binder : null,
```

- [ ] **Step 5: Run the browser test and verify GREEN**

Run: `npx playwright test e2e/construction.spec.ts --grep "spawns, identifies, highlights"`

Expected: 1 test passes.

- [ ] **Step 6: Add the nested-choice and cleanup browser regression**

Add a second focused case. It selects the first bubble by its rendered rim, wraps that bubble in a second one, opens inside the original inner bubble, and verifies both direct choices:

```ts
test('nested bound-predicate choices identify their bubbles by order, color, and hover', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const term = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const termAt = await bodyPoint(page, term)
  await page.mouse.click(termAt.x, termAt.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('1')
  await page.getByLabel('Bubble arity').press('Enter')
  await waitForRest(page)

  const innerBefore = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!)
  const innerRim = await pagePoint(page, { x: innerBefore.x + innerBefore.r, y: innerBefore.y })
  await page.mouse.click(innerRim.x, innerRim.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('2')
  await page.getByLabel('Bubble arity').press('Enter')
  await waitForRest(page)

  const bubbles = await page.evaluate(() => window.__vpaDebug!.regions().filter((region) => region.kind === 'bubble'))
  const inner = bubbles.find((bubble) => bubble.parent !== 'r0')!
  const outer = bubbles.find((bubble) => bubble.parent === 'r0')!
  const invoke = await pagePoint(page, { x: inner.x + inner.r * 0.55, y: inner.y })
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })

  const rows = page.locator('.vpa-spawn-bound-predicate')
  await expect(rows).toHaveCount(2)
  await expect(rows.nth(0)).toContainText('Binder 1 (innermost)')
  await expect(rows.nth(0)).toContainText('/1')
  await expect(rows.nth(1)).toContainText('Binder 2 (outermost)')
  await expect(rows.nth(1)).toContainText('/2')
  const swatches = page.locator('.vpa-spawn-binder-swatch')
  expect(await swatches.nth(0).evaluate((element) => getComputedStyle(element).backgroundColor))
    .not.toBe(await swatches.nth(1).evaluate((element) => getComputedStyle(element).backgroundColor))

  await rows.nth(0).hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(inner.id)
  await rows.nth(1).hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(outer.id)
  await page.getByLabel('Search relations to spawn').hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  await rows.nth(0).hover()
  await page.keyboard.press('Escape')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  await expect(rows).toHaveCount(0)
})
```

Keep the pure option test as the exhaustive arbitrary-depth proof.

- [ ] **Step 7: Run all affected non-physics validation**

Run:

```bash
npm test -- tests/app/edit.test.ts tests/app/spawn.test.ts tests/architecture/interaction-ownership.test.ts
npm run typecheck
npx playwright test e2e/construction.spec.ts
```

Expected: all focused Vitest files pass, typecheck exits 0, and every construction Playwright test passes. Do not run `tests/view/relax.test.ts`, `tests/view/wirephys.test.ts`, or the full physics-heavy suite.

- [ ] **Step 8: Commit the complete interaction slice**

```bash
git add src/app/interact/spawn.ts tests/app/spawn.test.ts src/app/shell.ts e2e/construction.spec.ts
git commit -m "feat: spawn bound predicates from quantifier context"
```

---

### Task 4: Close the integration receipt and verify repository conformance

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `/tmp/vpa-bound-predicate-spawn-foundation-v2-20260710.md` (scratch evidence only; never stage)

**Interfaces:**
- Consumes: fresh command output from Task 3 and the completed implementation diff.
- Produces: an accurate Task 2 completion receipt, foundation conformance evidence, and a clean committed repository.

- [ ] **Step 1: Replace the reopened marker with a factual completion receipt**

Change only the Task 2 checkbox, naming the implemented semantic option derivation, binder-colored circles, hover cleanup, atom construction, actual-app test, and exact validation commands/counts. Do not claim broader interaction integration is complete; Tasks 3–6 remain pending.

- [ ] **Step 2: Run fresh final verification before any completion claim**

Run:

```bash
git diff --check
npm test -- tests/app/edit.test.ts tests/app/spawn.test.ts tests/architecture/interaction-ownership.test.ts
npm run typecheck
npx playwright test e2e/construction.spec.ts
```

Expected: every command exits 0 with no failures.

- [ ] **Step 3: Append foundation conformance**

Append a `<conformance>` section recording semantic owners, files changed, tests executed with counts, actual-app evidence, absence of physics changes/tests, and evidence that no named-relation-only completion path remains.

- [ ] **Step 4: Commit the receipt**

```bash
git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md
git commit -m "docs: close bound predicate spawn integration"
```

- [ ] **Step 5: Verify clean state**

Run: `git status --short && git log -3 --oneline`

Expected: no status output, followed by the design, implementation, and receipt commits.
