# Headstrip Selection and Shared Context Menu Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make headstrip insensitive to selection of its own equation wire and give every game right-click menu the existing dark proof-menu appearance through one style authority.

**Architecture:** Normalize headstrip input at the proof-controller boundary, accepting two term nodes plus at most their one shared output wire before the kernel preflight remains authoritative. Replace component-owned menu palettes with a shared `context-menu.css` class family; proof and construction code retain only their different positioning and cascade structures.

**Tech Stack:** TypeScript, DOM/CSS, Vitest, Playwright browser fixtures, Vite

## Global Constraints

- Delete and Backspace use exactly the same headstrip recognition path.
- Headstrip accepts exactly two distinct term nodes, optionally accompanied only by their unique shared output wire.
- Any additional node, region, unrelated wire, or second wire prevents headstrip recognition.
- The proof kernel still validates every proposed headstrip step.
- The current dark proof-action menu is the sole visual source for game right-click menus.
- Do not retain the white construction palette, JavaScript hover-color mutations, or private proof-menu style classes.
- Run only focused controller, browser, source, and typecheck validation; do not run the physics suite.

---

### Task 1: Normalize Headstrip Selection

**Files:**
- Modify: `tests/game/game-proof-controller-routes.test.ts`
- Modify: `src/game/interface/proof-moves.ts`

**Interfaces:**
- Consumes: `selectedHeadStripStep(diagram: Diagram, hits: readonly Hit[], context: ProofContext): ProofStep | null`
- Produces: the same function signature with selection normalization before the existing kernel preflight

- [ ] **Step 1: Write failing controller and rejection tests**

Keep the existing two-node Delete/Backspace regression. Add a second parameterized controller test using the shared equation wire, and directly prove that an unrelated selected wire is not absorbed:

```ts
import {
  GameProofMoveController,
  selectedHeadStripStep,
  vacuousEliminationChainSteps,
  type GameProofActionInput,
} from '../../src/game/interface/proof-moves'

it.each(['Delete', 'Backspace'])('%s head-strips when the selected equation includes its wire', (pressed) => {
  const builder = new DiagramBuilder()
  const a = builder.termNode(builder.root, parseTerm('\\x. x'))
  const b = builder.termNode(builder.root, parseTerm('\\x. x'))
  const equation = builder.wire(builder.root, [
    { node: a, port: { kind: 'output' } },
    { node: b, port: { kind: 'output' } },
  ])
  const diagram = builder.build()
  const applied: ProofAction[] = []
  const selection = { value: [
    { kind: 'node' as const, id: a },
    { kind: 'wire' as const, id: equation },
    { kind: 'node' as const, id: b },
  ] }
  const controller = controllerFor(diagram, selection, applied, [])

  expect(controller.keyDown(key({ key: pressed }))).toBe(true)
  expect(stepsFrom(applied)).toEqual([{
    rule: 'headStrip', a, b,
    correspondence: { commonArity: 0, left: {}, right: {} },
  }])
})

it('does not treat an unrelated selected wire as part of headstrip', () => {
  const builder = new DiagramBuilder()
  const a = builder.termNode(builder.root, parseTerm('\\x. x'))
  const b = builder.termNode(builder.root, parseTerm('\\x. x'))
  builder.wire(builder.root, [
    { node: a, port: { kind: 'output' } },
    { node: b, port: { kind: 'output' } },
  ])
  const c = builder.termNode(builder.root, parseTerm('\\x. x'))
  const d = builder.termNode(builder.root, parseTerm('\\x. x'))
  const unrelated = builder.wire(builder.root, [
    { node: c, port: { kind: 'output' } },
    { node: d, port: { kind: 'output' } },
  ])
  const diagram = builder.build()

  expect(selectedHeadStripStep(diagram, [
    { kind: 'node', id: a },
    { kind: 'node', id: b },
    { kind: 'wire', id: unrelated },
  ], EMPTY_PROOF_CONTEXT)).toBeNull()
})
```

- [ ] **Step 2: Run the focused controller suite and verify RED**

Run: `npx vitest run tests/game/game-proof-controller-routes.test.ts`

Expected: the two shared-wire cases fail because `selectedHeadStripStep` currently requires exactly two node hits; the unrelated-wire rejection remains green.

- [ ] **Step 3: Implement semantic selection normalization**

Import `wireAt`, partition the hits, reject every non-node/non-wire shape and every count outside exactly two nodes plus zero or one wire, require distinct term nodes, and accept the optional wire only when it is the output wire of both nodes:

```ts
import { termNodeAt, wireAt } from '../../kernel/rules/access'

export function selectedHeadStripStep(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): ProofStep | null {
  const nodes = hits.filter((hit): hit is Extract<Hit, { kind: 'node' }> => hit.kind === 'node')
  const wires = hits.filter((hit): hit is Extract<Hit, { kind: 'wire' }> => hit.kind === 'wire')
  if (nodes.length !== 2 || wires.length > 1 || nodes.length + wires.length !== hits.length) return null
  const [a, b] = nodes.map((hit) => hit.id)
  if (a === undefined || b === undefined || a === b
    || diagram.nodes[a]?.kind !== 'term' || diagram.nodes[b]?.kind !== 'term') return null
  if (wires.length === 1) {
    const selectedWire = wires[0]!.id
    if (wireAt(diagram, a, { kind: 'output' }) !== selectedWire
      || wireAt(diagram, b, { kind: 'output' }) !== selectedWire) return null
  }
  const step: ProofStep = {
    rule: 'headStrip', a, b,
    correspondence: proposeAttachedPortCorrespondence(diagram, a, b),
  }
  try {
    applyStep(diagram, step, context, 'backward')
    return step
  } catch {
    return null
  }
}
```

- [ ] **Step 4: Run the focused controller suite and verify GREEN**

Run: `npx vitest run tests/game/game-proof-controller-routes.test.ts`

Expected: all controller-route tests pass for both two-node and node-plus-wire selections.

- [ ] **Step 5: Commit the headstrip behavior**

```bash
git add tests/game/game-proof-controller-routes.test.ts src/game/interface/proof-moves.ts
git commit -m "fix: accept selected equation wire for headstrip"
```

---

### Task 2: Replace Competing Context Menu Palettes

**Files:**
- Create: `src/game/interface/context-menu.css`
- Create: `tests/game/context-menu-source.test.ts`
- Modify: `src/game/interface/proof-moves.ts`
- Modify: `src/game/interface/proof-surface.css`
- Modify: `src/game/interface/construction-loupe.ts`
- Modify: `src/game/interface/loupe/interact/spawn.ts`
- Modify: `tests/game/game-proof-controller-routes.test.ts`
- Modify: `tests/game/construction-loupe-browser.test.ts`
- Modify: `tests/game/game-proof-surface-browser.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`

**Interfaces:**
- Produces: `.curse-context-menu`, `.curse-context-menu__heading`, `.curse-context-menu__action`, `.curse-context-menu__meta`, and `.curse-context-menu__input` as the sole game context-menu visual classes
- Consumes: existing `vpa-spawn-*` classes only as construction-cascade structure and test hooks

- [ ] **Step 1: Write failing shared-authority and rendered-palette tests**

Add `tests/game/context-menu-source.test.ts` to require both menu implementations to use the shared class family and reject displaced palettes:

```ts
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'

const source = (path: string): string => readFileSync(resolve(path), 'utf8')

describe('game context-menu style authority', () => {
  it('uses one semantic class family without private proof or inline construction palettes', () => {
    const proof = source('src/game/interface/proof-moves.ts')
    const spawn = source('src/game/interface/loupe/interact/spawn.ts')
    const proofCss = source('src/game/interface/proof-surface.css')

    expect(proof).toContain('curse-context-menu')
    expect(spawn).toContain('curse-context-menu')
    expect(proof).not.toMatch(/curse-proof-menu/)
    expect(proofCss).not.toMatch(/curse-proof-menu/)
    expect(spawn).not.toMatch(/#fff|#fef3c7|#d97706|#a8a29e|#78716c/)
    expect(spawn).not.toMatch(/style\.background\s*=/)
  })
})
```

Extend the construction browser lifecycle test after opening the cascade:

```ts
const palette = await page.locator('.vpa-spawn-column').evaluate((node) => {
  const style = getComputedStyle(node)
  return {
    backgroundColor: style.backgroundColor,
    borderTopColor: style.borderTopColor,
    color: style.color,
  }
})
expect(palette).toEqual({
  backgroundColor: 'rgba(7, 18, 30, 0.933)',
  borderTopColor: 'rgb(89, 217, 255)',
  color: 'rgb(234, 250, 255)',
})
```

Add a rendered comparison to `game-proof-surface-browser.test.ts` that opens an
actual proof-action menu, records its palette, opens the construction loupe and
its spawn cascade, then compares the construction panel to the recorded proof
palette:

```ts
it('uses the proof-action palette for the construction context menu', async () => {
  const page = await openFixture()
  try {
    const proofPoint = await page.evaluate(() => window.__gameProofSurfaceFixture.proofNodePoint())
    await page.mouse.click(proofPoint.x, proofPoint.y, { button: 'right' })
    const proofMenu = page.locator('.curse-context-menu--proof')
    await expect.poll(() => proofMenu.count()).toBe(1)
    const proofPalette = await proofMenu.evaluate((node) => {
      const style = getComputedStyle(node)
      return {
        backgroundColor: style.backgroundColor,
        borderTopColor: style.borderTopColor,
        color: style.color,
        boxShadow: style.boxShadow,
      }
    })

    expect(await page.evaluate(() => window.__gameProofSurfaceFixture.open())).toBe(true)
    await page.locator('.cursebreaker-construction-loupe__canvas')
      .click({ button: 'right', position: { x: 210, y: 210 } })
    const constructionMenu = page.locator('.vpa-spawn-column')
    await expect.poll(() => constructionMenu.count()).toBe(1)
    const constructionPalette = await constructionMenu.evaluate((node) => {
      const style = getComputedStyle(node)
      return {
        backgroundColor: style.backgroundColor,
        borderTopColor: style.borderTopColor,
        color: style.color,
        boxShadow: style.boxShadow,
      }
    })
    expect(constructionPalette).toEqual(proofPalette)
  } finally { await page.close() }
})
```

Update the fake-DOM helper selector from `.curse-proof-menu__action` to `.curse-context-menu__action`; this intentionally remains red until the proof DOM migrates.

Update the authoritative runtime's proof-menu locator from `.curse-proof-menu`
to `.curse-context-menu--proof`, then run its one editor lifecycle case to prove
the migrated selector still reaches the production menu:

Run: `npx vitest run tests/game/authoritative-runtime-browser.test.ts -t "opens the actual editor"`

Expected before selector migration: FAIL waiting for `.curse-proof-menu`.
Expected after selector migration: the selected editor lifecycle test passes.

- [ ] **Step 2: Run focused style tests and verify RED**

Run: `npx vitest run tests/game/context-menu-source.test.ts tests/game/game-proof-controller-routes.test.ts tests/game/construction-loupe-browser.test.ts tests/game/game-proof-surface-browser.test.ts`

Expected: source authority assertions, the migrated fake-DOM selector, and the dark construction palette assertion fail against the two incumbent menu styles.

- [ ] **Step 3: Create the shared stylesheet**

Create `src/game/interface/context-menu.css` with the proof menu's approved palette and all shared element styling, plus only the structural rules required for proof positioning and construction cascade layout:

```css
.curse-context-menu {
  overflow: hidden;
  border: 1.5px solid #59d9ff;
  border-radius: 0.5rem;
  background: #07121eee;
  box-shadow: 0 0.25rem 1rem #0008;
  color: #eafaff;
  font: 13px system-ui, sans-serif;
}

.curse-context-menu--proof {
  position: fixed;
  z-index: 61;
  top: var(--curse-context-menu-top);
  left: var(--curse-context-menu-left);
  width: 17rem;
  max-height: 24rem;
  overflow-y: auto;
}

.curse-context-menu__heading,
.curse-context-menu__action {
  display: flex;
  width: 100%;
  box-sizing: border-box;
  justify-content: space-between;
  gap: 0.375rem;
  padding: 0.375rem 0.625rem;
  border: 0;
  background: transparent;
  color: inherit;
  text-align: left;
  font: inherit;
}

.curse-context-menu__heading {
  color: #8edff5;
  font-size: 0.76923077em;
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

.curse-context-menu__action { cursor: pointer; }
.curse-context-menu__action:hover,
.curse-context-menu__action:focus-visible { background: #64dfff22; }
.curse-context-menu__meta { color: #8edff5; }

.curse-context-menu__input {
  width: 100%;
  box-sizing: border-box;
  padding: 0.4375rem 0.625rem;
  border: 0;
  border-bottom: 1px solid #47788a;
  outline: 0;
  background: #0d1d2a;
  color: #effcff;
  font: inherit;
}

.vpa-spawn-cascade {
  position: fixed;
  z-index: 71;
  display: flex;
  align-items: flex-start;
  font: 13px system-ui, sans-serif;
}
.vpa-spawn-backdrop { position: fixed; inset: 0; z-index: 70; background: transparent; }
.vpa-spawn-column { width: 220px; }
.vpa-spawn-listing { max-height: 270px; overflow-y: auto; }
.vpa-spawn-submenu {
  display: none;
  width: 190px;
  max-height: 300px;
  margin-left: 2px;
  overflow-y: auto;
}
```

- [ ] **Step 4: Migrate both menu DOM implementations**

Import `context-menu.css` from `proof-moves.ts` and `construction-loupe.ts`. In `proof-moves.ts`, replace the private class family and variables:

```ts
menu.className = 'curse-context-menu curse-context-menu--proof'
menu.style.setProperty('--curse-context-menu-left', `${sample.client.x + 10}px`)
menu.style.setProperty('--curse-context-menu-top', `${sample.client.y + 10}px`)
element.className = run === null ? 'curse-context-menu__heading' : 'curse-context-menu__action'
```

In `spawn.ts`, keep only runtime coordinates and binder swatch color inline. Apply `curse-context-menu` to both panels, `curse-context-menu__input` to the search control, `curse-context-menu__action` to interactive rows, `curse-context-menu__heading` to headings, and `curse-context-menu__meta` to hints. Remove the white/amber/stone declarations and color-changing pointer listeners. Namespace rows receive the action class even though hovering opens their submenu.

Delete the `.curse-proof-menu*` blocks from `proof-surface.css`; prompt styling remains unchanged.

- [ ] **Step 5: Run focused style tests and verify GREEN**

Run: `npx vitest run tests/game/context-menu-source.test.ts tests/game/game-proof-controller-routes.test.ts tests/game/construction-loupe-browser.test.ts tests/game/game-proof-surface-browser.test.ts`

Expected: all selected suites pass and the construction panel reports the proof menu's dark computed palette.

- [ ] **Step 6: Commit the shared style authority**

```bash
git add src/game/interface/context-menu.css src/game/interface/proof-moves.ts src/game/interface/proof-surface.css src/game/interface/construction-loupe.ts src/game/interface/loupe/interact/spawn.ts tests/game/context-menu-source.test.ts tests/game/game-proof-controller-routes.test.ts tests/game/construction-loupe-browser.test.ts tests/game/game-proof-surface-browser.test.ts tests/game/authoritative-runtime-browser.test.ts docs/superpowers/plans/2026-07-21-headstrip-selection-context-menu.md
git commit -m "fix: unify game context menu styling"
```

---

### Task 3: Focused Conformance Verification

**Files:**
- Modify: `/tmp/vpa-foundation-20260721-cursebreaker-headstrip-selection-context-menu-06.md`

**Interfaces:**
- Consumes: the completed headstrip recognizer and shared menu stylesheet
- Produces: fresh test evidence and the required foundation-record conformance receipt

- [ ] **Step 1: Run all directly affected tests together**

Run: `npx vitest run tests/game/game-proof-controller-routes.test.ts tests/game/context-menu-source.test.ts tests/game/construction-loupe-browser.test.ts tests/game/game-proof-surface-browser.test.ts`

Expected: all selected test files and tests pass with zero failures.

- [ ] **Step 2: Run the TypeScript authority**

Run: `npm run typecheck`

Expected: exit code 0 with no TypeScript errors.

- [ ] **Step 3: Audit the displaced models and patch quality**

Run: `rg -n "curse-proof-menu|#fff|#fef3c7|#d97706|#a8a29e|#78716c|style\\.background" src/game/interface/proof-moves.ts src/game/interface/proof-surface.css src/game/interface/loupe/interact/spawn.ts`

Expected: no matches.

Run: `git diff --check HEAD~2..HEAD`

Expected: no whitespace errors.

- [ ] **Step 4: Append the conformance receipt**

Append a `<conformance>` section to `/tmp/vpa-foundation-20260721-cursebreaker-headstrip-selection-context-menu-06.md` recording the normalized headstrip owner, the shared stylesheet owner, deleted palettes/classes, migrated consumers, exact focused validation output, and the source-audit evidence that the displaced models no longer remain.

- [ ] **Step 5: Push the branch**

Run: `git push origin game/cursebreaker`

Expected: `origin/game/cursebreaker` advances to the final local commit. Do not merge to `main`.
