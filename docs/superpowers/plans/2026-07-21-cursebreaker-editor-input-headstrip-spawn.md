# Cursebreaker Editor Input, Head-Strip, and Spawn Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make destructive keys context-correct, restore keyboard-only replacement head-strip, and add direct empty cut/bubble construction spawning.

**Architecture:** Active UI contexts own keyboard meaning: text controls edit, construction deletes draft objects, and puzzle input resolves proof operations. The kernel owns the sole head-strip semantics; puzzle selection authors it, while connection dragging cannot. The spawn cascade renders primitive choices and submits typed callbacks, while the construction loupe owns validated diagram mutation, history, reconciliation, and placement.

**Tech Stack:** TypeScript, Vitest, Playwright, DOM event routing, immutable diagram kernel.

## Global Constraints

- `Delete` and `Backspace` behave identically in every active context.
- Neither destructive key closes an interface; `Escape` closes.
- Head-strip matches `main` and is available only through the destructive-key puzzle route.
- Empty cut and empty quantifier bubble appear directly after `λ term…` and before bound predicates.
- Run focused tests and `npm run typecheck`; do not run `npm test` or `npm run test:physics`.

---

### Task 1: Correct Construction-Loupe Keyboard Ownership

**Files:**
- Modify: `tests/game/construction-loupe-semantics.test.ts`
- Modify: `tests/game/construction-loupe-browser.test.ts`
- Modify: `src/game/interface/construction-loupe.ts`

**Interfaces:**
- Consumes: `resolveConstructionLoupeKey(sample, editingText)` and `ConstructionLoupe.keyDown(sample, editingText)`.
- Produces: Escape-only dismissal; Delete/Backspace fall through to native text editing or `ConstructController.keyDown`.

- [ ] **Step 1: Write failing key-ownership tests**

Change the resolver assertions to:

```ts
expect(resolveConstructionLoupeKey(key({ key: 'Escape' }), false)).toBe('close')
expect(resolveConstructionLoupeKey(key({ key: 'Backspace' }), false)).toBe(null)
expect(resolveConstructionLoupeKey(key({ key: 'Delete' }), false)).toBe(null)
expect(resolveConstructionLoupeKey(key({ key: 'Backspace' }), true)).toBe(null)
expect(resolveConstructionLoupeKey(key({ key: 'Delete' }), true)).toBe(null)
```

Extend the browser lifecycle test so pressing each destructive key with no selection leaves `.cursebreaker-construction-loupe` mounted, while Escape removes it. Keep the existing text-entry Backspace assertion. For forward deletion, fill `abc`, press `Home`, then `Delete`, and assert the field contains `bc` while the loupe remains mounted.

- [ ] **Step 2: Verify the tests fail for the close bug**

Run:

```bash
npx vitest run tests/game/construction-loupe-semantics.test.ts
npx playwright test tests/game/construction-loupe-browser.test.ts --grep "keyboard lifecycle|Backspace"
```

Expected: the resolver test reports `Backspace` as `close`, and the browser lifecycle shows Backspace dismissing the loupe.

- [ ] **Step 3: Remove the competing close route**

Make the resolver and instruction copy equivalent to:

```ts
if (sample.key === 'Enter') return 'commit'
if (sample.key === 'Escape') return 'close'
return null
```

```ts
instructions.textContent = 'Enter commits. Escape closes. Control Z undoes within this construction.'
```

Preserve the text-entry guard and let non-text Delete/Backspace continue to `this.#construct.keyDown(sample)`.

- [ ] **Step 4: Verify focused keyboard behavior**

Run the two commands from Step 2. Expected: PASS with the loupe retained for both destructive keys and dismissed by Escape.

- [ ] **Step 5: Commit**

```bash
git add src/game/interface/construction-loupe.ts tests/game/construction-loupe-semantics.test.ts tests/game/construction-loupe-browser.test.ts
git commit -m "fix(game): reserve destructive keys for editing"
```

### Task 2: Restore Authoritative Head-Strip Replacement Semantics

**Files:**
- Modify: `tests/kernel/rules/headstrip.test.ts`
- Modify: `src/kernel/rules/headstrip.ts`

**Interfaces:**
- Consumes: `applyHeadStrip(diagram, a, b, correspondence, reservation?)`.
- Produces: the exact `main` implementation contract: a self-contained binary equation is replaced by nontrivial argument equations.

- [ ] **Step 1: Restore the failing `main` expectations**

Replace the branch's additive assertions with the exact tests from `main`, including:

```ts
expect(out.nodes[n1]).toBeUndefined()
expect(out.nodes[n2]).toBeUndefined()
expect(out.wires[weq]).toBeUndefined()
expect(out.wires[wa]!.endpoints).toEqual([])
```

Restore the nullary/trivial discharge tests and the extra-endpoint and external-scope refusal tests from `main`.

- [ ] **Step 2: Verify the restored tests fail against the additive implementation**

Run:

```bash
npx vitest run tests/kernel/rules/headstrip.test.ts
```

Expected: failures show the source nodes/wire surviving and missing binary/scope gates.

- [ ] **Step 3: Restore the exact `main` kernel implementation**

Apply the complete `main` version of `src/kernel/rules/headstrip.ts`. Its material replacement block is:

```ts
const nodes: Record<NodeId, DiagramNode> = {}
for (const [id, node] of Object.entries(d.nodes)) {
  if (id !== a && id !== b) nodes[id] = node
}
const wires: Record<WireId, Wire> = {}
for (const [id, wire] of Object.entries(d.wires)) {
  if (id === oa) continue
  wires[id] = {
    scope: wire.scope,
    endpoints: wire.endpoints.filter((endpoint) => endpoint.node !== a && endpoint.node !== b),
  }
}
const takenNodes = new Set(Object.keys(d.nodes))
const takenWires = new Set(Object.keys(d.wires))
```

Before decomposition, restore the two gates requiring `equation.endpoints.length === 2` and `equation.scope === region`.

- [ ] **Step 4: Verify authoritative semantics**

Run `npx vitest run tests/kernel/rules/headstrip.test.ts`. Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/headstrip.ts tests/kernel/rules/headstrip.test.ts
git commit -m "fix(kernel): restore replacement head strip"
```

### Task 3: Make Head-Strip Keyboard-Only

**Files:**
- Modify: `tests/game/game-proof-controller-routes.test.ts`
- Modify: `tests/app/moves.test.ts`
- Modify: `src/game/interface/proof-moves.ts`
- Modify: `src/interaction/proof-connection.ts`

**Interfaces:**
- Consumes: selected `Hit[]`, `proposeAttachedPortCorrespondence`, `applyStep`, and existing contextual deletion.
- Produces: `selectedHeadStripStep(diagram, hits, context): ProofStep | null`; Delete and Backspace use it identically; same-wire dragging cannot return `headStrip`.

- [ ] **Step 1: Write failing keyboard and drag tests**

Add a controller test parameterized over both keys:

```ts
it.each(['Delete', 'Backspace'])('%s head-strips a selected binary rigid-head equation', (pressed) => {
  const builder = new DiagramBuilder()
  const a = builder.termNode(builder.root, parseTerm('\\x. x'))
  const b = builder.termNode(builder.root, parseTerm('\\x. x'))
  builder.wire(builder.root, [
    { node: a, port: { kind: 'output' } },
    { node: b, port: { kind: 'output' } },
  ])
  const diagram = builder.build()
  const applied: ProofAction[] = []
  const selection = { value: [{ kind: 'node' as const, id: a }, { kind: 'node' as const, id: b }] }
  const controller = controllerFor(diagram, selection, applied, [])

  expect(controller.keyDown(key({ key: pressed }))).toBe(true)
  expect(stepsFrom(applied)).toEqual([expect.objectContaining({ rule: 'headStrip', a, b })])
})
```

Replace the connection test that expects dragged `headStrip` with a refusal assertion:

```ts
expect(() => proofConnectionStep(d, outputEnd(wire, a), outputEnd(wire, c), 'backward', 64))
  .toThrow(/no valid proof connection|compatible endpoint strand/i)
```

- [ ] **Step 2: Verify keyboard tests fail and drag still authors head-strip**

Run:

```bash
npx vitest run tests/game/game-proof-controller-routes.test.ts tests/app/moves.test.ts
```

Expected: keyboard selection falls into generic deletion, and the drag expectation fails because `headStrip` is still returned.

- [ ] **Step 3: Add one selected head-strip resolver and remove drag authorship**

Add the focused resolver:

```ts
export function selectedHeadStripStep(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): ProofStep | null {
  if (hits.length !== 2 || hits.some((hit) => hit.kind !== 'node')) return null
  const [a, b] = hits.map((hit) => hit.id)
  if (a === undefined || b === undefined
    || diagram.nodes[a]?.kind !== 'term' || diagram.nodes[b]?.kind !== 'term') return null
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

Call it at the start of the shared Delete/Backspace branch and commit it immediately when non-null. In `proofConnectionStep`, delete the same-wire output-pair `headStrip` construction. Retain only kernel-preflighted connection operations such as anchored split.

- [ ] **Step 4: Verify keyboard-only routing**

Run the command from Step 2. Expected: PASS, with both keys producing the same step and drag producing no head-strip.

- [ ] **Step 5: Commit**

```bash
git add src/game/interface/proof-moves.ts src/interaction/proof-connection.ts tests/game/game-proof-controller-routes.test.ts tests/app/moves.test.ts
git commit -m "fix(game): make head strip a destructive-key action"
```

### Task 4: Add Empty Cut and Quantifier-Bubble Spawn Choices

**Files:**
- Modify: `tests/game/construction-loupe-browser.test.ts`
- Modify: `tests/game/construction-loupe-semantics.test.ts`
- Modify: `src/game/interface/loupe/edit.ts`
- Modify: `src/game/interface/loupe/interact/spawn.ts`
- Modify: `src/game/interface/construction-loupe.ts`

**Interfaces:**
- Produces: `addEmptyCut(d, parent)` and `addEmptyBubble(d, parent, arity)` returning `{ diagram, region }`.
- Extends: `SpawnCascadeOptions` with `spawnCut(request)` and `spawnBubble({ arity, invocation })`.
- Consumes: the construction loupe's draft replacement and body placement at `anchor:<region>`.

- [ ] **Step 1: Write failing structural and browser tests**

Add semantic tests that assert:

```ts
const cut = addEmptyCut(d, d.root)
expect(cut.diagram.regions[cut.region]).toEqual({ kind: 'cut', parent: d.root })

const bubble = addEmptyBubble(d, d.root, 2)
expect(bubble.diagram.regions[bubble.region]).toEqual({ kind: 'bubble', parent: d.root, arity: 2 })
```

Add a browser test that opens the construction spawn menu and checks button order:

```ts
const rows = (await page.locator('.vpa-spawn-row').allTextContents()).map((text) => text.trim())
expect(rows.slice(0, 3)).toEqual(['λ term…', 'Empty cut', 'Empty quantifier bubble…'])
```

Click each new option, submit arity `2` for the bubble, and inspect the fixture debug diagram or exposed structural summary to prove an empty cut and empty arity-2 bubble were committed.

- [ ] **Step 2: Verify the new affordance tests fail**

Run:

```bash
npx vitest run tests/game/construction-loupe-semantics.test.ts
npx playwright test tests/game/construction-loupe-browser.test.ts --grep "spawn"
```

Expected: missing exports/menu rows and no callback behavior.

- [ ] **Step 3: Implement typed empty-region spawning**

Add validated structural primitives equivalent to:

```ts
function addEmptyRegion(
  d: Diagram,
  parent: RegionId,
  make: (parent: RegionId) => Region,
  base: string,
): { diagram: Diagram; region: RegionId } {
  if (d.regions[parent] === undefined) throw new Error(`unknown region '${parent}'`)
  const region = freshId(new Set(Object.keys(d.regions)), base)
  return {
    region,
    diagram: mkDiagram({
      root: d.root,
      regions: { ...d.regions, [region]: make(parent) },
      nodes: { ...d.nodes },
      wires: { ...d.wires },
    }),
  }
}

export function addEmptyCut(d: Diagram, parent: RegionId): { diagram: Diagram; region: RegionId } {
  return addEmptyRegion(d, parent, (owner) => ({ kind: 'cut', parent: owner }), 'cut')
}

export function addEmptyBubble(d: Diagram, parent: RegionId, arity: number): { diagram: Diagram; region: RegionId } {
  if (!Number.isInteger(arity) || arity < 0) throw new Error(`'${arity}' is not a valid arity`)
  return addEmptyRegion(d, parent, (owner) => ({ kind: 'bubble', parent: owner, arity }), 'bub')
}
```

Extend the cascade's tree in exact order:

```ts
const nodes: HTMLElement[] = [
  row('λ term…', '', enterTermMode),
  row('Empty cut', '', pickEmptyCut),
  row('Empty quantifier bubble…', '', enterBubbleMode),
]
```

Bubble mode reuses the focused search field as a number entry, accepts only a nonnegative integer on Enter, and calls `spawnBubble`. Backspace/Delete remain native because the field's key handler stops propagation and handles only Escape/Enter.

In `ConstructionLoupe`, wire callbacks through `replaceComprehensionDiagram` and reconcile the new leaf anchor at the invocation point:

```ts
spawnCut: ({ invocation: at }) => this.#editRegion(
  () => addEmptyCut(this.#diagram(), at.region), at.world,
),
spawnBubble: ({ arity, invocation: at }) => this.#editRegion(
  () => addEmptyBubble(this.#diagram(), at.region, arity), at.world,
),
```

- [ ] **Step 4: Verify spawn behavior**

Run the commands from Step 2. Expected: PASS with exact ordering, validated arity, empty regions, and retained text editing.

- [ ] **Step 5: Commit**

```bash
git add src/game/interface/loupe/edit.ts src/game/interface/loupe/interact/spawn.ts src/game/interface/construction-loupe.ts tests/game/construction-loupe-semantics.test.ts tests/game/construction-loupe-browser.test.ts
git commit -m "feat(game): spawn empty construction boundaries"
```

### Task 5: Focused Integration Verification

**Files:**
- Modify only if a focused validation exposes an in-scope defect.

**Interfaces:**
- Verifies the integrated input, kernel, proof-routing, spawn, and type contracts.

- [ ] **Step 1: Run the focused unit battery**

```bash
npx vitest run tests/kernel/rules/headstrip.test.ts tests/kernel/proof/step.test.ts tests/game/construction-loupe-semantics.test.ts tests/game/game-proof-controller-routes.test.ts tests/app/moves.test.ts
```

Expected: PASS.

- [ ] **Step 2: Run the focused browser battery**

```bash
npx playwright test tests/game/construction-loupe-browser.test.ts
```

Expected: PASS.

- [ ] **Step 3: Run type checking**

```bash
npm run typecheck
```

Expected: exit 0 with no TypeScript diagnostics.

- [ ] **Step 4: Confirm displaced paths are absent**

```bash
rg -n "Backspace.*close|Escape or Backspace closes|rule: 'headStrip'" src/game/interface/construction-loupe.ts src/interaction/proof-connection.ts tests/app/moves.test.ts
```

Expected: no Backspace close text and no drag-based `headStrip` construction or expectation.

- [ ] **Step 5: Record conformance and inspect the final diff**

Append the executed evidence to `/tmp/vpa-foundation-20260721-cursebreaker-editor-input-headstrip-spawn-04.md`, then run:

```bash
git status --short
git diff --check
git log -6 --oneline --decorate
```

Expected: only intentional changes, no whitespace errors, and focused commits on `game/cursebreaker`.
