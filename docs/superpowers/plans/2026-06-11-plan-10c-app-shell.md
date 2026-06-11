# Plan 10c: App Shell and Interactions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The interactive application: construct diagrams in EDIT mode (formula entry with `\`-as-λ, select-then-button cuts/bubbles, port wiring), prove in PROVE mode (polarity-aware rule menu over the current selection, theorem citation from the bundled theories, bidirectional forward/backward sessions meeting in the middle), rendered live through the Plan 9 view layer with always-settling physics and pin-while-drag.

**Architecture:** A new `src/app/` layer that may import everything below it (kernel, theories, view) while nothing imports it (layering edges added). The heart is HEADLESS and fully tested: `edit.ts` (construction-mode diagram surgery — not rules; validated by mkDiagram), `session.ts` (the proof state machine: goal, forward chain, backward tail recorded as forward-valid steps, fingerprint meet detection, `composeProofs` at the meet, undo), `hittest.ts` (pure point-vs-scene resolution), `actions.ts` (pure enumeration of applicable moves for a selection, gates mirrored without invoking appliers). The DOM shell (`shell.ts` + `app/` page) is thin glue over those four modules plus the view layer — build-verified in this plan, E2E-tested in Plan 10d.

**Tech Stack:** TypeScript strict, Vitest, vite (already a devDependency), Canvas 2D. Zero runtime deps preserved.

---

## Design decisions (read before implementing)

**Edit mode vs prove mode.** Constructing a statement is not proving: EDIT operations are arbitrary diagram surgery (add a term node from parsed text, wrap a selection in a single cut or a bubble, join two ports onto one wire, delete a selection) validated only by `mkDiagram` — they build the lhs/rhs of a goal. PROVE operations are exclusively kernel rules recorded as `ProofStep`s. The session enforces the phase: once proving starts, the diagrams change only through steps.

**The session is the proof object under construction.** `ProofSession` holds the goal (`lhs`/`rhs` as `DiagramWithBoundary`), the forward state (current diagram + steps from lhs) and the backward state (current diagram + steps recorded as the FORWARD steps they invert, in user order — step i transforms backward-diagram i to backward-diagram i−1). Applying forward = `applyStep` + push. Applying backward = compute the inverse-applied diagram G′ AND the forward step (G′ → G) together, per supported rule pair (double cut intro↔elim, vacuous bubble intro↔elim, insertion↔erasure at the appropriate polarities, conversion↔conversion). After every change, meet detection compares `diagramFingerprint(forward.current)` against `backward.current`; on meet, `composeProofs(forward.current, backward.current, reversed backward steps)` produces the full chain, and `checkTheorem` on the assembled theorem is the final word. Undo pops the respective history (full diagrams retained — proof diagrams are small; no deltas, no cleverness).

**Backward step construction must reproduce the exact prior diagram.** Each backward action computes G′ from G with known fresh ids, then builds the forward step against G′ such that `applyStep(G′, step)` is id-exactly G — asserted at construction time (loud failure if an applier's id choices drift). This keeps the recorded tail replayable without iso-rewriting anywhere except the meet itself, where Plan 8's `composeProofs` already handles it.

**Actions are enumerated, not attempted.** `applicableActions(d, sel, ctx)` mirrors the rule gates read-only (polarity checks, shape checks) and returns descriptors `{ kind, label, needsTarget?, needsInput? }`; the UI renders them as the floating menu. Two-phase actions (iteration's target, theorem citation's argument wires) get a pending state in the shell, not in the session. Enumeration NEVER invokes appliers (no speculative application); the applier remains the sole authority when the user commits — a refused action at commit time is surfaced verbatim (the kernel's message IS the UX copy).

**Hit testing and selection.** `hitTest(scene, point)` resolves the topmost item: the smallest region circle containing the point, refined to a node when within its `outerRadius`, refined to a wire when within `WIRE_TOLERANCE` of a spoke segment (a documented UI tolerance — visual only, like REGION_PADDING). Click toggles items into a growing selection; `buildSelection(d, items)` derives the anchor (the deepest region containing every item directly — direct nodes of the anchor plus child subtree roots; anything else is a loud refusal explaining what to select instead) and validates via `mkSelection`.

**Physics integration.** The shell owns one `PhysicsState` per displayed diagram, re-seeded via `initialState` whenever the diagram identity changes (layout never persists — structural, per Plan 9). Pin-while-drag: the dragged node's position is overwritten after each `step()` with the pointer position and its velocity zeroed — physics settles everything else around it; on release the pin lifts.

**The shell.** One canvas, floating chrome in DOM: mode toggle (edit/prove), the action menu (enumerated), a text input for term entry (`\` read as λ, parsed with the theory's constant names), a theorem list (from the loaded bundled theories) for citation, goal status line (fingerprints met / steps counts), undo. Browser glue only — every branch it takes calls a tested headless function. `app/index.html` + `app/main.ts` become the vite root (the Plan 9 `demo/` stays as the bare view-layer demo); `"app": "vite app"` script.

**File map:**
- Create: `src/app/edit.ts`, `src/app/session.ts`, `src/app/hittest.ts`, `src/app/actions.ts`, `src/app/shell.ts`, `src/app/index.ts`
- Create: `app/index.html`, `app/main.ts`
- Modify: `package.json` (app script), `tests/architecture/layering.test.ts` (app edges)
- Tests: `tests/app/{edit,session,hittest,actions}.test.ts`

---

### Task 1: Edit operations

**Files:**
- Create: `src/app/edit.ts`
- Test: `tests/app/edit.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/app/edit.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import {
  addTermNode, addCut, addBubble, joinPorts, deleteSelection, emptyDiagram,
} from '../../src/app/edit'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('edit operations (construction mode, mkDiagram-validated surgery)', () => {
  it('starts from the empty sheet and adds parsed term nodes with auto wires', () => {
    const d0 = emptyDiagram()
    expect(Object.keys(d0.nodes)).toHaveLength(0)
    const { diagram: d1, node } = addTermNode(d0, d0.root, p('\\x. x y'))
    expect(d1.nodes[node]?.kind).toBe('term')
    // output + y singleton wires materialized
    const touching = Object.values(d1.wires).filter((w) => w.endpoints.some((ep) => ep.node === node))
    expect(touching).toHaveLength(2)
  })

  it('wraps a selection in a single cut and in a bubble', () => {
    const d0 = emptyDiagram()
    const { diagram: d1, node } = addTermNode(d0, d0.root, p('y'))
    const sel = mkSelection(d1, { region: d1.root, regions: [], nodes: [node], wires: [] })
    const { diagram: d2, region: cut } = addCut(d1, sel)
    expect(d2.regions[cut]?.kind).toBe('cut')
    expect(d2.nodes[node]?.region).toBe(cut)
    const sel2 = mkSelection(d2, { region: d2.root, regions: [cut], nodes: [], wires: [] })
    const { diagram: d3, region: bub } = addBubble(d2, sel2, 2)
    expect(d3.regions[bub]?.kind).toBe('bubble')
    expect((d3.regions[cut] as { parent: string }).parent).toBe(bub)
  })

  it('joins two ports onto one wire (construction-level identification)', () => {
    const d0 = emptyDiagram()
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    const b = addTermNode(a.diagram, a.diagram.root, p('y'))
    const d = b.diagram
    const out = joinPorts(d,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 'y' } })
    const shared = Object.values(out.wires).find((w) =>
      w.endpoints.some((ep) => ep.node === a.node) && w.endpoints.some((ep) => ep.node === b.node))
    expect(shared).toBeDefined()
    expect(shared!.endpoints).toHaveLength(2)
  })

  it('joinPorts merges the wires at their deepest common scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(h.root, p('y'))
    const d = h.build()
    const out = joinPorts(d,
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } })
    const shared = Object.values(out.wires).find((w) => w.endpoints.length === 2)!
    expect(shared.scope).toBe(d.root)
  })

  it('deletes a selection, trimming touching wires', () => {
    const d0 = emptyDiagram()
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    const b = addTermNode(a.diagram, a.diagram.root, p('y'))
    const joined = joinPorts(b.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 'y' } })
    const sel = mkSelection(joined, { region: joined.root, regions: [], nodes: [b.node], wires: [] })
    const out = deleteSelection(joined, sel)
    expect(out.nodes[b.node]).toBeUndefined()
    expect(out.nodes[a.node]).toBeDefined()
  })

  it('refuses joining a port to itself, loudly', () => {
    const d0 = emptyDiagram()
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    expect(() => joinPorts(a.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: a.node, port: { kind: 'output' } })).toThrowError(/same port/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/app/edit.test.ts`
Expected: FAIL — cannot resolve `app/edit`.

- [ ] **Step 3: Implement**

`src/app/edit.ts`:

```ts
import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'
import type { Diagram, DiagramNode, Endpoint, NodeId, Port, Region, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { mkDiagram, portKey } from '../kernel/diagram/diagram'
import { isAncestorOrEqual } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { removeSubgraph } from '../kernel/diagram/subgraph/splice'
import { freshId } from '../kernel/diagram/subgraph/freshId'

/**
 * Construction-mode surgery. These are NOT rules: they build statements
 * before proving starts, and their only obligation is structural validity
 * (every result passes mkDiagram). The session refuses them once a proof is
 * underway.
 */

export function emptyDiagram(): Diagram {
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
}

export function addTermNode(d: Diagram, region: RegionId, term: Term): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: { kind: 'term', region, term } }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  const ports: Port[] = [{ kind: 'output' }, ...freePorts(term).map((name): Port => ({ kind: 'freeVar', name }))]
  for (const port of ports) {
    const w = freshId(takenWires, 'w')
    takenWires.add(w)
    wires[w] = { scope: region, endpoints: [{ node, port }] }
  }
  return { diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }), node }
}

function wrap(d: Diagram, sel: SubgraphSelection, make: (parent: RegionId) => Region, base: string): { diagram: Diagram; region: RegionId } {
  const region = freshId(new Set(Object.keys(d.regions)), base)
  const regions: Record<RegionId, Region> = { ...d.regions, [region]: make(sel.region) }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut' ? { kind: 'cut', parent: region } : { kind: 'bubble', parent: region, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = n.kind === 'term'
        ? { kind: 'term', region, term: n.term }
        : { kind: 'atom', region, binder: n.binder }
    }
  }
  return { diagram: mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } }), region }
}

/** Wrap a selection in a SINGLE cut (construction only — proofs use double-cut intro). */
export function addCut(d: Diagram, sel: SubgraphSelection): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'cut', parent }), 'cut')
}

export function addBubble(d: Diagram, sel: SubgraphSelection, arity: number): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'bubble', parent, arity }), 'bub')
}

/**
 * Identify two individuals: merge the wires holding the two ports into one,
 * scoped at the deepest common scope of the originals (construction-level —
 * the rule-gated counterpart is applyWireJoin).
 */
export function joinPorts(d: Diagram, a: Endpoint, b: Endpoint): Diagram {
  if (a.node === b.node && portKey(a.port) === portKey(b.port)) {
    throw new Error('cannot join a port to the same port')
  }
  const holder = (ep: Endpoint): WireId => {
    const found = Object.entries(d.wires).find(([, w]) =>
      w.endpoints.some((x) => x.node === ep.node && portKey(x.port) === portKey(ep.port)))
    if (found === undefined) throw new Error(`no wire holds port '${portKey(ep.port)}' of node '${ep.node}'`)
    return found[0]
  }
  const wa = holder(a)
  const wb = holder(b)
  if (wa === wb) return d
  const sa = d.wires[wa]!.scope
  const sb = d.wires[wb]!.scope
  const scope = isAncestorOrEqual(d, sa, sb) ? sa
    : isAncestorOrEqual(d, sb, sa) ? sb
    : d.root
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === wb) continue
    wires[id] = id === wa
      ? { scope, endpoints: [...d.wires[wa]!.endpoints, ...d.wires[wb]!.endpoints] }
      : w
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}

export function deleteSelection(d: Diagram, sel: SubgraphSelection): Diagram {
  return removeSubgraph(d, sel)
}
```

NOTE: `joinPorts` falling back to `d.root` for incomparable scopes is correct construction semantics (the merged line's quantifier must enclose both ends; the root always does). The deepest common ANCESTOR would be tighter — acceptable simplification for construction mode, documented here; tighten in 10d if statement-authoring ever cares.

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/app/edit.ts tests/app/edit.test.ts
git commit -m "feat(app): construction-mode edit operations"
```

---

### Task 2: The proof session (forward + goal)

**Files:**
- Create: `src/app/session.ts`
- Test: `tests/app/session.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/app/session.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem } from '../../src/app/session'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)

function goalPair() {
  // goal: o = PLUS ONE ONE node ⟹ same node double-cut-wrapped (a toy goal)
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('\\x. x'))
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [])
  const r = new DiagramBuilder()
  const m = r.termNode(r.root, p('\\x. x'))
  const c1 = r.cut(r.root)
  r.cut(c1)
  void m
  const rhs = mkDiagramWithBoundary(r.build(), [])
  return { lhs, rhs, n }
}

describe('proof session', () => {
  it('starts at the goal ends and applies forward steps through the kernel', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    expect(s0.forward.steps).toHaveLength(0)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s0.forward.current, { region: s0.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    expect(s1.forward.steps).toHaveLength(1)
    expect(Object.keys(s1.forward.current.regions).length).toBe(3)
  })

  it('meets when forward reaches the rhs and assembles a checkable theorem', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    expect(meet(s)).toBe(false)
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy')
    expect(thm.steps.length).toBeGreaterThan(0)
    expect(thm.name).toBe('toy')
  })

  it('forward refusals surface the kernel message and leave the session unchanged', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs, n } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    expect(() => applyForward(s0, {
      rule: 'insertion',
      region: s0.forward.current.root,
      pattern: lhs, attachments: [], binders: {},
    })).toThrowError(/insertion requires a negative region/)
    expect(s0.forward.steps).toHaveLength(0)
    void n
  })

  it('undo pops exactly one step and restores the prior diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s0.forward.current, { region: s0.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    const s2 = undoForward(s1)
    expect(s2.forward.steps).toHaveLength(0)
    expect(s2.forward.current).toBe(s0.forward.current)
    expect(() => undoForward(s2)).toThrowError(/nothing to undo/)
  })

  it('cites bundled theorems as single steps', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, p('ZERO'))
    const wz = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const start = mkDiagramWithBoundary(h.build(), [wz])
    const target = start // rhs irrelevant for this check
    let s = startSession(start, target, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
      at: { sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [nz], wires: [] }), args: [wz] },
    })
    expect(Object.values(s.forward.current.regions).some((r) => r.kind === 'bubble')).toBe(true)
  })
})

describe('backward mode', () => {
  it('un-wraps a double cut backward, recording the forward intro step', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    // the goal has the node + an empty double cut: backward double-cut ELIM
    // is the inverse of forward INTRO... no: backward we REMOVE structure the
    // forward direction would ADD. Removing the goal's double cut backward
    // records the forward doubleCutIntro that re-creates it.
    const outer = Object.entries(s.backward.current.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === s.backward.current.root,
    )![0]
    s = applyBackward(s, { kind: 'unDoubleCut', outer })
    expect(s.backward.steps).toHaveLength(1)
    expect(s.backward.steps[0]!.rule).toBe('doubleCutIntro')
    expect(Object.keys(s.backward.current.regions)).toHaveLength(1)
    // and now the two sides meet: lhs ≅ unwrapped rhs
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy2')
    expect(thm.steps).toHaveLength(1)
  })

  it('backward undo restores the prior goal diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    const outer = Object.entries(s.backward.current.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === s.backward.current.root,
    )![0]
    const before = s.backward.current
    s = applyBackward(s, { kind: 'unDoubleCut', outer })
    s = undoBackward(s)
    expect(s.backward.current).toBe(before)
    expect(s.backward.steps).toHaveLength(0)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/app/session.test.ts`
Expected: FAIL — cannot resolve `app/session`.

- [ ] **Step 3: Implement**

`src/app/session.ts`:

```ts
import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { diagramFingerprint } from '../kernel/diagram/canonical/fingerprint'
import { applyDoubleCutElim } from '../kernel/rules/doublecut'
import { applyVacuousBubbleElim } from '../kernel/rules/vacuous'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { composeProofs } from '../kernel/proof/compose'

export type Side = {
  readonly current: Diagram
  readonly steps: readonly ProofStep[]
  readonly history: readonly Diagram[]
}

export type ProofSession = {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly ctx: ProofContext
  readonly forward: Side
  readonly backward: Side
}

export function startSession(lhs: DiagramWithBoundary, rhs: DiagramWithBoundary, ctx: ProofContext): ProofSession {
  return {
    lhs, rhs, ctx,
    forward: { current: lhs.diagram, steps: [], history: [] },
    backward: { current: rhs.diagram, steps: [], history: [] },
  }
}

/** Apply a forward step through the kernel; refusals propagate untouched. */
export function applyForward(s: ProofSession, step: ProofStep): ProofSession {
  const next = applyStep(s.forward.current, step, s.ctx)
  return {
    ...s,
    forward: {
      current: next,
      steps: [...s.forward.steps, step],
      history: [...s.forward.history, s.forward.current],
    },
  }
}

export function undoForward(s: ProofSession): ProofSession {
  const history = s.forward.history
  if (history.length === 0) throw new Error('nothing to undo on the forward side')
  return {
    ...s,
    forward: {
      current: history[history.length - 1]!,
      steps: s.forward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
}

/**
 * Backward actions transform the GOAL side: the user removes structure the
 * forward direction would add. Each action computes the inverse-applied
 * diagram G′ and the forward step (G′ → G) TOGETHER, then asserts that
 * replaying the step on G′ reproduces G id-exactly — keeping the recorded
 * tail replayable without iso-rewriting anywhere except the meet.
 */
export type BackwardAction =
  | { readonly kind: 'unDoubleCut'; readonly outer: RegionId }
  | { readonly kind: 'unVacuousBubble'; readonly bubble: RegionId }

export function applyBackward(s: ProofSession, action: BackwardAction): ProofSession {
  const g = s.backward.current
  let gPrime: Diagram
  let step: ProofStep
  switch (action.kind) {
    case 'unDoubleCut': {
      const inner = Object.entries(g.regions).find(
        ([, r]) => r.kind === 'cut' && r.parent === action.outer,
      )
      if (inner === undefined) throw new Error(`'${action.outer}' has no inner cut to unwrap`)
      gPrime = applyDoubleCutElim(g, action.outer)
      // the forward step re-creating the pair: intro around what the inner
      // cut contained, which now sits where the OUTER cut's parent was
      const outerRegion = g.regions[action.outer]!
      const parent: RegionId = outerRegion.kind === 'sheet' ? g.root : outerRegion.parent
      const regions = Object.entries(gPrime.regions)
        .filter(([id, r]) => r.kind !== 'sheet' && r.parent === parent && g.regions[id] !== undefined &&
          (g.regions[id]! as { parent?: RegionId }).parent === inner[0])
        .map(([id]) => id)
      const nodes = Object.entries(gPrime.nodes)
        .filter(([id, n]) => n.region === parent && g.nodes[id]?.region === inner[0])
        .map(([id]) => id)
      const wires = Object.entries(gPrime.wires)
        .filter(([id, w]) => w.scope === parent && g.wires[id]?.scope === inner[0])
        .map(([id]) => id)
      step = { rule: 'doubleCutIntro', sel: { region: parent, regions, nodes, wires } }
      break
    }
    case 'unVacuousBubble': {
      const b = g.regions[action.bubble]
      if (b === undefined || b.kind !== 'bubble') throw new Error(`'${action.bubble}' is not a bubble`)
      gPrime = applyVacuousBubbleElim(g, action.bubble)
      const parent = b.parent
      const regions = Object.entries(gPrime.regions)
        .filter(([id, r]) => r.kind !== 'sheet' && r.parent === parent &&
          (g.regions[id] as { parent?: RegionId } | undefined)?.parent === action.bubble)
        .map(([id]) => id)
      const nodes = Object.entries(gPrime.nodes)
        .filter(([id, n]) => n.region === parent && g.nodes[id]?.region === action.bubble)
        .map(([id]) => id)
      const wires = Object.entries(gPrime.wires)
        .filter(([id, w]) => w.scope === parent && g.wires[id]?.scope === action.bubble)
        .map(([id]) => id)
      step = { rule: 'vacuousIntro', sel: { region: parent, regions, nodes, wires }, arity: b.arity }
      break
    }
  }
  // the reproduction assertion: forward(step, G′) must be G id-exactly
  const reproduced = applyStep(gPrime, step, s.ctx)
  if (diagramFingerprint(reproduced) !== diagramFingerprint(g)) {
    throw new Error(`backward action '${action.kind}' could not reconstruct the goal it inverted; this is a session bug`)
  }
  return {
    ...s,
    backward: {
      current: gPrime,
      steps: [...s.backward.steps, step],
      history: [...s.backward.history, g],
    },
  }
}

export function undoBackward(s: ProofSession): ProofSession {
  const history = s.backward.history
  if (history.length === 0) throw new Error('nothing to undo on the backward side')
  return {
    ...s,
    backward: {
      current: history[history.length - 1]!,
      steps: s.backward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
}

export function meet(s: ProofSession): boolean {
  return diagramFingerprint(s.forward.current) === diagramFingerprint(s.backward.current)
}

/** Compose both halves into the finished theorem (caller runs checkTheorem). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  const tail = [...s.backward.steps].reverse()
  const composed = composeProofs(s.forward.current, s.backward.current, tail, s.ctx)
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    steps: [...s.forward.steps, ...composed],
  }
}
```

NOTE on the reproduction assertion: it compares FINGERPRINTS, not raw ids — `composeProofs` at the meet handles any id drift between the recorded tail's diagrams and the forward side, and within the backward chain each step was literally constructed against its own predecessor, so replay works; the fingerprint assertion catches semantic divergence (a wrong selection reconstruction) loudly at action time, which is the bug class that matters. The doc comment above says "id-exactly" as the aspiration the selection-reconstruction code aims for — implementer: reword that comment to match the fingerprint check (the plan text is the drift).

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/app/session.ts tests/app/session.test.ts
git commit -m "feat(app): bidirectional proof session with meet composition"
```

---

### Task 3: Hit testing + selection building

**Files:**
- Create: `src/app/hittest.ts`
- Test: `tests/app/hittest.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/app/hittest.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { vec } from '../../src/view/vec'
import { hitTest, buildSelection } from '../../src/app/hittest'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function setup() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('\\x. x'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('y'))
  const d = h.build()
  const positions = new Map([[n, vec(0, 0)], [m, vec(60, 0)]])
  const scene = buildScene(d, positions)
  return { d, n, cut, m, scene }
}

describe('hitTest', () => {
  it('resolves a node when the point is inside its outer radius', () => {
    const { n, scene } = setup()
    const hit = hitTest(scene, vec(1, 1))
    expect(hit).toEqual({ kind: 'node', id: n })
  })

  it('resolves the smallest containing region otherwise', () => {
    const { cut, scene } = setup()
    const region = scene.regions.find((r) => r.id === cut)!
    const probe = vec(region.center.x + region.radius - 1, region.center.y)
    const hit = hitTest(scene, probe)
    expect(hit).toEqual({ kind: 'region', id: cut })
  })

  it('resolves a wire near a spoke segment', () => {
    const { d, n, m } = setup()
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    const b = h2.termNode(h2.root, p('y'))
    const w = h2.wire(h2.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d2 = h2.build()
    const scene2 = buildScene(d2, new Map([[a, vec(0, 0)], [b, vec(80, 0)]]))
    const star = scene2.wires.find((x) => x.id === w)!
    const mid = vec((star.hub.x + star.spokes[0]!.x) / 2, (star.hub.y + star.spokes[0]!.y) / 2)
    expect(hitTest(scene2, mid)).toEqual({ kind: 'wire', id: w })
    void d
    void n
    void m
  })

  it('returns null in empty space', () => {
    const { scene } = setup()
    expect(hitTest(scene, vec(500, 500))).toBeNull()
  })
})

describe('buildSelection', () => {
  it('derives the anchor and partitions items into nodes and subtree roots', () => {
    const { d, n, cut } = setup()
    const sel = buildSelection(d, [{ kind: 'node', id: n }, { kind: 'region', id: cut }])
    expect(sel.region).toBe(d.root)
    expect(sel.nodes).toEqual([n])
    expect(sel.regions).toEqual([cut])
  })

  it('refuses mixed-depth picks with an instructive message', () => {
    const { d, n, m } = setup()
    expect(() => buildSelection(d, [{ kind: 'node', id: n }, { kind: 'node', id: m }]))
      .toThrowError(/select the enclosing cut instead/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

- [ ] **Step 3: Implement**

`src/app/hittest.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Scene } from '../view/scene'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'

export type Hit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

/** UI pick tolerance around wire segments, world units. Visual only. */
const WIRE_TOLERANCE = 1.5

function segmentDistance(p: Vec2, a: Vec2, b: Vec2): number {
  const ab = sub(b, a)
  const ap = sub(p, a)
  const len2 = ab.x * ab.x + ab.y * ab.y
  const t = len2 === 0 ? 0 : Math.max(0, Math.min(1, (ap.x * ab.x + ap.y * ab.y) / len2))
  return length(sub(p, { x: a.x + ab.x * t, y: a.y + ab.y * t }))
}

/** Topmost item under the point: node, then wire, then smallest region. */
export function hitTest(scene: Scene, point: Vec2): Hit | null {
  for (const n of scene.nodes) {
    if (length(sub(point, n.center)) <= n.geometry.outerRadius) {
      return { kind: 'node', id: n.id }
    }
  }
  for (const w of scene.wires) {
    for (const spoke of w.spokes) {
      if (segmentDistance(point, w.hub, spoke) <= WIRE_TOLERANCE) {
        return { kind: 'wire', id: w.id }
      }
    }
  }
  let best: { id: RegionId; radius: number } | null = null
  for (const r of scene.regions) {
    if (r.kind === 'sheet') continue
    if (length(sub(point, r.center)) <= r.radius && (best === null || r.radius < best.radius)) {
      best = { id: r.id, radius: r.radius }
    }
  }
  return best === null ? null : { kind: 'region', id: best.id }
}

/**
 * Build a kernel selection from clicked items. The anchor is the common
 * parent: every picked node must live DIRECTLY in it and every picked region
 * must be its direct child — anything deeper needs its enclosing subtree
 * picked instead, and the refusal says so.
 */
export function buildSelection(d: Diagram, items: readonly Hit[]): SubgraphSelection {
  const nodes: NodeId[] = []
  const regions: RegionId[] = []
  const wires: WireId[] = []
  const anchors = new Set<RegionId>()
  for (const item of items) {
    if (item.kind === 'node') {
      const n = d.nodes[item.id]
      if (n === undefined) throw new Error(`unknown node '${item.id}'`)
      nodes.push(item.id)
      anchors.add(n.region)
    } else if (item.kind === 'region') {
      const r = d.regions[item.id]
      if (r === undefined) throw new Error(`unknown region '${item.id}'`)
      if (r.kind === 'sheet') throw new Error('the sheet cannot be selected')
      regions.push(item.id)
      anchors.add(r.parent)
    } else {
      const w = d.wires[item.id]
      if (w === undefined) throw new Error(`unknown wire '${item.id}'`)
      wires.push(item.id)
      anchors.add(w.scope)
    }
  }
  if (anchors.size === 0) throw new Error('nothing selected')
  if (anchors.size > 1) {
    throw new Error(
      `selection spans several regions (${[...anchors].map((a) => `'${a}'`).join(', ')}); select the enclosing cut instead of reaching inside it`,
    )
  }
  const region = [...anchors][0]!
  return mkSelection(d, { region, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/app/hittest.ts tests/app/hittest.test.ts
git commit -m "feat(app): hit testing and interactive selection building"
```

---

### Task 4: Action enumeration

**Files:**
- Create: `src/app/actions.ts`
- Test: `tests/app/actions.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/app/actions.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { applicableActions } from '../../src/app/actions'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applicableActions', () => {
  it('offers erasure at positive selections and insertion at negative regions', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())

    const pos = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const atPos = applicableActions(d, pos, ctx).map((a) => a.kind)
    expect(atPos).toContain('erase')
    expect(atPos).not.toContain('insert')
    expect(atPos).toContain('doubleCutWrap')
    expect(atPos).toContain('iterate')
    expect(atPos).toContain('vacuousWrap')

    const neg = mkSelection(d, { region: cut, regions: [], nodes: [], wires: [] })
    const atNeg = applicableActions(d, neg, ctx).map((a) => a.kind)
    expect(atNeg).toContain('insert')
    expect(atNeg).not.toContain('erase')
  })

  it('offers double-cut elimination only on empty-annulus cuts', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    h.cut(c1)
    const c3 = h.cut(h.root)
    h.termNode(c3, p('y'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const onClean = applicableActions(d, mkSelection(d, { region: d.root, regions: [c1], nodes: [], wires: [] }), ctx)
    expect(onClean.map((a) => a.kind)).toContain('doubleCutElim')
    const onDirty = applicableActions(d, mkSelection(d, { region: d.root, regions: [c3], nodes: [], wires: [] }), ctx)
    expect(onDirty.map((a) => a.kind)).not.toContain('doubleCutElim')
  })

  it('offers vacuous elimination only on atom-free bubbles, and instantiation only on negative ones', () => {
    const h = new DiagramBuilder()
    const empty = h.bubble(h.root, 1)
    const cut = h.cut(h.root)
    const negBub = h.bubble(cut, 1)
    h.atom(negBub, negBub)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const onEmpty = applicableActions(d, mkSelection(d, { region: d.root, regions: [empty], nodes: [], wires: [] }), ctx).map((a) => a.kind)
    expect(onEmpty).toContain('vacuousElim')
    expect(onEmpty).not.toContain('instantiate')
    const onNeg = applicableActions(d, mkSelection(d, { region: cut, regions: [negBub], nodes: [], wires: [] }), ctx).map((a) => a.kind)
    expect(onNeg).toContain('instantiate')
    expect(onNeg).not.toContain('vacuousElim')
  })

  it('offers theorem citations whose direction matches the selection polarity', () => {
    const consts = new Set(['ZERO'])
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, parseTerm('ZERO', consts))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [nz], wires: [] })
    const cites = applicableActions(d, sel, ctx).filter((a) => a.kind === 'citeTheorem')
    expect(cites.length).toBeGreaterThan(0)
    expect(cites.every((c) => c.kind === 'citeTheorem' && c.direction === 'forward')).toBe(true)
  })

  it('every descriptor carries a human label', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    for (const a of applicableActions(d, sel, ctx)) {
      expect(a.label.length).toBeGreaterThan(0)
    }
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

- [ ] **Step 3: Implement**

`src/app/actions.ts`:

```ts
import type { Diagram } from '../kernel/diagram/diagram'
import { polarity } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/step'

/**
 * Pure, read-only enumeration of moves the UI may offer for a selection.
 * Gates are MIRRORED here (never invoked): the applier remains the sole
 * authority at commit time, and its refusal message is surfaced verbatim.
 * Two-phase moves (targets, arguments, terms) are flagged, not resolved.
 */
export type ActionDescriptor =
  | { readonly kind: 'erase'; readonly label: string }
  | { readonly kind: 'insert'; readonly label: string; readonly needsInput: 'pattern' }
  | { readonly kind: 'doubleCutWrap'; readonly label: string }
  | { readonly kind: 'doubleCutElim'; readonly label: string }
  | { readonly kind: 'vacuousWrap'; readonly label: string; readonly needsInput: 'arity' }
  | { readonly kind: 'vacuousElim'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string; readonly needsTarget: true }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'instantiate'; readonly label: string; readonly needsInput: 'comprehension' }
  | { readonly kind: 'convert'; readonly label: string; readonly needsInput: 'term' }
  | { readonly kind: 'citeTheorem'; readonly label: string; readonly name: string; readonly direction: 'forward' | 'reverse' }

export function applicableActions(d: Diagram, sel: SubgraphSelection, ctx: ProofContext): ActionDescriptor[] {
  const out: ActionDescriptor[] = []
  const pol = polarity(d, sel.region)
  const hasContent = sel.nodes.length + sel.regions.length + sel.wires.length > 0

  if (hasContent && pol === 'positive') out.push({ kind: 'erase', label: 'Erase (positive region)' })
  if (!hasContent && pol === 'negative') out.push({ kind: 'insert', label: 'Insert…', needsInput: 'pattern' })
  out.push({ kind: 'doubleCutWrap', label: 'Wrap in a double cut' })
  out.push({ kind: 'vacuousWrap', label: 'Wrap in a vacuous bubble…', needsInput: 'arity' })
  if (hasContent) {
    out.push({ kind: 'iterate', label: 'Iterate into…', needsTarget: true })
    out.push({ kind: 'deiterate', label: 'Deiterate (needs a justifying copy)' })
  }
  if (sel.nodes.length === 1 && sel.regions.length === 0 && d.nodes[sel.nodes[0]!]?.kind === 'term') {
    out.push({ kind: 'convert', label: 'Convert (βη)…', needsInput: 'term' })
  }

  // single selected region: structural eliminations
  if (sel.regions.length === 1 && sel.nodes.length === 0 && sel.wires.length === 0) {
    const rid = sel.regions[0]!
    const r = d.regions[rid]!
    if (r.kind === 'cut') {
      const children = Object.entries(d.regions).filter(([, x]) => x.kind !== 'sheet' && x.parent === rid)
      const nodesIn = Object.values(d.nodes).some((n) => n.region === rid)
      const wiresIn = Object.values(d.wires).some((w) => w.scope === rid)
      if (children.length === 1 && children[0]![1].kind === 'cut' && !nodesIn && !wiresIn) {
        out.push({ kind: 'doubleCutElim', label: 'Eliminate the double cut' })
      }
    }
    if (r.kind === 'bubble') {
      const bound = Object.values(d.nodes).some((n) => n.kind === 'atom' && n.binder === rid)
      if (!bound) out.push({ kind: 'vacuousElim', label: 'Dissolve the vacuous bubble' })
      if (bound && polarity(d, rid) === 'negative') {
        out.push({ kind: 'instantiate', label: 'Instantiate the relation…', needsInput: 'comprehension' })
      }
    }
  }

  for (const [name] of ctx.theorems) {
    const direction = pol === 'positive' ? 'forward' as const : 'reverse' as const
    out.push({ kind: 'citeTheorem', label: `Cite ${name} (${direction})`, name, direction })
  }
  return out
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/app/actions.ts tests/app/actions.test.ts
git commit -m "feat(app): polarity-aware action enumeration"
```

---

### Task 5: The shell

**Files:**
- Create: `src/app/shell.ts`, `src/app/index.ts`
- Create: `app/index.html`, `app/main.ts`
- Modify: `package.json` (`"app": "vite app"`)
- Modify: `tests/architecture/layering.test.ts` (app edges: nothing under src/kernel, src/view, src/theories imports src/app; only shell.ts and view/canvas.ts touch DOM types)

The shell is browser glue: every decision branch calls a tested headless function. No unit tests beyond the layering edges and the vite build; behavioral coverage is Plan 10d's E2E.

- [ ] **Step 1: Layering edges** — extend the architecture test with:

```ts
  it('nothing below the app layer imports it', () => {
    const offenders: string[] = []
    for (const dir of ['src/kernel', 'src/view', 'src/theories']) {
      for (const file of tsFilesUnder(dir)) {
        for (const spec of importSpecifiers(file)) {
          if (spec.includes('/app/') || spec.startsWith('../app')) {
            offenders.push(`${file} imports '${spec}'`)
          }
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
```

- [ ] **Step 2: Implement the shell.** `src/app/shell.ts` owns: mode state (`'edit' | 'prove'`), the displayed diagram (edit target or session side), selection (list of Hits + the derived kernel selection when valid), pending two-phase action, physics state + pin, viewport transform (pan/zoom), and the render loop. Public surface:

```ts
export type ShellOptions = {
  readonly canvas: HTMLCanvasElement
  readonly chrome: HTMLElement
}
export function mountShell(opts: ShellOptions): { dispose(): void }
```

Internals (write straightforwardly — this is glue):
- Boot: `loadTheory(theoryToJson(buildFregeTheory()))` + lambda likewise; merge contexts for citation lists.
- Edit mode: term input (`<input>` whose value goes through `parseTerm(value, constNames)`; `\` is already the parser's λ), buttons for cut/bubble wrapping and delete over the current selection (calling `edit.ts`), port-join via two successive port-ish clicks (clicking a node cycles its anchors — keep simple: clicking two WIRES joins them via `joinPorts` on representative endpoints; refine in 10d).
- Prove mode: "set goal" snapshots the current edit diagram as lhs and a second snapshot as rhs (two buttons), `startSession`; the action menu renders `applicableActions(side.current, selection, ctx)` for the active side (forward/backward toggle); committing an action builds the ProofStep (or BackwardAction) and calls `applyForward`/`applyBackward` in a try/catch whose error message lands in the status line verbatim; meet detection updates the status line; "assemble" runs `assembleTheorem` + `checkTheorem` and reports.
- Render loop: physics `step()` per frame (with the drag pin override), `buildScene`, `renderScene`, `drawShapes` with the viewport transform; hover highlights the `hitTest` result by re-stroking its shape (binder hover tethers land in 10d with the richer interaction pass).
- `src/app/index.ts` barrel: `export { mountShell } from './shell'` plus the headless modules' exports.
- `app/main.ts`: `mountShell({ canvas, chrome })` on DOM ready; `app/index.html` mirrors demo/index.html plus a chrome `<div>`.

- [ ] **Step 3: Gates** — `npx vitest run` (all green incl. new layering edge), `npx tsc --noEmit`, `npx vite build app --logLevel error` compiles. Never start the dev server.

- [ ] **Step 4: Commit**

```bash
git add src/app/shell.ts src/app/index.ts app/index.html app/main.ts package.json tests/architecture/layering.test.ts
git commit -m "feat(app): canvas shell with edit/prove modes over the headless core"
```

---

### Task 6: Battery

**Files:**
- Test: `tests/app/pipeline.test.ts`

- [ ] **Step 1: Write the battery** (must pass against Tasks 1–5)

`tests/app/pipeline.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { emptyDiagram, addTermNode, addCut } from '../../src/app/edit'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { startSession, applyForward, applyBackward, meet, assembleTheorem } from '../../src/app/session'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('edit → prove → assemble, end to end', () => {
  it('a user-constructed goal is proven bidirectionally and checks', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // EDIT: lhs = a single identity node; rhs = the same wrapped in two cuts
    const e0 = emptyDiagram()
    const { diagram: lhsD } = addTermNode(e0, e0.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(lhsD, [])
    const r1 = addTermNode(e0, e0.root, p('\\x. x'))
    const selR = mkSelection(r1.diagram, { region: r1.diagram.root, regions: [], nodes: [r1.node], wires: [] })
    const r2 = addCut(r1.diagram, selR)
    const selR2 = mkSelection(r2.diagram, { region: r2.diagram.root, regions: [r2.region], nodes: [], wires: [] })
    const r3 = addCut(r2.diagram, selR2)
    const rhs = mkDiagramWithBoundary(r3.diagram, [])

    // PROVE: backward unwrap meets the untouched forward side
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, { kind: 'unDoubleCut', outer: r3.region })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'identityDoubleCut')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('forward citation sessions check too', () => {
    const consts = new Set(['ZERO'])
    const ctx = verifyTheory(buildFregeTheory())
    const e0 = emptyDiagram()
    const { diagram: startD, node } = addTermNode(e0, e0.root, parseTerm('ZERO', consts))
    const wz = Object.entries(startD.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'output'))![0]
    const lhs = mkDiagramWithBoundary(startD, [wz])
    let s = startSession(lhs, lhs, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
      at: { sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [node], wires: [] }), args: [wz] },
    })
    const rhs = mkDiagramWithBoundary(s.forward.current, [wz])
    const thm = { name: 'viaSession', lhs, rhs, steps: [...s.forward.steps] }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Commit**

```bash
git add tests/app/pipeline.test.ts
git commit -m "test(app): edit-to-checked-theorem pipeline battery"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean, `npx vite build app` compiles.
- Demonstrated: construction surgery validated by mkDiagram (incl. cross-scope port joining and instructive selection refusals); the session applies forward steps through the kernel with verbatim refusal surfacing, records backward actions as reproduction-asserted forward steps, detects meets by fingerprint, and assembles theorems that `checkTheorem` accepts; hit testing resolves node/wire/region by the documented precedence; action enumeration mirrors every gate read-only (erase/insert polarity, empty-annulus, vacuity, instantiation negativity, citation direction); the app layer sits strictly on top (layering edges machine-checked).
- Plan 10d: persistence UI (save/load theory files from the browser), hover tethers + richer port wiring, E2E (playwright), and the polish pass.

## Carried obligations (forward)

- Backward-mode coverage grows on demand: `unDoubleCut`/`unVacuousBubble` ship now; un-erase (backward insertion), un-conversion, and un-citation land in 10d alongside the E2E that exercises them.
- All prior carried items (open theorem sides, matcher symmetry, R(x,x), joinPorts deepest-common-ancestor) remain.
