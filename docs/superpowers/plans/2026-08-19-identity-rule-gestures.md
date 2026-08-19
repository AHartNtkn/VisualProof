# Identity-Rule Gestures Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the three identity rules (vacuity / presentation invariance / identification) direct gestures in both edit and proof mode, delete the unratified draw.ts contact mechanism, and re-home proof-mode sever on the slash.

**Architecture:** A new shared `IdentityOpsController` (src/app/interact/identity-ops.ts) recognizes identity-specific grabs (dot interior, dot rim, legs, end discs) and dispatches oriented drops to kernel `ProofStep`s; proof mode commits them through the step pipeline, edit mode applies them directly via the kernel rule functions (the rules are ungated, so both modes share one implementation). The construction-mode slash is extracted to a shared `SlashController` and gains a proof-mode committer producing `wireSever` steps. `DrawGestureController` is deleted with its dead UI surface.

**Tech Stack:** TypeScript, vitest (`npx vitest run --config vitest.config.ts <file>`), no new dependencies.

**Spec:** `docs/superpowers/specs/2026-08-19-identity-rule-gestures-design.md` (ratified 2026-08-19 — read it first; it records the gesture table and the precedence rulings this plan implements).

## Global Constraints

- Work lands on branch `worktree-signature-indexed-wires` in `.worktrees/signature-indexed-wires`. A peer Lean session commits to the same branch: `git add` ONLY the specific files you touched, never `-A`/`.`; never touch `VisualProof/`.
- NEVER run `test:physics` or `test:all`. Verification = targeted vitest files + `npx tsc --noEmit` (whole project).
- Kernel is sole authority: gesture code never re-implements gates; refusals surface the kernel message verbatim via `refuse(text, pointer)`.
- No menus for proof actions; every new gesture is a single-object action or an oriented drag between two specific objects; nothing consumes selection order.
- Same gesture ⇒ same operation in edit and proof mode (see spec table).
- No dead code: anything made unreachable by a deletion in this plan is deleted in the same task.
- TDD per task: write the failing test, watch it fail, implement, watch it pass, commit.
- Commit messages: conventional prefixes (`feat:`, `refactor:`, `test:`), no mention of plans/history.

---

### Task 1: Extract the slash into a shared SlashController

The slash (right-drag straight line; crossed wire legs sever) lives inline in `ConstructController.#slashClaim` (src/app/interact/construct.ts:217-256) with private helpers `crosses`, `crossedLegs` (construct.ts:69-90), and `endpointAt` (construct.ts:92-100). Extract it so proof mode can reuse it (Task 2). Edit-mode behavior must not change.

**Files:**
- Create: `src/app/interact/slash.ts`
- Modify: `src/app/interact/construct.ts` (delete moved helpers + `#slashClaim`, delegate to the controller)
- Test: `tests/app/slash.test.ts`

**Interfaces (produced):**

```ts
// src/app/interact/slash.ts
export type SlashCrossing = { readonly wire: WireId; readonly endpoint: Endpoint }
export type SlashOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly theme: () => Theme
  /** Endpoint-resolved crossings, at least one. Junction-only legs are pre-filtered. */
  readonly commit: (crossings: readonly SlashCrossing[], sample: PointerSample) => void
  /** A still right-click: the mode's resting right-click surface (spawn / context). */
  readonly still: (sample: PointerSample) => void
  readonly refuse: (text: string, pointer: Vec2) => void
}
export class SlashController {
  constructor(options: SlashOptions)
  claim(sample: PointerSample): PointerClaim | null   // right button only
  /** True exactly once after a claimed right release, to suppress the browser contextmenu. */
  consumeMenuSuppression(): boolean
  overlay(): readonly Shape[]
  cancel(): void
}
```

Behavior moved verbatim from construct.ts: a right press claims; `move` extends the preview segment; a still release calls `still(sample)`; a moved release computes `crossedLegs(engine, from, to)`, resolves each leg to its endpoint via `endpointAt`, then:
- no crossings at all → `refuse('the slash crossed no strand', sample.client)`
- crossings exist but none resolve (all junction-side) → `refuse('that strand runs between junctions; sever nearer a port', sample.client)`
- otherwise → `commit(resolvedCrossings, sample)`.

Overlay: the preview segment stroked with `theme().interaction.refusal`, width 2 (as today). Menu suppression: set a flag on every claimed right press; `consumeMenuSuppression()` reads and clears it (copy the pattern from the current draw.ts:116-120).

**Steps:**

- [ ] **Step 1: Write the failing test**

```ts
// tests/app/slash.test.ts
import { describe, expect, it } from 'vitest'
import { SlashController, type SlashCrossing } from '../../src/app/interact/slash'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { PointerSample } from '../../src/app/interact/viewport'
import { place, pointerSample } from './helpers/gesture'

function rightSample(point: { x: number; y: number }): PointerSample {
  return { ...pointerSample(point), button: 2 }
}

describe('SlashController', () => {
  function harness() {
    const builder = new DiagramBuilder()
    const seg = segment(builder, builder.root)   // from './helpers/build'
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, seg.ends[0], { x: 100, y: 300 })
    place(engine, seg.ends[1], { x: 500, y: 300 })
    const commits: SlashCrossing[][] = []
    const stills: PointerSample[] = []
    const refusals: string[] = []
    const controller = new SlashController({
      active: () => true,
      engine: () => engine,
      diagram: () => diagram,
      theme: () => LIGHT,
      commit: (crossings) => { commits.push([...crossings]) },
      still: (sample) => { stills.push(sample) },
      refuse: (text) => { refusals.push(text) },
    })
    return { controller, commits, stills, refusals }
  }

  it('severs the crossed leg', () => {
    const { controller, commits } = harness()
    const claim = controller.claim(rightSample({ x: 300, y: 100 }))
    expect(claim).not.toBeNull()
    claim!.move(rightSample({ x: 300, y: 500 }))
    claim!.release(rightSample({ x: 300, y: 500 }), true)
    expect(commits).toHaveLength(1)
    expect(commits[0]!.length).toBeGreaterThan(0)
  })

  it('a still right-click reaches the resting surface', () => {
    const { controller, stills } = harness()
    const claim = controller.claim(rightSample({ x: 700, y: 700 }))
    claim!.release(rightSample({ x: 700, y: 700 }), false)
    expect(stills).toHaveLength(1)
  })

  it('refuses a slash through nothing', () => {
    const { controller, refusals } = harness()
    const claim = controller.claim(rightSample({ x: 700, y: 650 }))
    claim!.move(rightSample({ x: 720, y: 700 }))
    claim!.release(rightSample({ x: 720, y: 700 }), true)
    expect(refusals).toEqual(['the slash crossed no strand'])
  })
})
```

Fix the fixture against real signatures before running: `builder.atom(region, relSig([IOTA]))`, wire sig must match the atom sig (see tests/app/wire-ops.test.ts:103-116 `pluming()` for the exact pattern). The wire between atom (100,300) and pin (500,300) runs horizontally; the slash from (300,100) to (300,500) crosses it.

- [ ] **Step 2: Run to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/app/slash.test.ts`
Expected: FAIL — module `src/app/interact/slash.ts` does not exist.

- [ ] **Step 3: Create slash.ts by moving code out of construct.ts**

Move `crosses`, `crossedLegs`, `endpointAt`, and the `#slashClaim` body into `SlashController` per the interface above. `crossedLegs` needs `computeLegs` from `../../view/wires` and `LegGeom` — check construct.ts's imports and move exactly what the helpers use. Rewire `ConstructController`: construct a `SlashController` in its constructor with

```ts
this.#slash = new SlashController({
  active: options.active,
  engine: options.engine,
  diagram: options.diagram,
  theme: options.theme,
  still: (sample) => {
    this.#options.openSpawn(sample, regionAt(this.#options.engine(), this.#options.diagram(), sample.world))
  },
  commit: (crossings, sample) => {
    let next = this.#options.diagram()
    let severed = 0
    for (const crossing of crossings) {
      try {
        next = severEndpoint(next, crossing.wire, crossing.endpoint)
        severed++
      } catch (error) {
        this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
      }
    }
    if (severed > 0) this.#options.commit(next)
  },
  refuse: options.refuse,
})
```

and replace `if (sample.button === 2) return this.#slashClaim(sample)` with `return this.#slash.claim(sample)`. The slash preview moves into `SlashController.overlay()`; `ConstructController.overlay()` spreads it. Delete `#slashClaim` and the moved helpers from construct.ts.

Note the crossing-to-wire mapping: construct's old loop severed via `crossing.leg.wid`; `SlashCrossing.wire` carries that id.

- [ ] **Step 4: Run the new test and the edit-mode suite**

Run: `npx vitest run --config vitest.config.ts tests/app/slash.test.ts tests/app/edit.test.ts tests/app/connection.test.ts tests/app/shell-label.test.ts`
Expected: PASS (edit-mode slash behavior unchanged).

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/slash.ts src/app/interact/construct.ts tests/app/slash.test.ts
git commit -m "refactor: extract the slash into a shared controller"
```

---

### Task 2: Proof-mode slash severs; delete draw.ts

Right button in proof mode currently routes to `DrawGestureController` (moves.ts:210). Replace it with a `SlashController` committing `wireSever` steps, and delete draw.ts and everything only it reached.

**Files:**
- Delete: `src/app/interact/draw.ts`, `tests/app/draw.test.ts`
- Modify: `src/app/interact/moves.ts` (replace `#draw` with `#slash`; keep `Q`, keep `openSpawn`, keep `#openContextMenu`)
- Test: extend `tests/app/moves.test.ts`; prune its draw-dependent cases

**Interfaces:**
- Consumes: `SlashController` from Task 1.
- Produces: proof right-drag = sever. The `wireSever` step shape: `{ rule: 'wireSever', input: { wire, keep } }` — `keep` is the wire's endpoints minus the crossed ones; `scope` omitted (defaults to the wire's derived scope, src/kernel/rules/wire-quantifier.ts:23-32).

**Steps:**

- [ ] **Step 1: Write the failing test**

In tests/app/moves.test.ts, using the file's existing `harness` (it records `ProofAction`s passed to `apply`) and its local `pointerSample`/`keySample`; add `place` from `./helpers/gesture` to the imports:

```ts
it('a right-drag slash across a leg commits wireSever', () => {
  const builder = new DiagramBuilder()
  const seg = segment(builder, builder.root)
  const diagram = builder.build()
  const { moves, engine, applied } = harness(diagram)
  place(engine, seg.ends[0], { x: 100, y: 300 })
  place(engine, seg.ends[1], { x: 500, y: 300 })
  const at = (p: Vec2) => ({ ...pointerSample(p), button: 2 })
  const claim = moves.claim(at({ x: 150, y: 100 }))
  expect(claim).not.toBeNull()
  claim!.move(at({ x: 150, y: 500 }))
  claim!.release(at({ x: 150, y: 500 }), true)
  expect(applied).toHaveLength(1)
  const steps = applied[0]!.steps
  expect(steps.length).toBeGreaterThan(0)
  expect(steps.every((step) => step.rule === 'wireSever')).toBe(true)
  const input = (steps[0] as Extract<ProofStep, { rule: 'wireSever' }>).input
  expect(input.wire).toBe(seg.wire)
  expect(input.keep).toHaveLength(1)   // one end severed, one kept
  expect(input.scope).toBeUndefined()  // derived-scope default
})
```

(The vertical slash at x=150 crosses the chain between the pins near `ends[0]`; which endpoint the crossed leg resolves to is geometry the kernel doesn't care about, so assert the count, not the identity.)

- [ ] **Step 2: Run to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/app/moves.test.ts -t 'slash'`
Expected: FAIL — right-button claims still route to the draw controller.

- [ ] **Step 3: Rewire moves.ts and delete draw.ts**

In `ProofMoveController`:
- Delete the `#draw` field, its construction (moves.ts:149-164), `...this.#draw.overlay()`, `this.#draw.cancel()`, and the `hasPendingInteraction` check in the Escape branch.
- Add `#slash = new SlashController({ active, engine, diagram, theme, still: (sample) => { this.#openContextMenu(sample) }, commit: (crossings, sample) => { …build steps below…; this.#lastPointer = sample.client; this.#commitSteps('wireSever', steps) }, refuse: options.refuse })`.
- `claim`: `if (sample.button === 2) return this.#slash.claim(sample)`.
- `contextMenu`: replace `this.#draw.consumeMenuSuppression()` with `this.#slash.consumeMenuSuppression()`.

Step construction in the commit callback:

```ts
const diagram = this.#options.diagram()
const byWire = new Map<WireId, Endpoint[]>()
for (const crossing of crossings) {
  const bucket = byWire.get(crossing.wire) ?? []
  bucket.push(crossing.endpoint)
  byWire.set(crossing.wire, bucket)
}
const steps: ProofStep[] = [...byWire.entries()].map(([wire, severed]) => {
  const moved = new Set(severed.map((ep) => `${ep.node}:${pkey(ep.port)}`))
  const keep = (diagram.wires[wire]?.endpoints ?? [])
    .filter((ep) => !moved.has(`${ep.node}:${pkey(ep.port)}`))
  return { rule: 'wireSever', input: { wire, keep } }
})
```

Delete `src/app/interact/draw.ts` and `tests/app/draw.test.ts` entirely. Fix every remaining `import`/reference (`npx tsc --noEmit` finds them; expected sites: moves.ts only). Prune moves.test.ts / viewport-proof-moves.test.ts cases that exercised the deleted contact mechanism (pending drawings, contactless spawn commit, lasso cutWrap, strand-contact identityInsert, end-contact sever, identityAbstract, endsSpawn); keep and adapt any case that tested the still-right-click palette, which must still pass.

- [ ] **Step 4: Verify**

Run: `npx tsc --noEmit && npx vitest run --config vitest.config.ts tests/app/moves.test.ts tests/app/viewport-proof-moves.test.ts tests/app/slash.test.ts`
Expected: PASS, zero tsc errors.

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/moves.ts src/app/interact/draw.ts tests/app/draw.test.ts tests/app/moves.test.ts tests/app/viewport-proof-moves.test.ts
git commit -m "feat: proof-mode slash severs; delete the unratified drawing mechanism"
```

(`git add` on deleted paths records the deletions.)

---

### Task 3: Delete the dead identityInsert UI surface

With draw.ts gone, nothing reaches the `identityInsert` UI pieces. The kernel rule stays (it is proof-language, used by replays); only the UI dies. Interactive equating is compositional: strand→strand join, `Q`-pin, expose.

**Files:**
- Modify: `src/app/actions.ts` — delete the `identityInsert` ActionDescriptor variant (line 19), the `applicableActions` block pushing it (lines 48-50), and `identityInsertionWires` (lines 105-133).
- Modify: `src/app/interact/moves.ts` — delete the `case 'identityInsert'` in `#appendAction`.
- Modify: `src/app/interact/proof-spawn.ts` — the `case 'identity'` in `proofNodeSpawnStep` (lines 40-45): check reachability. `StructuralSpawnRequest.node` is a `DiagramNode`; if no caller ever passes an identity node (the `SpawnCascade` only wires `spawnRef`/`spawnAtom`), narrow the request type to `Exclude<DiagramNode, { kind: 'identity' }>` equivalent (e.g. a union of the atom/ref node shapes) and delete the case. If a test constructs it, delete that test case too.
- Test: `tests/app/actions.test.ts` — update: assert `identityInsert` is no longer offered anywhere.

**Steps:**

- [ ] **Step 1: Update the actions test to assert absence** (this is the failing test: it fails while the descriptor still exists)

```ts
it('never offers identityInsert — equating is compositional (join, pin, expose)', () => {
  // reuse the file's existing fixture that used to yield identityInsert
  // and assert the returned kinds exclude 'identityInsert'
})
```

- [ ] **Step 2: Run to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/app/actions.test.ts`
Expected: the new case FAILS (descriptor still produced); existing identityInsert-positive cases still pass.

- [ ] **Step 3: Delete the surface**

Make the modifications listed under Files. Delete the now-obsolete identityInsert-positive test cases in actions.test.ts.

- [ ] **Step 4: Verify**

Run: `npx tsc --noEmit && npx vitest run --config vitest.config.ts tests/app/actions.test.ts tests/app/moves.test.ts tests/app/spawn.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/app/actions.ts src/app/interact/moves.ts src/app/interact/proof-spawn.ts tests/app/actions.test.ts
git commit -m "refactor: delete the dead identityInsert UI surface"
```

---

### Task 4: IdentityOpsController — grabs and collapse

The new shared controller. This task builds the grab recognizer, the controller shell, the edit-mode direct applier, and the first drop row: **dot dragged into open space = identification collapse**.

**Files:**
- Create: `src/app/interact/identity-ops.ts`
- Modify: `src/app/interact/moves.ts` (instantiate; claim order: identity → wireOps → copy)
- Modify: `src/app/interact/construct.ts` (instantiate with the direct applier; claim order: identity → connection → copy → placement)
- Test: `tests/app/identity-ops.test.ts`

**Interfaces (produced — later tasks extend the drop table, these signatures are fixed):**

```ts
// src/app/interact/identity-ops.ts
export type IdentityGrab =
  | { readonly kind: 'dot'; readonly node: NodeId }
  | { readonly kind: 'dotRim'; readonly node: NodeId }
  | { readonly kind: 'leg'; readonly node: NodeId; readonly wire: WireId; readonly index: number }
  | { readonly kind: 'endDisc'; readonly node: NodeId; readonly wire: WireId }

export type IdentityOpsOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly viewScale: () => number
  readonly theme: () => Theme
  /** Edit mode claims atom/ref end discs for the expose drag; proof mode
      leaves them to WireOpsDragController, which owns richer end drops. */
  readonly claimEndDiscs: boolean
  readonly commit: (label: string, steps: readonly ProofStep[], pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

export class IdentityOpsController {
  constructor(options: IdentityOpsOptions)
  claim(sample: PointerSample): PointerClaim | null   // left button, no modifiers
  overlay(): readonly Shape[]
  cancel(): void
}

/** The identity dot whose disc (interior or rim halo) contains the point. */
export function identityDiscAt(engine: Engine, point: Vec2): NodeId | null

/** Edit-mode committer: apply identity-rule steps directly (they are ungated). */
export function applyIdentitySteps(d: Diagram, steps: readonly ProofStep[]): Diagram

/** Collapse at `node`: absorb all its wires into a survivor. Throws RuleError
    when the dot has fewer than two distinct wires. */
export function collapseStep(d: Diagram, node: NodeId): ProofStep
```

**Grab recognition** (`#grabAt(point)`), precedence documented in draw.ts's old probe comment (identity discs outrank wire terminals):
1. Identity disc first: for each engine body with `kind === 'identity'`, `r = body.discR * engine.scale`, `dist = |point - body.pos|`, `halo = HIT_RADIUS_PX / viewScale()` (HIT_RADIUS_PX = 6, as wire-ops). `|dist - r| <= halo` → `dotRim`; `dist < r - halo` → `dot`. (Between the bands, rim wins: `dist <= r + halo` → `dotRim`.)
2. Legs: `wireManipulationHitTest(engine, point, viewport)` returning an endpoint hit with `port.kind === 'identity'` → `{ kind: 'leg', node: endpoint.node, wire: hit.wire, index: endpoint.port.index }`. (Reached only outside every dot's halo, by ordering.)
3. End discs (`claimEndDiscs` only): atom/ref body whose disc contains the point, with its head wire (reuse the logic of wire-ops `#discAt`; import `headWireOf` from './wire-ops') → `endDisc`.
4. Otherwise null (the claim falls through to the next controller).

**Drop dispatch this task** (`#drop(grab, sample)`): only `grab.kind === 'dot'` → if the drop point hits neither a wire manipulation, nor an identity disc, nor (when relevant) an atom/ref disc — i.e. open space — commit `collapseStep`. Everything else refuses `'release in open space to collapse, or on another dot to fuse'`. Other grab kinds refuse with a placeholder-free message naming their gesture (`dotRim`: `'pull the stub into open space'` — implemented in Task 6; `leg`: `'release on the dot or one of its legs'` — Task 8; `endDisc`: `'release on an identity dot on this wire to expose'` — Task 7). Refusing is correct behavior for not-yet-implemented rows only because each row lands within this plan; the final state has every row live.

**collapseStep survivor algorithm** (spec ruling — forced-or-invisible):

```ts
export function collapseStep(d: Diagram, node: NodeId): ProofStep {
  const dot = d.nodes[node]
  if (dot === undefined || dot.kind !== 'identity') throw new RuleError(`'${node}' is not an identity node`)
  const attached = [...new Set(
    Object.entries(d.wires)
      .filter(([, w]) => w.endpoints.some((ep) => ep.node === node))
      .map(([id]) => id),
  )].sort()
  if (attached.length < 2) {
    throw new RuleError(`collapse needs at least two wires at '${node}'`)
  }
  const violates = (wireId: WireId): boolean =>
    d.wires[wireId]!.endpoints.some((ep) =>
      ep.node !== node && !isAncestorOrEqual(d, dot.region, d.nodes[ep.node]!.region))
  const violators = attached.filter(violates)
  const survivor = violators[0] ?? attached[0]!
  return {
    rule: 'identification',
    input: { kind: 'collapse', node, survivor, absorbed: attached.filter((w) => w !== survivor) },
  }
}
```

(If two or more wires violate, the kernel refuses with its own message — surfaced verbatim; do not pre-empt it.)

**applyIdentitySteps:**

```ts
export function applyIdentitySteps(d: Diagram, steps: readonly ProofStep[]): Diagram {
  let next = d
  for (const step of steps) {
    switch (step.rule) {
      case 'vacuity':
        next = step.direction === 'insert'
          ? applyVacuityInsert(next, step.instance)
          : applyVacuityDelete(next, step.instance)
        break
      case 'presentation':
        next = applyPresentation(next, step.input)
        break
      case 'identification':
        next = applyIdentification(next, step.input)
        break
      default:
        throw new Error(`'${step.rule}' is not an identity-rule step`)
    }
  }
  return next
}
```

**Overlay:** a segment from grab origin to the current pointer in `theme().interaction.valid`, width 1.6 — the same feedback wire-ops draws. Use the `#issueClaim` epoch pattern copied from wire-ops.ts:445-472 so cancel is race-safe.

**Mode wiring:**
- moves.ts: `#identity = new IdentityOpsController({ …, claimEndDiscs: false, commit: (label, steps, pointer) => { this.#lastPointer = pointer; return this.#commitSteps(label, steps) }, refuse: options.refuse })`; claim order becomes `this.#identity.claim(sample) ?? this.#wireOps.claim(sample) ?? this.#copy.claim(sample)`.
- construct.ts: `#identity = new IdentityOpsController({ …, claimEndDiscs: true, commit: (label, steps) => this.#tryCommit(() => applyIdentitySteps(this.#options.diagram(), steps), label), refuse: options.refuse })`; claim it before `#connection` (a leg press must be an identity grab, not a join source — joins remain available from strands). Spread `#identity.overlay()` into both modes' overlays and call `cancel()` from both `dispose`/`cancel` paths.

**Steps:**

- [ ] **Step 1: Write the failing tests**

```ts
// tests/app/identity-ops.test.ts
import { describe, expect, it } from 'vitest'
import { IdentityOpsController, applyIdentitySteps, collapseStep } from '../../src/app/interact/identity-ops'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId, WireId } from '../../src/kernel/diagram/diagram'
import { IOTA } from '../../src/kernel/diagram/sig'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { Vec2 } from '../../src/view/vec'
import { farBlank, place, pointerSample } from './helpers/gesture'

/** Two wires meeting at an arity-2 dot at the root, each held by a pin. */
function dotJoined() {
  const builder = new DiagramBuilder()
  const dot = builder.identity(builder.root, IOTA, 2)
  const a = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
  const aPin = builder.pin(a, builder.root)
  const b = builder.wire([{ node: dot, port: { kind: 'identity', index: 1 } }])
  const bPin = builder.pin(b, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot, { x: 300, y: 300 })
  place(engine, aPin, { x: 100, y: 300 })
  place(engine, bPin, { x: 500, y: 300 })
  return { diagram, engine, dot, a, b, aPin, bPin }
}

type Committed = { readonly label: string; readonly steps: readonly ProofStep[] }

function harness(diagram: Diagram, engine: Engine, claimEndDiscs = false) {
  const committed: Committed[] = []
  const refusals: string[] = []
  let current = diagram
  const controller = new IdentityOpsController({
    active: () => true,
    engine: () => engine,
    diagram: () => current,
    viewScale: () => 1,
    theme: () => LIGHT,
    claimEndDiscs,
    commit: (label, steps) => {
      try {
        current = applyAction(current, { label, steps, placements: [] }, EMPTY_PROOF_CONTEXT, 'forward')
      } catch (error) {
        refusals.push(error instanceof Error ? error.message : String(error))
        return false
      }
      committed.push({ label, steps })
      return true
    },
    refuse: (text) => { refusals.push(text) },
  })
  return { controller, committed, refusals, diagram: () => current }
}

function drag(controller: IdentityOpsController, from: Vec2, to: Vec2): void {
  const claim = controller.claim(pointerSample(from))
  expect(claim).not.toBeNull()
  claim!.move(pointerSample(to))
  claim!.release(pointerSample(to), true)
}

describe('collapse: dot dragged into open space', () => {
  it('commits identification collapse; the dot survives as an arity-1 pin on one wire', () => {
    const { diagram, engine, dot } = dotJoined()
    const h = harness(diagram, engine)
    drag(h.controller, { x: 300, y: 300 }, farBlank())
    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    const step = h.committed[0]!.steps[0]!
    expect(step).toMatchObject({ rule: 'identification', input: { kind: 'collapse', node: dot } })
    const after = h.diagram()
    expect(Object.keys(after.wires)).toHaveLength(1)
    const node = after.nodes[dot]
    expect(node).toMatchObject({ kind: 'identity', arity: 1 })
  })
})

describe('applyIdentitySteps (edit-mode committer)', () => {
  it('applies a collapse step directly and refuses non-identity steps', () => {
    const { diagram, dot } = dotJoined()
    const after = applyIdentitySteps(diagram, [collapseStep(diagram, dot)])
    expect(Object.keys(after.wires)).toHaveLength(1)
    expect(() => applyIdentitySteps(diagram, [{ rule: 'doubleCutElim', region: diagram.root } as ProofStep]))
      .toThrow(/not an identity-rule step/)
  })
})
```

- [ ] **Step 2: Run to verify failure**

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts`
Expected: FAIL — module does not exist.

- [ ] **Step 3: Implement identity-ops.ts** per the interface block above (grab recognizer, collapse drop row, refusal rows for the not-yet-built grabs, overlay, applyIdentitySteps, collapseStep).

- [ ] **Step 4: Run to verify pass**

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts`
Expected: PASS.

- [ ] **Step 5: Wire into both modes** (moves.ts and construct.ts as specified) and verify nothing regressed:

Run: `npx tsc --noEmit && npx vitest run --config vitest.config.ts tests/app/moves.test.ts tests/app/wire-ops.test.ts tests/app/edit.test.ts tests/app/connection.test.ts tests/app/viewport-proof-moves.test.ts`
Expected: PASS. If a wire-ops test grabbed an identity leg expecting a strand grab, the claim-order change breaks it — update that test to grab a genuine strand point (mid-wire), since leg grabs are now identity vocabulary.

- [ ] **Step 6: Commit**

```bash
git add src/app/interact/identity-ops.ts src/app/interact/moves.ts src/app/interact/construct.ts tests/app/identity-ops.test.ts tests/app/wire-ops.test.ts
git commit -m "feat: identity dot drag-off collapses — shared identity-ops controller in both modes"
```

---

### Task 5: Fuse — dot dragged onto another dot

**Files:**
- Modify: `src/app/interact/identity-ops.ts`
- Test: `tests/app/identity-ops.test.ts`

**Interfaces:**
- Consumes: `IdentityGrab`, `identityDiscAt`, the `dot` drop dispatch from Task 4.
- Produces: `fuseStep(d: Diagram, a: NodeId, b: NodeId): ProofStep` (exported for tests) building

```ts
function portWires(d: Diagram, node: NodeId): WireId[] {
  // ordered by identity port index; one entry per port (multiplicity preserved)
  const out: [number, WireId][] = []
  for (const [wireId, wire] of Object.entries(d.wires)) {
    for (const ep of wire.endpoints) {
      if (ep.node === node && ep.port.kind === 'identity') out.push([ep.port.index, wireId])
    }
  }
  return out.sort(([i], [j]) => i - j).map(([, w]) => w)
}

export function fuseStep(d: Diagram, a: NodeId, b: NodeId): ProofStep {
  const region = (d.nodes[a] as IdentityDiagramNode).region
  return {
    rule: 'presentation',
    input: {
      region,
      removeNodes: [a, b],
      addNodes: { dot: [...portWires(d, a), ...portWires(d, b)] },
    },
  }
}
```

The kernel refuses mismatched regions/sigs with its own message (identity-rules.ts:333-351) — surface it, never pre-check.

**Steps:**

- [ ] **Step 1: Failing test** — extend the fixture: two arity-2 dots bridged by a shared wire (`a—●1—c—●2—b`): build wires `a` (pin + ●1 port), `c` (●1 port + ●2 port), `b` (●2 port + pin). Drag ●1's center onto ●2's center. Assert: one committed `presentation` step; after it exactly one identity node exists, with arity 4, and the wire set is unchanged (`a`, `b`, `c` all present).

Also a refusal case: two dots in *different regions* (put ●2 inside `builder.cut(builder.root)`), drag one onto the other, assert `refusals` has one entry matching `/homed at/`.

- [ ] **Step 2: Run — FAIL** (`drop on a dot` currently refuses with the collapse/fuse message).

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts -t fuse`

- [ ] **Step 3: Implement** — in the `dot` drop dispatch, before the open-space check: `const target = identityDiscAt(engine, point)`; if `target !== null && target !== grab.node`, commit `('presentation', [fuseStep(diagram, grab.node, target)])`.

- [ ] **Step 4: Run — PASS.** Same command.

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/identity-ops.ts tests/app/identity-ops.test.ts
git commit -m "feat: dot-onto-dot fuses identity nodes"
```

---

### Task 6: Stub grow — dot rim pulled into open space

**Files:**
- Modify: `src/app/interact/identity-ops.ts`
- Test: `tests/app/identity-ops.test.ts`

**Interfaces:**
- Produces: the `dotRim` drop row. Step:

```ts
{
  rule: 'vacuity',
  direction: 'insert',
  instance: { kind: 'stub', base: grab.node, wire: 'w', end: 'w_end', region: dropRegion },
}
```

`dropRegion = regionAt(engine, diagram, sample.world)` (import `regionAt` from '../hittest'). Fresh ids are mint labels — the kernel freshens deterministically (identity-rules.ts:33-39). The kernel enforces at-or-under (identity-rules.ts:170-177); refusal surfaces verbatim.

**Steps:**

- [ ] **Step 1: Failing test** — from the `dotJoined` fixture, compute a rim point of the dot: `const body = engine.bodies.get(dot)!; const rim = { x: body.pos.x + body.discR * engine.scale, y: body.pos.y }`. Drag `rim → farBlank()`. Assert one committed vacuity-insert stub step with `base: dot`; after it the dot's arity is 3 and a new wire exists whose two endpoints are the dot and a fresh arity-1 node. Refusal case: place a second fixture where the drop lands inside a cut *above* nothing — instead use a dot homed inside a cut and drop at the root; assert one refusal matching `/not\s.*at-or-under|gated quantifier movement/` (copy the kernel's actual message fragment after observing it once).

- [ ] **Step 2: Run — FAIL** (rim drop currently refuses with the stub placeholder message).

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts -t stub`

- [ ] **Step 3: Implement** the `dotRim` drop row: open space (no manipulation/disc hits) → commit the stub step; anything else → `refuse('pull the stub into open space', sample.client)`.

- [ ] **Step 4: Run — PASS.**

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/identity-ops.ts tests/app/identity-ops.test.ts
git commit -m "feat: dot rim-pull grows a vacuity stub"
```

---

### Task 7: Expose — a wire's end dragged onto its dot

Proof mode: rows in `WireOpsDragController` (it owns end/port grabs there). Edit mode: the `endDisc` grab in `IdentityOpsController` (enabled by `claimEndDiscs: true`, already wired in Task 4).

**Files:**
- Modify: `src/app/interact/identity-ops.ts` (export `exposeStep`; implement the `endDisc` drop row)
- Modify: `src/app/interact/wire-ops.ts` (two drop rows)
- Test: `tests/app/identity-ops.test.ts`, `tests/app/wire-ops.test.ts`

**Interfaces:**
- Produces:

```ts
// identity-ops.ts
export function exposeStep(d: Diagram, dot: NodeId, wire: WireId, transfer: Endpoint): ProofStep {
  return {
    rule: 'identification',
    input: { kind: 'expose', node: dot, survivor: wire, freshWire: 'w', transfer: [transfer] },
  }
}
```

- Proof rows in wire-ops `#drop`:
  - `case 'end'`: before the final refuse, `const dot = identityDiscAt(engine, point)`; if `dot !== null` and `diagram.wires[grab.wire]!.endpoints.some((ep) => ep.node === dot)`, commit `('identification', exposeStep(diagram, dot, grab.wire, { node: grab.node, port: { kind: 'head' } }))`. Extend the end-drop refusal text to name the dot option: `'release on a parallel end, an own argument port, an identity dot on this wire, or open space'`.
  - `case 'port'`: before the off-node removal fallback (arityUnshift/argDrop), same check; transfer is `{ node: grab.node, port: { kind: 'arg', index: grab.position } }`.
- Edit row in identity-ops `#drop` for `endDisc`: identical check; transfer is the head endpoint `{ node: grab.node, port: { kind: 'head' } }`; otherwise `refuse('release on an identity dot on this wire to expose', sample.client)`.
- The dragged-end-is-a-pin case never reaches expose: a pin is an identity disc, so its press is a `dot` grab and dot-onto-dot is fuse (spec precedence ruling). No code needed — but the test asserts it.

**Steps:**

- [ ] **Step 1: Failing tests.**

In identity-ops.test.ts (edit-mode path — `claimEndDiscs: true`): fixture = one BINARY-atom wire as in wire-ops `pluming()`, plus `builder.pin(wire, builder.root)` making the dot; place atom at (300,300), pin-dot at (300,80). Drag the atom's disc center onto the dot. Assert one committed identification-expose step with `survivor` = the head wire and `transfer` = the atom's head endpoint; after it two wires exist and the dot has arity 2.

Precedence case: drag one pin of a two-pin bare segment onto a dot on the same wire → asserted committed step is `presentation` (fuse), never expose.

In wire-ops.test.ts (proof path): same fixture through its existing `harness`; drag atom center → dot; assert the committed step matches `{ rule: 'identification', input: { kind: 'expose' } }`. And an arg-port case: drag an arg port anchor (`port(0)` per the pluming pattern) onto a dot attached to that arg wire; assert expose with the arg endpoint in `transfer`.

- [ ] **Step 2: Run — FAIL.**

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts tests/app/wire-ops.test.ts -t expose`

- [ ] **Step 3: Implement** the three rows as specified.

- [ ] **Step 4: Run — PASS** (full both files, not just -t expose, to catch drop-table regressions).

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/identity-ops.ts src/app/interact/wire-ops.ts tests/app/identity-ops.test.ts tests/app/wire-ops.test.ts
git commit -m "feat: end-onto-dot exposes an endpoint onto a fresh equated wire"
```

---

### Task 8: Leg drops — fission, duplicate, contract

**Files:**
- Modify: `src/app/interact/identity-ops.ts`
- Test: `tests/app/identity-ops.test.ts`

**Interfaces:**
- Produces (exported for tests):

```ts
export function fissionStep(d: Diagram, node: NodeId, dragged: WireId, bridge: WireId): ProofStep {
  const region = (d.nodes[node] as IdentityDiagramNode).region
  const ports = portWires(d, node)
  return {
    rule: 'presentation',
    input: {
      region,
      removeNodes: [node],
      addNodes: {
        [`${node}_a`]: [dragged, bridge],
        [`${node}_b`]: ports.filter((w) => w !== dragged),
      },
    },
  }
}

export function duplicateStep(d: Diagram, node: NodeId, wire: WireId): ProofStep {
  const region = (d.nodes[node] as IdentityDiagramNode).region
  return {
    rule: 'presentation',
    input: { region, removeNodes: [node], addNodes: { [node]: [...portWires(d, node), wire] } },
  }
}

export function contractStep(d: Diagram, node: NodeId, wire: WireId): ProofStep {
  const region = (d.nodes[node] as IdentityDiagramNode).region
  const ports = portWires(d, node)
  const drop = ports.indexOf(wire)
  return {
    rule: 'presentation',
    input: { region, removeNodes: [node], addNodes: { [node]: ports.filter((_, i) => i !== drop) } },
  }
}
```

(`addNodes` keys are mint labels; `freshId` renames on collision, so reusing the node's own label is safe and keeps ids stable-looking.)

- Drop dispatch for `grab.kind === 'leg'`:
  1. Resolve the drop: `wireManipulationHitTest` endpoint hit with `port.kind === 'identity'` and `endpoint.node === grab.node` → a target leg `{ wire: hit.wire }`. Same wire as `grab.wire` → **contract** (guard: the wire must hold ≥2 ports on the dot — `portWires` count — else refuse `'only a doubled leg contracts'`); different wire → **fission** (`dragged = grab.wire`, `bridge = target wire`).
  2. Else if the drop point is inside `grab.node`'s own disc (`identityDiscAt(engine, point) === grab.node`) → **duplicate**.
  3. Else `refuse('release on the dot to duplicate, or on one of its other legs', sample.client)`.

**Steps:**

- [ ] **Step 1: Failing tests.** Fixture: three-wire dot (`dotJoined` generalized to arity 3, pins at (100,300), (500,300), (300,540); dot at (300,300)).
  - *Fission:* compute the leg grab point for wire `a` via `endpointPoint(engine, a, { node: dot, port: { kind: 'identity', index: 0 } })`; drag it onto wire `c`'s leg point. Assert one `presentation` step; after it two identity nodes exist: one with port-wires `[a, c]`, one with `[b, c]` (order-insensitive set assertions); wire set unchanged.
  - *Duplicate:* drag wire `a`'s leg point onto the dot center. Assert after: one identity node, arity 4, `a` holding two ports on it.
  - *Contract:* start from a built fixture where `a` holds two ports on the dot (`builder.wire([{node: dot, port:{kind:'identity',index:0}}, {node: dot, port:{kind:'identity',index:1}}])`); drag one of `a`'s leg points onto the other. Assert after: arity down by one, `a` holding one port.

- [ ] **Step 2: Run — FAIL.**

Run: `npx vitest run --config vitest.config.ts tests/app/identity-ops.test.ts -t 'fission|duplicate|contract'`

- [ ] **Step 3: Implement** the leg drop dispatch and the three step builders.

- [ ] **Step 4: Run — PASS** (whole file).

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/identity-ops.ts tests/app/identity-ops.test.ts
git commit -m "feat: leg drags — fission with drawn bridge, duplicate, contract"
```

---

### Task 9: Q over a strand pins; Q reaches edit mode

**Files:**
- Modify: `src/app/interact/moves.ts` (Q branch: strand-aware)
- Modify: `src/app/interact/construct.ts` (Q handling + `passiveSample`)
- Modify: `src/app/edit.ts` (`addRelationWire` sig parameter widened `RelSig` → `Sig`)
- Modify: `src/app/shell.ts` (feed `passiveSample` to the construct controller alongside proofMoves — see shell.ts:1596)
- Test: `tests/app/moves.test.ts`, `tests/app/edit.test.ts`

**Interfaces:**
- Proof Q dispatch (moves.ts, inside the existing `sample.key === 'q'` branch, before the bare-wire commit):

```ts
const world = this.#lastWorld
const manipulation = wireManipulationHitTest(
  this.#options.engine(), world, { scale: this.#options.viewScale() },
)
if (manipulation !== null) {
  this.#commitSteps('vacuity', [{
    rule: 'vacuity',
    direction: 'insert',
    instance: {
      kind: 'pin',
      wire: manipulation.wire,
      node: 'pin',
      region: regionAt(this.#options.engine(), this.#options.diagram(), world),
    },
  }])
  return true
}
// existing bare-wire commit follows unchanged
```

(`viewScale` is already an option of `ProofMoveControllerOptions`.) Shift is ignored over a strand — a pin's sig is the wire's sig.

- Edit Q (construct.ts `keyDown`): add a `#lastWorld: Vec2 | null` + `passiveSample(sample: PointerSample | null): void` mirroring moves.ts:192-199. Q dispatch: strand under pointer → `#tryCommit(() => applyIdentitySteps(d, [pin step as above]), 'pinned')`; blank → `#tryCommit(() => addRelationWire(d, region, sample.shiftKey ? relSig([]) : IOTA).diagram, 'bare line drawn')`; no pointer → `refuse('point at a region first')`.
- edit.ts: `addRelationWire(d, region, sig: Sig)` — the body only stores the sig; widen the parameter type and update its doc line. Callers pass `RelSig` today (construct.ts:336) and keep compiling.
- shell.ts: the viewport's `passiveSample` callback currently forwards only to `proofMoves`; forward to both controllers (each ignores samples while inactive).

**Steps:**

- [ ] **Step 1: Failing tests.**
  - moves.test.ts (add `spread` to the `./helpers/build` import):

```ts
it('Q over a strand pins the wire at the hovered region', () => {
  const builder = new DiagramBuilder()
  const seg = segment(builder, builder.root)
  const diagram = builder.build()
  const { moves, engine, applied } = harness(diagram)
  const mid = spread(engine, seg, { x: 300, y: 300 })
  moves.passiveSample(pointerSample(mid))
  expect(moves.keyDown(keySample('q'))).toBe(true)
  expect(applied).toHaveLength(1)
  expect(applied[0]!.steps[0]).toMatchObject({
    rule: 'vacuity',
    direction: 'insert',
    instance: { kind: 'pin', wire: seg.wire, region: diagram.root },
  })
})
```

  The existing blank-Q tests (moves.test.ts:172,193) must stay green — blank means no wire manipulation hit at the pointer.
  - edit.test.ts, unit-level: `addRelationWire(diagram, builder.root, IOTA)` builds an IOTA segment with two arity-1 identity ends (before the type widening this does not compile — that is the failing state). Then a controller-level Q test: build a `ConstructController` harness in edit.test.ts mirroring the option shape visible in construct.ts (`active/engine/diagram/viewScale/theme/selection/commit/refuse/openSpawn`, commit records the next `Diagram`); drive `construct.passiveSample(pointerSample(mid))` then `construct.keyDown(keySample('q'))` over a strand and assert the committed diagram gained one arity-1 identity node on `seg.wire`; over blank, assert it gained a fresh two-pin segment.

- [ ] **Step 2: Run — FAIL.**

Run: `npx tsc --noEmit; npx vitest run --config vitest.config.ts tests/app/moves.test.ts tests/app/edit.test.ts`

- [ ] **Step 3: Implement** the four file changes.

- [ ] **Step 4: Run — PASS**, plus `npx tsc --noEmit` clean.

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/moves.ts src/app/interact/construct.ts src/app/edit.ts src/app/shell.ts tests/app/moves.test.ts tests/app/edit.test.ts
git commit -m "feat: Q over a strand pins the wire; Q spawns in edit mode"
```

---

### Task 10: Contextual Delete — shape-determined vacuity deletes

**Files:**
- Modify: `src/app/interact/moves.ts` (Delete branch, before discovery — alongside the existing lone-wire `endsDelete` dispatch at moves.ts:344-353)
- Test: `tests/app/moves.test.ts`

**Interfaces:** new dispatch when the selection is exactly one **node** hit and that node is an identity node:

```ts
const node = diagram.nodes[hit.id]
if (node?.kind === 'identity') {
  if (node.arity === 0) {
    this.#commit({
      rule: 'vacuity', direction: 'delete',
      instance: { kind: 'point', node: hit.id, region: node.region, sig: node.sig },
    })
    return true
  }
  if (node.arity === 1) {
    const [wireId, wire] = Object.entries(diagram.wires)
      .find(([, w]) => w.endpoints.some((ep) => ep.node === hit.id))!
    const other = wire.endpoints.find((ep) => ep.node !== hit.id)
    const stubShaped = wire.endpoints.length === 2
      && other !== undefined
      && diagram.nodes[other.node]?.kind === 'identity'
    this.#commit(stubShaped
      ? {
          rule: 'vacuity', direction: 'delete',
          instance: { kind: 'stub', base: other.node, wire: wireId, end: hit.id, region: node.region },
        }
      : {
          rule: 'vacuity', direction: 'delete',
          instance: { kind: 'pin', wire: wireId, node: hit.id, region: node.region },
        })
    return true
  }
  // arity ≥ 2 falls through: an in-path dot is content, handled by discovery (erase, …)
}
```

The dispatch is shape-determined, not a fallback chain: a 2-end wire whose other end is an identity node *is* a stub (detach is impossible there — two-end floor), everything else is a detach attempt, and load-bearing pins are the kernel's refusal (identity-rules.ts:288-296), surfaced verbatim.

**Steps:**

- [ ] **Step 1: Failing tests** (moves.test.ts; selection hits are `{ kind: 'node', id }`):

```ts
it('Delete on one pin of a bare segment retracts the stub, leaving the lone point', () => {
  const builder = new DiagramBuilder()
  const seg = segment(builder, builder.root)
  const diagram = builder.build()
  const { moves, applied } = harness(diagram, [{ kind: 'node', id: seg.ends[0] }])
  expect(moves.keyDown(keySample('Delete'))).toBe(true)
  expect(applied).toHaveLength(1)
  expect(applied[0]!.steps[0]).toMatchObject({
    rule: 'vacuity',
    direction: 'delete',
    instance: { kind: 'stub', wire: seg.wire, end: seg.ends[0], base: seg.ends[1] },
  })
})

it('Delete on a spare pin of a three-ended wire detaches it', () => {
  const builder = new DiagramBuilder()
  const seg = segment(builder, builder.root)
  const spare = builder.pin(seg.wire, builder.root)
  const diagram = builder.build()
  const { moves, applied } = harness(diagram, [{ kind: 'node', id: spare }])
  expect(moves.keyDown(keySample('Delete'))).toBe(true)
  expect(applied[0]!.steps[0]).toMatchObject({
    rule: 'vacuity',
    direction: 'delete',
    instance: { kind: 'pin', wire: seg.wire, node: spare },
  })
})

it('Delete on a load-bearing pin surfaces the kernel refusal', () => {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const seg = segment(builder, cut)          // two ends inside the cut
  const root = builder.pin(seg.wire, builder.root)  // scope-holding root pin
  const diagram = builder.build()
  const { moves, applied, refusals } = harness(diagram, [{ kind: 'node', id: root }])
  expect(moves.keyDown(keySample('Delete'))).toBe(true)
  expect(applied).toHaveLength(0)
  expect(refusals.some((text) => /load-bearing/.test(text))).toBe(true)
})

it('Delete on a lone point deletes it as vacuity', () => {
  const builder = new DiagramBuilder()
  const point = builder.point(builder.root)
  const diagram = builder.build()
  const { moves, applied } = harness(diagram, [{ kind: 'node', id: point }])
  expect(moves.keyDown(keySample('Delete'))).toBe(true)
  expect(applied[0]!.steps[0]).toMatchObject({
    rule: 'vacuity',
    direction: 'delete',
    instance: { kind: 'point', node: point, region: diagram.root },
  })
})
```

Caution on the refusal test: the moves harness `apply` only records — it never runs the kernel. For the refusal to surface, this one test must apply the step (mirror the identity-ops harness: run `applyAction` inside `apply` and push failures to `refusals`), or the assertion belongs on the thrown `applyAction` in a kernel-direct expectation. Use the applyAction-in-apply variant so the spring-back path itself is exercised.

- [ ] **Step 2: Run — FAIL** (Delete on a node hit currently falls to discovery and refuses or erases).

Run: `npx vitest run --config vitest.config.ts tests/app/moves.test.ts -t 'vacuity delete|stub retract|pin detach|load-bearing'`

- [ ] **Step 3: Implement** the dispatch.

- [ ] **Step 4: Run — PASS** (whole moves.test.ts).

- [ ] **Step 5: Commit**

```bash
git add src/app/interact/moves.ts tests/app/moves.test.ts
git commit -m "feat: Delete on a dot reads as the vacuity shape it names"
```

---

### Task 11: Final verification sweep

**Files:** none new — this is verification and any fallout it forces.

- [ ] **Step 1: Whole-project type check.** Run: `npx tsc --noEmit`. Expected: 0 errors.
- [ ] **Step 2: Ordinary suite.** Run: `npx vitest run --config vitest.config.ts`. Expected: all green. Fix every failure before proceeding — a failure is never reported as informational. (Never run `test:physics` / `test:all`.)
- [ ] **Step 3: Frege replay guard.** Run the theories tests (they replay recorded proofs on the kernel): `npx vitest run --config vitest.config.ts tests/theories`. Expected: green — proves the UI changes never touched replay semantics.
- [ ] **Step 4: Commit any fallout fixes** (scoped adds), then confirm `git status` shows only the peer session's `VisualProof/` files as untouched noise.
