import { describe, expect, it } from 'vitest'
import { IdentityOpsController, applyIdentitySteps, collapseStep, fuseStep } from '../../src/app/interact/identity-ops'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { IOTA } from '../../src/kernel/diagram/sig'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { Vec2 } from '../../src/view/vec'
import { farBlank, place, placeRegion, pointerSample } from './helpers/gesture'

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

/** Two arity-2 dots bridged by a shared wire: `a—●1—c—●2—b`, each outer end
    held by a pin at `root`. */
function bridgedDots() {
  const builder = new DiagramBuilder()
  const dot1 = builder.identity(builder.root, IOTA, 2)
  const dot2 = builder.identity(builder.root, IOTA, 2)
  const a = builder.wire([{ node: dot1, port: { kind: 'identity', index: 0 } }])
  const aPin = builder.pin(a, builder.root)
  const c = builder.wire([
    { node: dot1, port: { kind: 'identity', index: 1 } },
    { node: dot2, port: { kind: 'identity', index: 0 } },
  ])
  const b = builder.wire([{ node: dot2, port: { kind: 'identity', index: 1 } }])
  const bPin = builder.pin(b, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot1, { x: 300, y: 300 })
  place(engine, dot2, { x: 500, y: 300 })
  place(engine, aPin, { x: 100, y: 300 })
  place(engine, bPin, { x: 700, y: 300 })
  return { diagram, engine, dot1, dot2, a, b, c, aPin, bPin }
}

/** Same shape as `bridgedDots`, but ●2 is homed inside a cut — fusing across
    regions must refuse. */
function bridgedDotsAcrossRegions() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const dot1 = builder.identity(builder.root, IOTA, 2)
  const dot2 = builder.identity(cut, IOTA, 2)
  const a = builder.wire([{ node: dot1, port: { kind: 'identity', index: 0 } }])
  const aPin = builder.pin(a, builder.root)
  builder.wire([
    { node: dot1, port: { kind: 'identity', index: 1 } },
    { node: dot2, port: { kind: 'identity', index: 0 } },
  ])
  const b = builder.wire([{ node: dot2, port: { kind: 'identity', index: 1 } }])
  const bPin = builder.pin(b, cut)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot1, { x: 300, y: 300 })
  place(engine, dot2, { x: 500, y: 300 })
  place(engine, aPin, { x: 100, y: 300 })
  place(engine, bPin, { x: 700, y: 300 })
  return { diagram, engine, dot1, dot2 }
}

/** An arity-1 dot homed inside a cut, held by a pin at the cut — the cut's
    engine region circle sits close around the dot so a far drop resolves
    (via `regionAt`'s fallback) to the diagram's root, above the cut. */
function dotInCut() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const dot = builder.identity(cut, IOTA, 1)
  const w = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
  const pin = builder.pin(w, cut)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot, { x: 300, y: 300 })
  place(engine, pin, { x: 500, y: 300 })
  placeRegion(engine, cut, { x: 300, y: 300 }, 100)
  return { diagram, engine, dot, cut }
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

describe('fuse: dot dragged onto another dot', () => {
  it('commits a presentation step that replaces both dots with one arity-4 node over the same wires', () => {
    const { diagram, engine, dot1, dot2, a, b, c } = bridgedDots()
    const h = harness(diagram, engine)
    drag(h.controller, { x: 300, y: 300 }, { x: 500, y: 300 })
    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    expect(h.committed[0]!.steps).toEqual([fuseStep(diagram, dot1, dot2)])
    const after = h.diagram()
    expect(after.nodes[dot1]).toBeUndefined()
    expect(after.nodes[dot2]).toBeUndefined()
    expect(Object.keys(after.wires).sort()).toEqual([a, b, c].sort())
    const fused = Object.values(after.nodes).filter((n) => n.kind === 'identity' && n.arity === 4)
    expect(fused).toHaveLength(1)
  })

  it('refuses when the dots are homed at different regions', () => {
    const { diagram, engine } = bridgedDotsAcrossRegions()
    const h = harness(diagram, engine)
    drag(h.controller, { x: 300, y: 300 }, { x: 500, y: 300 })
    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.refusals[0]).toMatch(/homed at/)
  })
})

describe('stub: dot rim pulled into open space', () => {
  it('commits a vacuity-insert stub step: the dot gains a port and a fresh wire runs to a fresh arity-1 node', () => {
    const { diagram, engine, dot, a, b } = dotJoined()
    const h = harness(diagram, engine)
    const body = engine.bodies.get(dot)!
    const rim = { x: body.pos.x + body.discR * engine.scale, y: body.pos.y }
    drag(h.controller, rim, farBlank())
    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    const step = h.committed[0]!.steps[0]!
    expect(step).toMatchObject({ rule: 'vacuity', direction: 'insert', instance: { kind: 'stub', base: dot } })
    const after = h.diagram()
    expect(after.nodes[dot]).toMatchObject({ kind: 'identity', arity: 3 })
    const stubWire = Object.keys(after.wires).find((id) => id !== a && id !== b)
    expect(stubWire).toBeDefined()
    const endpoints = after.wires[stubWire!]!.endpoints
    expect(endpoints).toHaveLength(2)
    expect(endpoints.some((ep) => ep.node === dot)).toBe(true)
    const end = endpoints.find((ep) => ep.node !== dot)!.node
    expect(after.nodes[end]).toMatchObject({ kind: 'identity', arity: 1 })
  })

  it('refuses when the drop region is not at-or-under the dot\'s region', () => {
    const { diagram, engine, dot } = dotInCut()
    const h = harness(diagram, engine)
    const body = engine.bodies.get(dot)!
    const rim = { x: body.pos.x + body.discR * engine.scale, y: body.pos.y }
    drag(h.controller, rim, farBlank())
    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.refusals[0]).toMatch(/not.*at-or-under|gated quantifier movement/)
  })

  it('refuses a non-open-space drop with the placeholder message', () => {
    const { diagram, engine, dot } = dotJoined()
    const h = harness(diagram, engine)
    const body = engine.bodies.get(dot)!
    const rim = { x: body.pos.x + body.discR * engine.scale, y: body.pos.y }
    drag(h.controller, rim, { x: 300, y: 300 })
    expect(h.committed).toEqual([])
    expect(h.refusals).toEqual(['pull the stub into open space'])
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
