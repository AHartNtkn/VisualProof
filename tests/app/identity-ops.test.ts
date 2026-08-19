import { describe, expect, it } from 'vitest'
import { IdentityOpsController, applyIdentitySteps, collapseStep } from '../../src/app/interact/identity-ops'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
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
