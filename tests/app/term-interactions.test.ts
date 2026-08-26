import { describe, expect, it } from 'vitest'
import { planCopy } from '../../src/app/copy-planner'
import {
  FissionDragController,
  fissionHit,
  fissionTargetPoint,
  type FissionRequest,
} from '../../src/app/interact/fission'
import { proofConnectionStep } from '../../src/app/interact/moves'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { wireAt } from '../../src/kernel/rules/access'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { application, bound, free, lambda } from '../../src/kernel/term/term'
import { recomputeRegions } from '../../src/view'
import { localToWorld, mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { polar } from '../../src/view/vec'

function pointer(
  world: { readonly x: number; readonly y: number },
  node: string,
): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: world,
    screen: world,
    world,
    hit: { kind: 'node', id: node },
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

describe('term interaction surface', () => {
  it('selects a nested painted term occurrence by its semantic path', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(free(0), application(lambda(bound(0)), free(1))),
    )
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const body = engine.bodies.get(node)!
    const occurrence = body.geometry!.occurrences.find((item) =>
      item.path.join('/') === 'argument')!
    const point = occurrence.hit.kind === 'arcPoint'
      ? localToWorld(engine, body, occurrence.hit.point)
      : occurrence.hit.kind === 'exit'
        ? localToWorld(engine, body, body.geometry!.exitLine![0])
        : (() => {
            const radial = body.geometry!.radials[occurrence.hit.radialIndex]!
            return localToWorld(engine, body, polar(radial.angle, (radial.r0 + radial.r1) / 2))
          })()
    expect(fissionHit(engine, diagram, point, 1)?.path).toEqual(['argument'])
  })

  it('previews and commits an outward drag of the selected whole subterm', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(free(0), application(lambda(bound(0)), free(1))),
    )
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    recomputeRegions(engine)
    const startPoint = fissionTargetPoint(engine, node, ['argument'])!
    const body = engine.bodies.get(node)!
    const destination = {
      x: body.pos.x + body.discR * engine.scale + 8,
      y: body.pos.y,
    }
    const committed: FissionRequest[] = []
    const refused: string[] = []
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: (message) => { refused.push(message) },
    })

    const claim = controller.claim(pointer(startPoint, node))!
    claim.move(pointer(destination, node))
    expect(controller.overlay().length).toBeGreaterThan(0)
    claim.release(pointer(destination, node), true)

    expect(refused).toEqual([])
    expect(committed).toEqual([{
      node,
      path: ['argument'],
      at: destination,
    }])
  })

  it('copies a whole term node with every output and free-slot incidence', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(builder.root, application(free(0), free(1)))
    const diagram = builder.build()
    const ports = [
      { kind: 'output' as const },
      { kind: 'free' as const, index: 0 },
      { kind: 'free' as const, index: 1 },
    ]
    const holders = ports.map((port) => wireAt(diagram, node, port))
    const plan = planCopy(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    }), {
      kind: 'edit',
      diagram,
      region: diagram.root,
      at: { x: 10, y: 20 },
    })
    expect(plan.kind).toBe('edit')
    if (plan.kind !== 'edit') throw new Error('expected an edit copy plan')
    for (const holder of holders) {
      expect(plan.result.wires[holder]!.endpoints.length)
        .toBe(diagram.wires[holder]!.endpoints.length + 1)
    }
  })

  it('resolves convertible term outputs to a dedicated Lambda congruence step', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, free(0))
    const right = builder.term(builder.root, free(0))
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    const diagram = builder.build()
    const leftWire = wireAt(diagram, left, { kind: 'output' })
    const rightWire = wireAt(diagram, right, { kind: 'output' })
    expect(proofConnectionStep(
      diagram,
      { wire: leftWire, endpoint: { node: left, port: { kind: 'output' } } },
      { wire: rightWire, endpoint: { node: right, port: { kind: 'output' } } },
      'forward',
      64,
    )).toMatchObject({ rule: 'lambdaCongruenceJoin', a: left, b: right })
  })

  it('resolves host-equivalent aliased interfaces through one carrier column', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, application(free(0), free(1)), 2)
    const right = builder.term(builder.root, application(free(0), free(0)), 1)
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: left, port: { kind: 'free', index: 1 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    const diagram = builder.build()
    const step = proofConnectionStep(
      diagram,
      {
        wire: wireAt(diagram, left, { kind: 'output' }),
        endpoint: { node: left, port: { kind: 'output' } },
      },
      {
        wire: wireAt(diagram, right, { kind: 'output' }),
        endpoint: { node: right, port: { kind: 'output' } },
      },
      'forward',
      64,
    )

    expect(step).toMatchObject({
      rule: 'lambdaCongruenceJoin',
      correspondence: { commonArity: 1, left: [0, 0], right: [0] },
    })
  })

  it('connects two term free-slot wires through the proof wire join', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.term(cut, free(0))
    const right = builder.term(cut, free(0))
    const diagram = builder.build()
    const leftEndpoint = { node: left, port: { kind: 'free' as const, index: 0 } }
    const rightEndpoint = { node: right, port: { kind: 'free' as const, index: 0 } }
    expect(proofConnectionStep(
      diagram,
      { wire: wireAt(diagram, left, leftEndpoint.port), endpoint: leftEndpoint },
      { wire: wireAt(diagram, right, rightEndpoint.port), endpoint: rightEndpoint },
      'forward',
      64,
    )).toEqual({
      rule: 'wireJoin',
      input: {
        a: wireAt(diagram, left, leftEndpoint.port),
        b: wireAt(diagram, right, rightEndpoint.port),
      },
    })
  })
})
