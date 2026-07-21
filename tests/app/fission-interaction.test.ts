import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine, localToWorld } from '../../src/view/engine'
import { recomputeRegions } from '../../src/view'
import { polar } from '../../src/view/vec'
import { LIGHT } from '../../src/view/paint'
import {
  FissionDragController,
  fissionHit,
  type FissionRequest,
} from '../../src/app/interact/fission'
import type { PointerSample } from '../../src/app/interact/viewport'
import { ConstructController } from '../../src/app/interact/construct'
import { ProofMoveController } from '../../src/app/interact/moves'
import { wireHitTest } from '../../src/app/hittest'
import { applyFission, applyFusion } from '../../src/kernel/rules/fusion'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'

const p = (source: string) => parseTerm(source)

function fixture(source = 'a ((\\x. x) b)') {
  const builder = new DiagramBuilder()
  const node = builder.termNode(builder.root, p(source))
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.bodies.get(node)!.pos = { x: 0, y: 0 }
  recomputeRegions(engine)
  const pointFor = (path: readonly string[]) => {
    const body = engine.bodies.get(node)!
    const occurrence = body.geometry!.occurrences.find((candidate) =>
      candidate.path.length === path.length && candidate.path.every((segment, index) => segment === path[index]))!
    if (occurrence.hit.kind === 'arcPoint') return localToWorld(engine, body, occurrence.hit.point)
    if (occurrence.hit.kind === 'exit') {
      const [a, b] = body.geometry!.exitLine!
      return localToWorld(engine, body, { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 })
    }
    const radial = body.geometry!.radials[occurrence.hit.radialIndex]!
    return localToWorld(engine, body, polar(radial.angle, (radial.r0 + radial.r1) / 2))
  }
  return { builder, node, diagram, engine, pointFor }
}

const sample = (world: { x: number; y: number }, node: string, overrides: Partial<PointerSample> = {}): PointerSample => ({
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
  ...overrides,
})

describe('fission anatomy targeting', () => {
  it('resolves distinct nested and root occurrences from their painted carriers', () => {
    const f = fixture()
    expect(fissionHit(f.engine, f.diagram, f.pointFor(['arg']), 1)?.path).toEqual(['arg'])
    expect(fissionHit(f.engine, f.diagram, f.pointFor(['arg', 'fn']), 1)?.path).toEqual(['arg', 'fn'])
    expect(fissionHit(f.engine, f.diagram, f.pointFor([]), 1)?.path).toEqual([])
  })

  it('keeps the chosen binder-dependent occurrence and marks it invalid', () => {
    const f = fixture('\\x. x y')
    const target = fissionHit(f.engine, f.diagram, f.pointFor(['body']), 1)
    expect(target?.path).toEqual(['body'])
    expect(target?.valid).toBe(false)
    expect(target?.reason).toMatch(/references binders above/)
  })
})

describe('shared fission drag controller', () => {
  it('declines hover and claim while Ctrl is held', () => {
    const f = fixture()
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: () => {},
      refuse: () => {},
    })
    const at = sample(f.pointFor(['arg']), f.node, { ctrlKey: true })
    controller.hover(at)
    expect(controller.overlay()).toEqual([])
    expect(controller.claim(at)).toBeNull()
  })

  it('highlights only internal anatomy and commits the exact path after an outward drag', () => {
    const f = fixture()
    const committed: FissionRequest[] = []
    const refused: string[] = []
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: (text) => { refused.push(text) },
    })
    const start = sample(f.pointFor(['arg']), f.node)
    controller.hover(start)
    expect(controller.overlay().length).toBeGreaterThan(0)
    expect(controller.overlay().some((shape) => shape.kind === 'circle')).toBe(false)
    const claim = controller.claim(start)!
    const body = f.engine.bodies.get(f.node)!
    const destination = { x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }
    const end = sample(destination, f.node)
    claim.move(end)
    claim.release(end, true)

    expect(refused).toEqual([])
    expect(committed).toEqual([{ node: f.node, path: ['arg'], at: destination }])
    expect(controller.overlay()).toEqual([])
  })

  it('keeps a still press as selection and refuses a binder-invalid release', () => {
    const f = fixture('\\x. x y')
    const committed: FissionRequest[] = []
    const refused: string[] = []
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: (text) => { refused.push(text) },
    })
    const start = sample(f.pointFor(['body']), f.node)
    const still = controller.claim(start)!
    still.release(start, false)
    expect(committed).toEqual([])
    expect(refused).toEqual([])

    const drag = controller.claim(start)!
    const end = sample({ x: 20, y: 0 }, f.node)
    drag.move(end)
    drag.release(end, true)
    expect(committed).toEqual([])
    expect(refused.join(' ')).toMatch(/references binders above/)
  })

  it('invalidates a live claim on cancel, Ctrl, inactive mode, and disposal', () => {
    const f = fixture()
    const committed: FissionRequest[] = []
    let active = true
    const controller = new FissionDragController({
      active: () => active,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: () => {},
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const body = f.engine.bodies.get(f.node)!
    const destination = { x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }
    const end = sample(destination, f.node)
    const cancelledRelease = (cancel: () => void) => {
      const claim = controller.claim(start)!
      claim.move(end)
      cancel()
      claim.release(end, true)
    }

    cancelledRelease(() => { controller.cancel() })
    cancelledRelease(() => { controller.modifiersChanged(true); controller.modifiersChanged(false) })
    cancelledRelease(() => { active = false; controller.overlay(); active = true })
    cancelledRelease(() => { controller.dispose() })
    expect(committed).toEqual([])
  })

  it('revalidates a changed node/path and reports commit failures instead of throwing', () => {
    const f = fixture()
    let current = f.diagram
    let throwOnCommit = false
    const committed: FissionRequest[] = []
    const refused: string[] = []
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => current,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => {
        if (throwOnCommit) throw new Error('history rejected stale fission')
        committed.push(request)
      },
      refuse: (text) => { refused.push(text) },
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const body = f.engine.bodies.get(f.node)!
    const destination = { x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }
    const end = sample(destination, f.node)

    const stale = controller.claim(start)!
    stale.move(end)
    current = new DiagramBuilder().build()
    expect(() => controller.overlay()).not.toThrow()
    expect(() => stale.release(end, true)).not.toThrow()
    expect(committed).toEqual([])
    expect(refused.join(' ')).toMatch(/node|path|unknown/i)

    current = f.diagram
    throwOnCommit = true
    const rejected = controller.claim(start)!
    rejected.move(end)
    expect(() => rejected.release(end, true)).not.toThrow()
    expect(refused.join(' ')).toMatch(/history rejected stale fission/)
  })

  it('refuses in-body, outside-frame, and wrong-direct-region releases without committing', () => {
    const f = fixture()
    const committed: FissionRequest[] = []
    const refused: string[] = []
    const controller = new FissionDragController({
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: (text) => { refused.push(text) },
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const body = f.engine.bodies.get(f.node)!
    const releaseAt = (destination: { x: number; y: number }) => {
      const claim = controller.claim(start)!
      const end = sample(destination, f.node)
      claim.move(end)
      claim.release(end, true)
    }
    releaseAt(body.pos)
    f.engine.frame = { center: body.pos, half: body.discR * f.engine.scale + 1 }
    releaseAt({ x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y })

    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const node = builder.termNode(builder.root, p('a ((\\x. x) b)'))
    builder.termNode(cut, p('\\z. z'))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    recomputeRegions(engine)
    engine.bodies.get(node)!.pos = { x: 0, y: 0 }
    const cutGeometry = engine.regions.get(cut)!
    cutGeometry.center = { x: 30, y: 0 }
    cutGeometry.radius = 6
    const occurrence = engine.bodies.get(node)!.geometry!.occurrences.find((candidate) => candidate.path.join('/') === 'arg')!
    const radial = occurrence.hit.kind === 'radial' ? engine.bodies.get(node)!.geometry!.radials[occurrence.hit.radialIndex]! : null
    const wrongStart = occurrence.hit.kind === 'arcPoint'
      ? localToWorld(engine, engine.bodies.get(node)!, occurrence.hit.point)
      : occurrence.hit.kind === 'exit'
        ? localToWorld(engine, engine.bodies.get(node)!, engine.bodies.get(node)!.geometry!.exitLine![0])
        : localToWorld(engine, engine.bodies.get(node)!, polar(radial!.angle, (radial!.r0 + radial!.r1) / 2))
    const wrongRegion = new FissionDragController({
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (request) => { committed.push(request) },
      refuse: (text) => { refused.push(text) },
    })
    const wrongClaim = wrongRegion.claim(sample(wrongStart, node))!
    const wrongEnd = sample(cutGeometry.center, node)
    wrongClaim.move(wrongEnd)
    wrongClaim.release(wrongEnd, true)

    expect(committed).toEqual([])
    expect(refused.filter((text) => text.includes('current region'))).toHaveLength(3)
  })
})

describe('Edit fission integration', () => {
  it('preserves free-port wires and fuses back to the exact starting diagram', () => {
    const f = fixture()
    const beforeWires = Object.keys(f.diagram.wires)
    const split = applyFission(f.diagram, f.node, ['arg'])
    const producer = Object.keys(split.nodes).find((id) => f.diagram.nodes[id] === undefined)!
    const freshWire = Object.keys(split.wires).find((id) => f.diagram.wires[id] === undefined)!
    const migrated = beforeWires.filter((wire) => split.wires[wire]!.endpoints
      .some((endpoint) => endpoint.node === producer && endpoint.port.kind === 'freeVar'))
    expect(migrated.length).toBeGreaterThan(0)
    for (const wire of migrated) expect(f.diagram.wires[wire]!.endpoints.some((endpoint) => endpoint.node === f.node)).toBe(true)
    expect(applyFusion(split, freshWire)).toEqual(f.diagram)
  })

  it('routes an internal anatomy drag through the shared controller before node placement', () => {
    const f = fixture()
    const requests: FissionRequest[] = []
    const construct = new ConstructController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      engine: () => f.engine,
      viewScale: () => 1,
      diagram: () => f.diagram,
      selection: () => [{ kind: 'node', id: f.node }],
      setSelection: () => {},
      commit: () => {},
      commitFission: (request) => { requests.push(request) },
      refuse: (text) => { throw new Error(text) },
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const claim = construct.claim(start)
    expect(claim).not.toBeNull()
    const body = f.engine.bodies.get(f.node)!
    const destination = { x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }
    const end = sample(destination, f.node)
    claim!.move(end)
    claim!.release(end, true)
    expect(requests).toEqual([{ node: f.node, path: ['arg'], at: destination }])
  })

  it('Escape invalidates the active fission claim before pointer release', () => {
    const f = fixture()
    const requests: FissionRequest[] = []
    const construct = new ConstructController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      engine: () => f.engine,
      viewScale: () => 1,
      diagram: () => f.diagram,
      selection: () => [],
      setSelection: () => {},
      commit: () => {},
      commitFission: (request) => { requests.push(request) },
      refuse: () => {},
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const claim = construct.claim(start)!
    const body = f.engine.bodies.get(f.node)!
    const end = sample({ x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }, f.node)
    claim.move(end)
    expect(construct.keyDown({ key: 'Escape', shiftKey: false, ctrlKey: false, altKey: false, metaKey: false, repeat: false })).toBe(true)
    claim.release(end, true)
    expect(requests).toEqual([])
  })
})

describe('Proof fission integration', () => {
  it('routes internal anatomy to fission before selected-node iteration', () => {
    const f = fixture()
    const requests: FissionRequest[] = []
    const controller = new ProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      selection: () => [{ kind: 'node', id: f.node }],
      setSelection: () => {},
      context: () => (EMPTY_PROOF_CONTEXT),
      orientation: () => 'forward',
      apply: () => {},
      commitFission: (request) => { requests.push(request) },
      refuse: (text) => { throw new Error(text) },
      theme: () => LIGHT,
      fuel: () => 64,
      openComprehension: () => {},
      openAbstraction: () => {},
      openSpawn: () => {},
    })
    const start = sample(f.pointFor(['arg']), f.node)
    const claim = controller.claim(start)!
    const body = f.engine.bodies.get(f.node)!
    const destination = { x: body.pos.x + body.discR * f.engine.scale + 8, y: body.pos.y }
    const end = sample(destination, f.node)
    claim.move(end)
    claim.release(end, true)
    expect(requests).toEqual([{ node: f.node, path: ['arg'], at: destination }])
  })

  it('retains iteration elsewhere on the selected node with an enclosing halo', () => {
    const f = fixture()
    const fissions: FissionRequest[] = []
    const controller = new ProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => f.diagram,
      engine: () => f.engine,
      viewScale: () => 1,
      selection: () => [{ kind: 'node', id: f.node }],
      setSelection: () => {},
      context: () => (EMPTY_PROOF_CONTEXT),
      orientation: () => 'forward',
      apply: () => {},
      commitFission: (request) => { fissions.push(request) },
      refuse: () => {},
      theme: () => LIGHT,
      fuel: () => 64,
      openComprehension: () => {},
      openAbstraction: () => {},
      openSpawn: () => {},
    })
    const body = f.engine.bodies.get(f.node)!
    const offsets = [-0.8, -0.6, -0.4, 0, 0.4, 0.6, 0.8]
    const iterationPoint = offsets.flatMap((x) => offsets.map((y) => ({
      x: body.pos.x + x * body.discR * f.engine.scale,
      y: body.pos.y + y * body.discR * f.engine.scale,
    }))).find((point) => fissionHit(f.engine, f.diagram, point, 1) === null
      && wireHitTest(f.engine, point, { scale: 1 }) === null)!
    expect(iterationPoint).toBeDefined()
    const claim = controller.claim(sample(iterationPoint, f.node))!
    claim.move(sample({ x: iterationPoint.x + 1, y: iterationPoint.y + 1 }, f.node))
    expect(fissions).toEqual([])
    expect(controller.overlay().some((shape) => shape.kind === 'circle')).toBe(true)
    expect(controller.overlay().some((shape) => shape.kind === 'arc')).toBe(false)
    claim.cancel()
  })
})
