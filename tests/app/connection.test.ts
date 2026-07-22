import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { computeLegs, recomputeRegions } from '../../src/view/index'
import { LIGHT } from '../../src/view/paint'
import { ConnectionDragController, type ConnectionEnd } from '../../src/interaction/controllers/connection'
import { ConstructController } from '../../src/interaction/construct'
import type { PointerSample } from '../../src/interaction/controllers/viewport'
import type { Vec2 } from '../../src/view/vec'
import { vec } from '../../src/view/vec'

const p = (source: string) => parseTerm(source)

function sample(point: Vec2): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: point,
    screen: point,
    world: point,
    hit: null,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

function fixture() {
  const b = new DiagramBuilder()
  const a = b.termNode(b.root, p('f x'))
  const bNode = b.termNode(b.root, p('f y'))
  const c = b.termNode(b.root, p('g x'))
  const d = b.termNode(b.root, p('g y'))
  const wa = b.wire(b.root, [
    { node: a, port: { kind: 'output' } },
    { node: bNode, port: { kind: 'output' } },
  ])
  const wb = b.wire(b.root, [
    { node: c, port: { kind: 'output' } },
    { node: d, port: { kind: 'output' } },
  ])
  const engine = mkEngine(b.build(), [])
  engine.bodies.get(a)!.pos = vec(-60, -30)
  engine.bodies.get(bNode)!.pos = vec(-10, -30)
  engine.bodies.get(c)!.pos = vec(10, 30)
  engine.bodies.get(d)!.pos = vec(60, 30)
  recomputeRegions(engine)
  const endpointPoint = (wire: string, node: string): Vec2 => {
    const geometry = computeLegs(engine).find(({ leg }) => leg.wid === wire)!
    return geometry.leg.from.body === node ? geometry.pts[0]! : geometry.pts.at(-1)!
  }
  return { engine, a, c, wa, wb, source: endpointPoint(wa, a), target: endpointPoint(wb, c) }
}

describe('shared connection drag', () => {
  it('commits concrete source and target endpoints after a moved release', () => {
    const f = fixture()
    const committed: Array<readonly [ConnectionEnd, ConnectionEnd]> = []
    const controller = new ConnectionDragController({
      active: () => true,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (source, target) => { committed.push([source, target]); return true },
      refuse: () => {},
    })
    const claim = controller.claim(sample(f.source))!

    claim.move(sample(f.target))
    expect(controller.overlay().some((shape) => shape.kind === 'segment' && shape.stroke === LIGHT.interaction.valid)).toBe(true)
    claim.release(sample(f.target), true)

    expect(committed).toEqual([[
      { wire: f.wa, endpoint: { node: f.a, port: { kind: 'output' } } },
      { wire: f.wb, endpoint: { node: f.c, port: { kind: 'output' } } },
    ]])
  })

  it('leaves a still release to selection and commits nothing', () => {
    const f = fixture()
    const committed: Array<readonly [ConnectionEnd, ConnectionEnd]> = []
    const controller = new ConnectionDragController({
      active: () => true,
      engine: () => f.engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (source, target) => { committed.push([source, target]); return true },
      refuse: () => {},
    })
    const claim = controller.claim(sample(f.source))!

    expect(claim.still).toBe('selection')
    claim.release(sample(f.source), false)

    expect(committed).toEqual([])
  })

  it('highlights only the chosen target leg on a three-output equality wire', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('f x'))
    const c = b.termNode(b.root, p('f y'))
    const d = b.termNode(b.root, p('f z'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
      { node: d, port: { kind: 'output' } },
    ])
    const engine = mkEngine(b.build(), [])
    engine.bodies.get(a)!.pos = vec(-50, 20)
    engine.bodies.get(c)!.pos = vec(0, -30)
    engine.bodies.get(d)!.pos = vec(50, 20)
    recomputeRegions(engine)
    const legs = computeLegs(engine).filter(({ leg }) => leg.wid === wire)
    const legFor = (node: string) => legs.find(({ leg }) => leg.from.body === node || leg.to.body === node)!
    const pointFor = (node: string): Vec2 => {
      const geometry = legFor(node)
      return geometry.leg.from.body === node ? geometry.pts[0]! : geometry.pts.at(-1)!
    }
    const controller = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: () => true,
      refuse: () => {},
    })
    const claim = controller.claim(sample(pointFor(a)))!

    claim.move(sample(pointFor(d)))
    const highlighted = controller.overlay().filter((shape) => shape.kind === 'polyline')

    expect(highlighted).toHaveLength(1)
    expect(highlighted[0]).toMatchObject({ kind: 'polyline', pts: legFor(d).pts })
  })

  it('gives Edit-mode guidance when a connection returns to its source wire', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('f x'))
    const c = b.termNode(b.root, p('f y'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
    ])
    const diagram = b.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(a)!.pos = vec(-40, 0)
    engine.bodies.get(c)!.pos = vec(40, 0)
    recomputeRegions(engine)
    const geometry = computeLegs(engine).find(({ leg }) => leg.wid === wire)!
    const pointFor = (node: string): Vec2 => geometry.leg.from.body === node ? geometry.pts[0]! : geometry.pts.at(-1)!
    const refusals: string[] = []
    const controller = new ConstructController({
      host: {} as HTMLElement,
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      diagram: () => diagram,
      selection: () => [],
      setSelection: () => {},
      commit: () => {},
      commitFission: () => {},
      refuse: (text) => { refusals.push(text) },
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
    })
    const claim = controller.claim(sample(pointFor(a)))!

    claim.move(sample(pointFor(c)))
    claim.release(sample(pointFor(c)), true)

    expect(refusals).toEqual(['release on another line to join'])
  })
})
