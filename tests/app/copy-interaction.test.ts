import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { computeLegs, recomputeRegions } from '../../src/view/index'
import { LIGHT } from '../../src/view/paint'
import { CopyDragController } from '../../src/app/interact/copy'
import { ConstructController } from '../../src/app/interact/construct'
import type { Hit } from '../../src/app/hittest'
import type { PointerSample } from '../../src/app/interact/viewport'

const p = (source: string) => parseTerm(source)
const ctx: ProofContext = EMPTY_PROOF_CONTEXT

function sample(hit: Hit | null, world = { x: 0, y: 0 }, overrides: Partial<PointerSample> = {}): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: world,
    screen: world,
    world,
    hit,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
    ...overrides,
  }
}

function fixture() {
  const builder = new DiagramBuilder()
  const selected = builder.termNode(builder.root, p('y'))
  const producer = builder.termNode(builder.root, p('\\x. x'))
  builder.wire(builder.root, [
    { node: selected, port: { kind: 'freeVar', name: 'y' } },
    { node: producer, port: { kind: 'output' } },
  ])
  const target = builder.cut(builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  return { diagram, engine, selected, target }
}

describe('CopyDragController', () => {
  it('declines Ctrl, Shift, non-primary, unselected, and inactive starts without planning', () => {
    const f = fixture()
    let active = true
    let destinations = 0
    const controller = new CopyDragController({
      active: () => active,
      sourceDiagram: () => f.diagram,
      sourceSelection: () => [{ kind: 'node', id: f.selected }],
      sourceEngine: () => f.engine,
      viewScale: () => 1,
      destination: () => { destinations++; return null },
      commit: () => {},
      refuse: () => {},
      theme: () => LIGHT,
    })
    const selected = { kind: 'node', id: f.selected } as const
    expect(controller.claim(sample(selected, undefined, { ctrlKey: true }))).toBeNull()
    expect(controller.claim(sample(selected, undefined, { shiftKey: true }))).toBeNull()
    expect(controller.claim(sample(selected, undefined, { button: 2 }))).toBeNull()
    expect(controller.claim(sample({ kind: 'region', id: f.target }))).toBeNull()
    active = false
    expect(controller.claim(sample(selected))).toBeNull()
    expect(destinations).toBe(0)
    expect(controller.overlay()).toEqual([])
  })

  it('starts from any contained item on the complete surface of a selected subtree', () => {
    const builder = new DiagramBuilder()
    const selected = builder.cut(builder.root)
    const contained = builder.termNode(selected, p('x'))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => diagram,
      sourceSelection: () => [{ kind: 'region', id: selected }],
      sourceEngine: () => engine,
      viewScale: () => 1,
      destination: () => ({ kind: 'edit', diagram, region: diagram.root, at: { x: 1, y: 2 } }),
      commit: () => {},
      refuse: () => {},
      theme: () => LIGHT,
    })

    expect(controller.claim(sample({ kind: 'node', id: contained }))).not.toBeNull()
  })

  it('uses one enclosing green group preview for a valid proof iteration and commits one ProofAction', () => {
    const f = fixture()
    let diagram = f.diagram
    const actions: ProofAction[] = []
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => diagram,
      sourceSelection: () => [{ kind: 'node', id: f.selected }],
      sourceEngine: () => f.engine,
      viewScale: () => 1,
      destination: () => ({ kind: 'proof', diagram, region: f.target, orientation: 'forward', ctx }),
      commit: (plan) => {
        if (plan.kind !== 'proof') throw new Error('expected proof plan')
        actions.push(plan.action)
        diagram = applyAction(diagram, plan.action, ctx)
      },
      refuse: (text) => { throw new Error(text) },
      theme: () => LIGHT,
    })
    const start = sample({ kind: 'node', id: f.selected })
    const claim = controller.claim(start)!
    claim.move(start)

    const preview = controller.overlay()
    expect(preview.length).toBeGreaterThan(0)
    expect(preview.every((shape) => !('stroke' in shape) || shape.stroke === LIGHT.interaction.valid)).toBe(true)
    expect(preview.some((shape) => shape.kind === 'circle')).toBe(true)

    claim.release(start, true)
    expect(actions).toHaveLength(1)
    expect(actions[0]).toMatchObject({ label: 'Copy selection', steps: [{ rule: 'iteration', target: f.target }] })
    expect(controller.overlay()).toEqual([])
  })

  it('draws one enclosing source halo for a multi-item selected pattern', () => {
    const builder = new DiagramBuilder()
    const a = builder.termNode(builder.root, p('x'))
    const b = builder.termNode(builder.root, p('y'))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(a)!.pos = { x: -40, y: 0 }
    engine.bodies.get(b)!.pos = { x: 40, y: 0 }
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => diagram,
      sourceSelection: () => [{ kind: 'node', id: a }, { kind: 'node', id: b }],
      sourceEngine: () => engine,
      viewScale: () => 1,
      destination: () => ({ kind: 'edit', diagram, region: diagram.root, at: { x: 0, y: 20 } }),
      commit: () => {},
      refuse: () => {},
      theme: () => LIGHT,
    })
    const at = sample({ kind: 'node', id: a })
    const claim = controller.claim(at)!
    claim.move(at)
    const source = controller.sourceOverlay()

    expect(source).toHaveLength(1)
    expect(source[0]).toMatchObject({ kind: 'circle', stroke: LIGHT.interaction.valid })
    if (source[0]?.kind !== 'circle') throw new Error('expected enclosing circle')
    for (const node of [a, b]) {
      const body = engine.bodies.get(node)!
      expect(Math.hypot(body.pos.x - source[0].center.x, body.pos.y - source[0].center.y)
        + body.discR * engine.scale).toBeLessThanOrEqual(source[0].r)
    }
  })

  it('gives construction fallback the identical preview and still commits one durable action', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const selected = builder.termNode(sourceRegion, p('\\x. x'))
    const initial = builder.build()
    let diagram = initial
    const engine = mkEngine(diagram, [])
    const output = Object.entries(diagram.wires).find(([, wire]) => wire.endpoints[0]?.node === selected)![0]
    const actions: ProofAction[] = []
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => diagram,
      sourceSelection: () => [{ kind: 'node', id: selected }, { kind: 'wire', id: output }],
      sourceEngine: () => engine,
      viewScale: () => 1,
      destination: () => ({ kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx }),
      commit: (plan) => {
        if (plan.kind !== 'proof') throw new Error('expected proof plan')
        actions.push(plan.action)
        diagram = applyAction(diagram, plan.action, ctx)
      },
      refuse: (text) => { throw new Error(text) },
      theme: () => LIGHT,
    })
    const at = sample({ kind: 'node', id: selected })
    const claim = controller.claim(at)!
    claim.move(at)
    const previewKinds = controller.overlay().map((shape) => shape.kind)
    claim.release(at, true)

    expect(previewKinds).toContain('circle')
    expect(actions).toHaveLength(1)
    expect(actions[0]).toMatchObject({ label: 'Copy selection', steps: [{ rule: 'closedTermIntro' }] })
  })

  it('does not glow or mutate for refusal, cancellation, or a stale exact plan', () => {
    const f = fixture()
    let source: Diagram = f.diagram
    const commits: unknown[] = []
    const refusals: string[] = []
    let valid = false
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => source,
      sourceSelection: () => [{ kind: 'node', id: f.selected }],
      sourceEngine: () => f.engine,
      viewScale: () => 1,
      destination: () => valid
        ? { kind: 'edit', diagram: source, region: source.root, at: { x: 4, y: 5 } }
        : null,
      commit: (plan) => { commits.push(plan) },
      refuse: (text) => { refusals.push(text) },
      theme: () => LIGHT,
    })
    const at = sample({ kind: 'node', id: f.selected })

    const invalid = controller.claim(at)!
    invalid.move(at)
    expect(controller.overlay()).toEqual([])
    invalid.release(at, true)
    expect(commits).toEqual([])

    valid = true
    const cancelled = controller.claim(at)!
    cancelled.move(at)
    cancelled.cancel()
    cancelled.release(at, true)
    expect(commits).toEqual([])

    const stale = controller.claim(at)!
    stale.move(at)
    source = new DiagramBuilder().build()
    expect(controller.overlay()).toEqual([])
    stale.release(at, true)
    expect(commits).toEqual([])
    expect(refusals.join(' ')).toMatch(/stale|changed/i)
  })

  it('cancels an active copy when Ctrl becomes held before release', () => {
    const f = fixture()
    const commits: unknown[] = []
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => f.diagram,
      sourceSelection: () => [{ kind: 'node', id: f.selected }],
      sourceEngine: () => f.engine,
      viewScale: () => 1,
      destination: () => ({ kind: 'edit', diagram: f.diagram, region: f.diagram.root, at: { x: 2, y: 3 } }),
      commit: (plan) => { commits.push(plan) },
      refuse: () => {},
      theme: () => LIGHT,
    })
    const start = sample({ kind: 'node', id: f.selected })
    const claim = controller.claim(start)!
    claim.move(start)
    const ctrl = sample({ kind: 'node', id: f.selected }, start.world, { ctrlKey: true })
    claim.move(ctrl)
    claim.release(ctrl, true)

    expect(commits).toEqual([])
    expect(controller.overlay()).toEqual([])
  })

  it('commits Edit and workspace structural copies without mutating before drop', () => {
    for (const kind of ['edit', 'workspace'] as const) {
      const f = fixture()
      const empty = new DiagramBuilder().build()
      let live = kind === 'edit' ? f.diagram : empty
      const before = live
      let commits = 0
      const controller = new CopyDragController({
        active: () => true,
        sourceDiagram: () => f.diagram,
        sourceSelection: () => [{ kind: 'node', id: f.selected }],
        sourceEngine: () => f.engine,
        viewScale: () => 1,
        destination: () => kind === 'edit'
          ? { kind, diagram: live, region: live.root, at: { x: 9, y: 8 } }
          : { kind, draft: live, region: live.root, at: { x: 9, y: 8 } },
        commit: (plan) => { commits++; if (plan.kind !== 'proof') live = plan.result },
        refuse: (text) => { throw new Error(text) },
        theme: () => LIGHT,
      })
      const at = sample({ kind: 'node', id: f.selected })
      const claim = controller.claim(at)!
      claim.move(at)
      expect(live).toBe(before)
      claim.release(at, true)
      expect(commits).toBe(1)
      expect(live).not.toBe(before)
      expect(Object.keys(live.nodes)).toHaveLength(Object.keys(before.nodes).length + 1)
    }
  })
})

describe('shared copy surface integration', () => {
  it('routes one selected node through the same Edit copy planner as larger patterns', () => {
    const builder = new DiagramBuilder()
    const selected = builder.termNode(builder.root, p('\\x. x'))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(selected)!.pos = { x: 0, y: 0 }
    const body = engine.bodies.get(selected)!
    const wholeNodeSurface = {
      x: body.pos.x - 7 * engine.scale,
      y: body.pos.y - 5 * engine.scale,
    }
    let copyTargets = 0
    let copyCommits = 0
    const controller = new ConstructController({
      host: {} as HTMLElement,
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      diagram: () => diagram,
      selection: () => [{ kind: 'node', id: selected }],
      setSelection: () => {},
      commit: () => {},
      commitFission: () => {},
      refuse: () => {},
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
      copy: {
        destination: (at) => {
          copyTargets++
          return { kind: 'edit', diagram, region: diagram.root, at: at.world }
        },
        commit: () => { copyCommits++ },
      },
    })

    const claim = controller.claim(sample({ kind: 'node', id: selected }, wholeNodeSurface))!
    expect(claim.relaxationPins).toBeUndefined()
    claim.move(sample({ kind: 'node', id: selected }, { x: 30, y: 10 }))
    claim.release(sample({ kind: 'node', id: selected }, { x: 30, y: 10 }), true)

    expect(copyTargets).toBeGreaterThan(0)
    expect(copyCommits).toBe(1)
    expect(engine.bodies.get(selected)!.pos).toEqual({ x: 0, y: 0 })
  })

  it('lets connection-capable wire interaction claim before selected-pattern copy', () => {
    const builder = new DiagramBuilder()
    const a = builder.termNode(builder.root, p('f x'))
    const b = builder.termNode(builder.root, p('f y'))
    const wire = builder.wire(builder.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(a)!.pos = { x: -40, y: 0 }
    engine.bodies.get(b)!.pos = { x: 40, y: 0 }
    recomputeRegions(engine)
    const leg = computeLegs(engine).find((candidate) => candidate.leg.wid === wire)!
    const start = leg.pts[0]!
    let copyTargets = 0
    const controller = new ConstructController({
      host: {} as HTMLElement,
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      diagram: () => diagram,
      selection: () => [{ kind: 'wire', id: wire }],
      setSelection: () => {},
      commit: () => {},
      commitFission: () => {},
      refuse: () => {},
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
      copy: {
        destination: () => { copyTargets++; return null },
        commit: () => {},
      },
    })

    const claim = controller.claim(sample({ kind: 'wire', id: wire }, start))!
    claim.move(sample({ kind: 'wire', id: wire }, leg.pts.at(-1)!))
    expect(copyTargets).toBe(0)
  })

  it('routes a selected region through structural copy instead of Edit placement', () => {
    const builder = new DiagramBuilder()
    const selected = builder.cut(builder.root)
    let diagram = builder.build()
    const engine = mkEngine(diagram, [])
    let history = 0
    const controller = new ConstructController({
      host: {} as HTMLElement,
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      diagram: () => diagram,
      selection: () => [{ kind: 'region', id: selected }],
      setSelection: () => {},
      commit: () => { throw new Error('ordinary placement must not own selected-pattern copy') },
      commitFission: () => {},
      refuse: (text) => { throw new Error(text) },
      setProblem: () => {},
      clearProblem: () => {},
      openSpawn: () => {},
      theme: () => LIGHT,
      copy: {
        destination: (at) => ({ kind: 'edit', diagram, region: diagram.root, at: at.world }),
        commit: (plan) => {
          if (plan.kind === 'proof') throw new Error('expected structural copy')
          history++
          diagram = plan.result
        },
      },
    })
    const at = sample({ kind: 'region', id: selected })
    const claim = controller.claim(at)!
    claim.move(at)
    claim.release(at, true)
    expect(history).toBe(1)
    expect(Object.keys(diagram.regions)).toHaveLength(3)
  })
})
