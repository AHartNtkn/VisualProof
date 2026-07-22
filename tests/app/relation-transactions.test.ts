import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { existentialStubs, legPaths } from '../../src/view/wires'
import { AbstractTransaction } from '../../src/interaction/relation-transactions'
import type { RelationWorkspaceSnapshot } from '../../src/interaction/relation-workspace-draft'

const context = () => (EMPTY_PROOF_CONTEXT)

function unaryScene() {
  const builder = new DiagramBuilder()
  const first = builder.termNode(builder.root, parseTerm('\\x. x'))
  const firstWire = builder.wire(builder.root, [{ node: first, port: { kind: 'output' } }])
  const second = builder.termNode(builder.root, parseTerm('\\x. x'))
  builder.wire(builder.root, [{ node: second, port: { kind: 'output' } }])
  const diagram = builder.build()
  return {
    diagram,
    first,
    firstWire,
    wrap: mkSelection(diagram, { region: diagram.root, regions: [], nodes: [first, second], wires: [] }),
  }
}

function unarySnapshot(): RelationWorkspaceSnapshot {
  const builder = new DiagramBuilder()
  const node = builder.termNode(builder.root, parseTerm('\\x. x'))
  const wire = builder.wire(builder.root, [{ node, port: { kind: 'output' } }])
  return { diagram: builder.build(), ports: [{ id: 'port', wire, kind: 'optional' }] }
}

function emptySnapshot(): RelationWorkspaceSnapshot {
  return { diagram: mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } }), ports: [] }
}

function transactionFixture(scene = unaryScene()) {
  let live = scene.diagram
  const actions: ProofAction[] = []
  const transaction = new AbstractTransaction({
    diagram: () => live,
    boundary: () => [],
    wrap: scene.wrap,
    context,
    orientation: 'forward',
    apply: (action) => { actions.push(action) },
    cancel: () => {},
    engine: () => mkEngine(live, []),
    theme: () => LIGHT,
    matcherFuel: () => 128,
    solverFuel: () => 1024,
  })
  return { scene, transaction, actions, setLive: (next: typeof live) => { live = next } }
}

describe('AbstractTransaction', () => {
  it('keeps the proof source untouched while deriving a provisional wrap and commits one real abstraction action', () => {
    const fixture = transactionFixture()
    const before = exploreForm(fixture.scene.diagram)
    const draft = unarySnapshot()

    fixture.transaction.draftChanged(draft)

    expect(exploreForm(fixture.scene.diagram)).toBe(before)
    expect(fixture.transaction.previewShapes().some((shape) => shape.kind === 'circle')).toBe(true)
    expect(fixture.transaction.debugState()).toMatchObject({ kind: 'matches', activeIndex: 0, candidateCount: 2 })
    fixture.transaction.finalize(draft, [])
    expect(fixture.actions).toHaveLength(1)
    expect(fixture.actions[0]).toMatchObject({
      label: 'abstract relation',
      steps: [{ rule: 'comprehensionAbstract', wrap: fixture.scene.wrap }],
      placements: [],
    })
    expect(fixture.actions[0]!.steps[0]).toMatchObject({ occurrences: expect.any(Array) })
    expect(exploreForm(fixture.scene.diagram)).toBe(before)
  })

  it('draws the provisional bubble around the wires in a wrap selection', () => {
    const builder = new DiagramBuilder()
    const node = builder.termNode(builder.root, parseTerm('\\x. x'))
    const wire = builder.wire(builder.root, [{ node, port: { kind: 'output' } }])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(node)!.pos = { x: 140, y: 90 }
    const transaction = new AbstractTransaction({
      diagram: () => diagram,
      boundary: () => [],
      wrap: mkSelection(diagram, { region: diagram.root, regions: [], nodes: [node], wires: [wire] }),
      context,
      apply: () => {},
      cancel: () => {},
      engine: () => engine,
      theme: () => LIGHT,
      matcherFuel: () => 128,
      solverFuel: () => 1024,
    })
    const bubble = transaction.previewShapes()[0]
    expect(bubble).toMatchObject({ kind: 'circle' })
    if (bubble?.kind !== 'circle') throw new Error('expected provisional bubble circle')
    const wirePoints = [
      ...legPaths(engine).filter(({ wid }) => wid === wire).flatMap(({ pts }) => pts),
      ...existentialStubs(engine).filter(({ wid }) => wid === wire).flatMap(({ from, to, dot }) => [from, to, dot]),
    ]
    expect(wirePoints.length).toBeGreaterThan(0)
    expect(wirePoints.every((point) => Math.hypot(point.x - bubble.center.x, point.y - bubble.center.y) <= bubble.r - 10)).toBe(true)
  })

  it('cycles maximal sets, toggles exclusions, and refuses stale source without changing its draft state', () => {
    const fixture = transactionFixture()
    const draft = unarySnapshot()
    fixture.transaction.draftChanged(draft)
    const candidate = fixture.transaction.debugState().candidateKeys[0]!
    fixture.transaction.toggleExclusion(candidate)
    const excluded = fixture.transaction.debugState()
    expect(excluded.excludedKeys).toContain(candidate)
    fixture.transaction.cycle(1)

    fixture.setLive(mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } }))
    expect(() => fixture.transaction.finalize(draft, [])).toThrow(/source changed|missing/i)
    expect(fixture.actions).toEqual([])
    expect(fixture.transaction.debugState()).toEqual(excluded)
  })

  it('claims a click on a matched occurrence and toggles its exclusion without touching source', () => {
    const fixture = transactionFixture()
    const draft = unarySnapshot()
    fixture.transaction.draftChanged(draft)
    const before = exploreForm(fixture.scene.diagram)
    const sample = {
      pointerId: 1, button: 0,
      client: { x: 10, y: 12 }, screen: { x: 10, y: 12 }, world: { x: 0, y: 0 },
      hit: { kind: 'node' as const, id: fixture.scene.first },
      shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    }

    const claim = fixture.transaction.hostClaim(sample)
    expect(claim).not.toBeNull()
    claim!.release(sample, false)

    expect(fixture.transaction.debugState().excludedKeys).toHaveLength(1)
    expect(exploreForm(fixture.scene.diagram)).toBe(before)
    expect(fixture.actions).toEqual([])
  })

  it('keeps the empty marker clear of a wrapped node so its selected surface can start host copy', () => {
    const fixture = transactionFixture()
    fixture.transaction.draftChanged(emptySnapshot())
    const body = mkEngine(fixture.scene.diagram, []).bodies.get(fixture.scene.first)!
    const marker = fixture.transaction.debugState().markerPoint!
    expect(Math.hypot(marker.x - body.pos.x, marker.y - body.pos.y)).toBeGreaterThan(14)
    const sample = {
      pointerId: 1, button: 0,
      client: body.pos, screen: body.pos, world: body.pos,
      hit: { kind: 'node' as const, id: fixture.scene.first },
      shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    }
    expect(fixture.transaction.hostClaim(sample)).toBeNull()
  })

  it('uses the selected actually-empty marker for one anchored nullary occurrence and placement, or deselects to a trivial wrap', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const scene = {
      diagram,
      first: '',
      firstWire: '',
      wrap: mkSelection(diagram, { region: diagram.root, regions: [cut], nodes: [], wires: [] }),
    }
    const selected = transactionFixture(scene)
    const draft = emptySnapshot()
    selected.transaction.draftChanged(draft)
    const nestedPoint = selected.transaction.debugState().markerPoint!
    selected.transaction.moveEmptyMarker(cut, nestedPoint)
    expect(() => selected.transaction.moveEmptyMarker(diagram.root, { x: 1_000_000, y: 1_000_000 }))
      .toThrow(/outside the wrap/i)
    selected.transaction.finalize(draft, [])
    expect(selected.actions[0]).toMatchObject({
      steps: [{ rule: 'comprehensionAbstract', occurrences: [{ sel: { region: cut }, args: [] }] }],
      placements: [{ introducedNode: 0, x: nestedPoint.x, y: nestedPoint.y }],
    })

    const deselected = transactionFixture(scene)
    deselected.transaction.draftChanged(draft)
    deselected.transaction.toggleEmptyMarker()
    deselected.transaction.finalize(draft, [])
    expect(deselected.actions[0]).toMatchObject({
      steps: [{ rule: 'comprehensionAbstract', occurrences: [] }],
      placements: [],
    })
  })

  it('does not expose the empty-marker route for a nonempty draft with zero matches', () => {
    const builder = new DiagramBuilder()
    const hostNode = builder.termNode(builder.root, parseTerm('\\x. \\y. x'))
    const diagram = builder.build()
    const fixture = transactionFixture({
      diagram,
      first: hostNode,
      firstWire: '',
      wrap: mkSelection(diagram, { region: diagram.root, regions: [], nodes: [hostNode], wires: [] }),
    })
    const draft = unarySnapshot()
    fixture.transaction.draftChanged(draft)

    expect(fixture.transaction.debugState()).toMatchObject({ kind: 'matches', candidateCount: 0, canFinalize: false })
    expect(() => fixture.transaction.toggleEmptyMarker()).toThrow(/not actually empty/i)
    expect(() => fixture.transaction.finalize(draft, [])).toThrow(/no occurrence/i)
    expect(fixture.actions).toEqual([])
  })
})
