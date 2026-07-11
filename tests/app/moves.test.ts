import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import {
  contextualDeleteStep,
  discoverProofActions,
  foldedComprehension,
  instantiationChoices,
  iterationTargets,
  ProofMoveController,
} from '../../src/app/interact/moves'
import type { Hit } from '../../src/app/hittest'
import type { KeySample, PointerSample } from '../../src/app/interact/viewport'

const p = (source: string) => parseTerm(source)
const ctx = () => verifyTheory(buildFregeTheory())

const pointer = (hit: Hit): PointerSample => ({
  pointerId: 1,
  button: 0,
  client: { x: 12, y: 18 },
  screen: { x: 12, y: 18 },
  world: { x: 0, y: 0 },
  hit,
  shiftKey: false,
  ctrlKey: false,
  altKey: false,
  metaKey: false,
})

const key = (value: string): KeySample => ({
  key: value,
  shiftKey: value === value.toUpperCase() && value !== value.toLowerCase(),
  ctrlKey: false,
  altKey: false,
  metaKey: false,
  repeat: false,
})

function fusionController(initialSelection: 'none' | 'wire' | 'node' | 'mixed' = 'none') {
  const b = new DiagramBuilder()
  const producer = b.termNode(b.root, p('\\x. x'))
  const consumer = b.termNode(b.root, p('q y'))
  const wire = b.wire(b.root, [
    { node: producer, port: { kind: 'output' } },
    { node: consumer, port: { kind: 'freeVar', name: 'q' } },
  ])
  let diagram = b.build()
  let selection: Hit[] = initialSelection === 'wire'
    ? [{ kind: 'wire', id: wire }]
    : initialSelection === 'node'
      ? [{ kind: 'node', id: producer }]
      : initialSelection === 'mixed'
        ? [{ kind: 'wire', id: wire }, { kind: 'node', id: producer }]
        : []
  const applied: ProofStep[] = []
  const proof = ctx()
  const controller = new ProofMoveController({
    host: { ownerDocument: {} } as HTMLElement,
    active: () => true,
    diagram: () => diagram,
    engine: () => mkEngine(diagram, []),
    selection: () => selection,
    setSelection: (next) => { selection = [...next] },
    context: () => proof,
    orientation: () => 'forward',
    apply: (step) => {
      applied.push(step)
      diagram = applyStep(diagram, step, proof)
    },
    refuse: (text) => { throw new Error(text) },
    theme: () => LIGHT,
    fuel: () => 64,
    openComprehension: () => {},
  })
  return { controller, producer, consumer, wire, applied, diagram: () => diagram }
}

describe('shared proof move discovery', () => {
  it('absorb-normalizes a selected double-cut subtree and chooses its elimination first', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    const node = b.termNode(inner, p('x'))
    const d = b.build()
    const found = discoverProofActions(d, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: node },
    ], ctx(), 'forward')!

    expect(found.sel.regions).toEqual([outer])
    expect(found.sel.nodes).toEqual([])
    expect(contextualDeleteStep(d, found, 64)).toEqual({ rule: 'doubleCutElim', region: outer })
  })

  it('adds same-region orphan riders to erasure but stores no unrelated wire', () => {
    const b = new DiagramBuilder()
    const doomed = b.termNode(b.root, p('x'))
    const survivor = b.termNode(b.root, p('y'))
    const d = b.build()
    const found = discoverProofActions(d, [{ kind: 'node', id: doomed }], ctx(), 'forward')!
    const step = contextualDeleteStep(d, found, 64)
    expect(step?.rule).toBe('erasure')
    if (step?.rule !== 'erasure') throw new Error('expected erasure')
    const doomedWires = Object.entries(d.wires)
      .filter(([, wire]) => wire.endpoints.every((endpoint) => endpoint.node === doomed))
      .map(([id]) => id)
      .sort()
    const survivorWires = Object.entries(d.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === survivor))
      .map(([id]) => id)
    expect([...step.sel.wires].sort()).toEqual(doomedWires)
    expect(step.sel.wires.some((wire) => survivorWires.includes(wire))).toBe(false)
  })

  it('uses one vocabulary in both orientations while flipping only polarity gates', () => {
    const b = new DiagramBuilder()
    const node = b.termNode(b.root, p('(\\x. x) y'))
    const d = b.build()
    const forward = discoverProofActions(d, [{ kind: 'node', id: node }], ctx(), 'forward')!.actions.map((action) => action.kind)
    const backward = discoverProofActions(d, [{ kind: 'node', id: node }], ctx(), 'backward')!.actions.map((action) => action.kind)
    for (const shared of ['doubleCutWrap', 'vacuousWrap', 'iterate', 'deiterate', 'convert', 'relFold']) {
      expect(forward).toContain(shared)
      expect(backward).toContain(shared)
    }
    expect(forward).toContain('erase')
    expect(backward).not.toContain('erase')
  })
})

describe('proof move parameters', () => {
  it('offers one anonymous relation before matching named folded relations', () => {
    expect(instantiationChoices(ctx(), 2)).toEqual([
      { kind: 'anonymous', label: 'New relation…' },
      { kind: 'named', label: 'succ', name: 'succ' },
    ])
  })

  it('iterates only into descendants outside the selected subtree', () => {
    const b = new DiagramBuilder()
    const selected = b.cut(b.root)
    const inside = b.cut(selected)
    const sibling = b.cut(b.root)
    const nestedSibling = b.bubble(sibling, 0)
    const d = b.build()
    const found = discoverProofActions(d, [{ kind: 'region', id: selected }], ctx(), 'forward')!
    expect(iterationTargets(d, found.sel)).toEqual([d.root, sibling, nestedSibling])
    expect(iterationTargets(d, found.sel)).not.toContain(inside)
  })

  it('builds a named comprehension as one folded reference with ordered boundary wires', () => {
    const proof = ctx()
    const comp = foldedComprehension(proof, 'succ')
    const refs = Object.values(comp.diagram.nodes)
    expect(refs).toEqual([{ kind: 'ref', region: comp.diagram.root, defId: 'succ', arity: 2 }])
    expect(comp.boundary).toHaveLength(2)
    expect(comp.boundary.map((wire) => comp.diagram.wires[wire]!.endpoints[0]!.port)).toEqual([
      { kind: 'arg', index: 0 },
      { kind: 'arg', index: 1 },
    ])
  })
})

describe('fusion gesture dispatch', () => {
  it('submits the existing fusion step when its wire is double-clicked', () => {
    const fixture = fusionController()

    expect(fixture.controller.doubleClick(pointer({ kind: 'wire', id: fixture.wire }))).toBe(true)
    expect(fixture.applied).toEqual([{ rule: 'fusion', wire: fixture.wire }])
    expect(fixture.diagram().nodes[fixture.producer]).toBeUndefined()
    expect(fixture.diagram().wires[fixture.wire]).toBeUndefined()
  })

  it('submits the same fusion step when F is pressed with exactly its wire selected', () => {
    const selected = fusionController('wire')

    expect(selected.controller.keyDown(key('f'))).toBe(true)
    expect(selected.applied).toEqual([{ rule: 'fusion', wire: selected.wire }])
    expect(selected.diagram().nodes[selected.producer]).toBeUndefined()
    expect(selected.diagram().wires[selected.wire]).toBeUndefined()
  })

  it('does not claim F for a node or a multi-item selection', () => {
    const nodeOnly = fusionController('node')
    expect(nodeOnly.controller.keyDown(key('f'))).toBe(false)
    expect(nodeOnly.applied).toEqual([])

    const mixed = fusionController('mixed')
    expect(mixed.controller.keyDown(key('f'))).toBe(false)
    expect(mixed.applied).toEqual([])
  })
})
