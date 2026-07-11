import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import {
  contextualDeleteStep,
  discoverProofActions,
  foldedComprehension,
  iterationTargets,
} from '../../src/app/interact/moves'

const p = (source: string) => parseTerm(source)
const ctx = () => verifyTheory(buildFregeTheory())

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
