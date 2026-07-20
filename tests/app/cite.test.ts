import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { ProofContext } from '../../src/kernel/proof/context'
import { verifyTheory } from '../../src/kernel/proof/context'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { citationCandidates, citationDirection, citationStep } from '../../src/app/interact/cite'

function unaryPattern(defId: string) {
  const b = new DiagramBuilder()
  const node = b.ref(b.root, defId, 1)
  const boundary = b.wire(b.root, [{ node, port: { kind: 'arg', index: 0 } }])
  return { side: mkDiagramWithBoundary(b.build(), [boundary]), node }
}

function unaryRelation() {
  const builder = new DiagramBuilder()
  const boundary = builder.wire(builder.root, [])
  return mkDiagramWithBoundary(builder.build(), [boundary])
}

function fixture(): { host: ReturnType<DiagramBuilder['build']>; first: string; second: string; firstWire: string; ctx: ProofContext } {
  const pattern = unaryPattern('p').side
  const theorem: Theorem = { name: 'pRule', lhs: pattern, rhs: pattern, actions: [] }
  const unrelatedSide = unaryPattern('q').side
  const unrelated: Theorem = { name: 'qRule', lhs: unrelatedSide, rhs: unrelatedSide, actions: [] }
  const empty = new DiagramBuilder().build()
  const closed: Theorem = {
    name: 'closed',
    lhs: mkDiagramWithBoundary(empty, []),
    rhs: mkDiagramWithBoundary(empty, []),
    actions: [],
  }
  const h = new DiagramBuilder()
  const first = h.ref(h.root, 'p', 1)
  const firstWire = h.wire(h.root, [{ node: first, port: { kind: 'arg', index: 0 } }])
  const second = h.ref(h.root, 'p', 1)
  h.wire(h.root, [{ node: second, port: { kind: 'arg', index: 0 } }])
  return {
    host: h.build(),
    first,
    second,
    firstWire,
    ctx: verifyTheory({
      relations: { p: unaryRelation(), q: unaryRelation() },
      theorems: [theorem, unrelated, closed],
    }),
  }
}

describe('infer-first citation candidates', () => {
  it('keeps only occurrences containing the selection and infers its attachment', () => {
    const { host, first, firstWire, ctx } = fixture()
    const result = citationCandidates(host, [{ kind: 'node', id: first }], host.root, ctx, 'forward', 64)
    expect(result.applicable.map((candidate) => candidate.name)).toEqual(['pRule'])
    expect(result.applicable[0]!.occurrences).toHaveLength(1)
    expect(result.applicable[0]!.occurrences![0]!.attachments).toEqual([firstWire])
    expect(result.closed.map((candidate) => candidate.name)).toEqual(['closed'])
  })

  it('retains genuine ambiguity in deterministic matcher order', () => {
    const { host, first, second, ctx } = fixture()
    const candidate = citationCandidates(host, [], host.root, ctx, 'forward', 64).applicable[0]!
    expect(candidate.occurrences).toHaveLength(2)
    expect(candidate.occurrences!.map((occurrence) => [...occurrence.nodeMap.values()][0])).toEqual([first, second])
  })

  it('derives direction from polarity xor proof orientation', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const d = b.build()
    expect(citationDirection(d, d.root, 'forward')).toBe('forward')
    expect(citationDirection(d, d.root, 'backward')).toBe('reverse')
    expect(citationDirection(d, cut, 'forward')).toBe('reverse')
    expect(citationDirection(d, cut, 'backward')).toBe('forward')
  })

  it('builds matcher-derived and closed citation steps without manual wire input', () => {
    const { host, first, firstWire, ctx } = fixture()
    const found = citationCandidates(host, [{ kind: 'node', id: first }], host.root, ctx, 'forward', 64)
    const applied = citationStep(host, found.applicable[0]!, 0)
    expect(applied.rule).toBe('theorem')
    if (applied.rule !== 'theorem') throw new Error('expected theorem step')
    expect(applied.at.args).toEqual([firstWire])
    expect(applied.at.sel.nodes).toEqual([first])

    const inserted = citationStep(host, found.closed[0]!, undefined, host.root)
    expect(inserted.rule).toBe('theorem')
    if (inserted.rule !== 'theorem') throw new Error('expected theorem step')
    expect(inserted.at).toMatchObject({ sel: { region: host.root, regions: [], nodes: [], wires: [] }, args: [] })
  })
})
