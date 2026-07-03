import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { mkSelection, type SubgraphSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'

const p = (s: string) => parseTerm(s)

function roundTrip(d: ReturnType<DiagramBuilder['build']>, sel: SubgraphSelection): void {
  const validated = mkSelection(d, sel)
  const { pattern, attachments } = extractSubgraph(d, validated)
  const removed = removeSubgraph(d, validated)
  const restored = spliceSubgraph(removed, validated.region, pattern, attachments)
  expect(exploreForm(restored)).toBe(exploreForm(d))
}

describe('extract → remove → splice round-trip (fingerprint identity)', () => {
  it('holds for a cut subtree with a crossing wire', () => {
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. x'))
    b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'output' } },
    ])
    b.wire(cut, [])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
  })

  it('holds for a bubble with atoms and a shared argument wire', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 2)
    const t = b.termNode(bub, p('\\x. x'))
    const a = b.atom(bub, bub)
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: a, port: { kind: 'arg', index: 1 } },
    ])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [bub], nodes: [], wires: [] })
  })

  it('holds for a mixed selection: direct node + subtree + explicit top-level wire', () => {
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. y x'))
    const w = b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [cut], nodes: [nA], wires: [w] })
  })

  it('holds for a selection inside a nested region (splice point below the root)', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    b.termNode(inner, p('\\x. x'))
    const nMid = b.termNode(outer, p('\\x. \\y. x'))
    void nMid
    const d = b.build()
    roundTrip(d, { region: outer, regions: [inner], nodes: [], wires: [] })
  })

  it('holds for the empty selection (degenerate identity)', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [], nodes: [], wires: [] })
  })
})
