import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Host: node `y` at root wired to a hub, plus an empty cut to iterate into. */
function host() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('y'))
  const hub = h.termNode(h.root, p('\\x. x'))
  const w = h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: hub, port: { kind: 'output' } },
  ])
  const cut = h.cut(h.root)
  return { d: h.build(), n, hub, w, cut }
}

describe('applyIteration', () => {
  it('copies a subgraph into a descendant region, sharing attachments', () => {
    const { d, n, w, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, cut)
    // the attachment wire gained the copy's endpoint
    expect(out.wires[w]?.endpoints).toHaveLength(3)
    const copies = Object.values(out.nodes).filter((x) => x.region === cut)
    expect(copies).toHaveLength(1)
  })

  it('permits iteration into the same region', () => {
    const { d, n, w } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, d.root)
    expect(out.wires[w]?.endpoints).toHaveLength(3)
  })

  it('rejects targets outside the source region and targets inside the copy', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const inner = h.cut(cutA)
    const cutB = h.cut(h.root)
    const n = h.termNode(cutA, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cutA, regions: [inner], nodes: [n], wires: [] })
    expect(() => applyIteration(d, sel, cutB))
      .toThrowError(/iteration target 'r3' must lie within the source region 'r1'/)
    expect(() => applyIteration(d, sel, inner))
      .toThrowError(/iteration target 'r2' lies inside the iterated subgraph/)
  })
})

describe('applyDeiteration', () => {
  it('iterate then deiterate is the identity (fingerprint)', () => {
    const { d, n, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    // the copy is the unique node in the cut
    const copyId = Object.entries(iterated.nodes).find(([, x]) => x.region === cut)![0]
    const copySel = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    const back = applyDeiteration(iterated, copySel, 100)
    expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
  })

  it('rejects removal of an unjustified subgraph, by name', () => {
    const { d, n } = host()
    // the original has no second copy anywhere: deiterating it is unjustified
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence found for deiteration at 'r0'/)
  })

  it('a copy cannot justify itself, and separate wires are not shared attachments', () => {
    // ONE closed node: the matcher finds the node itself, but a copy cannot
    // justify its own removal
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence/)
    // TWO separately built identical nodes have DISTINCT output wires:
    // ∃x.P(x) ∧ ∃y.P(y) → ∃x.P(x) is erasure, not deiteration — refuse
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    h2.termNode(h2.root, p('\\x. x'))
    const d2 = h2.build()
    const sel2 = mkSelection(d2, { region: d2.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d2, sel2, 100))
      .toThrowError(/no justifying occurrence/)
  })

  it('attachment-SHARING duplicates deiterate: ∃x.(P(x)∧P(x)) → ∃x.P(x)', () => {
    // two `y` nodes sharing BOTH their y-wire and their output wire
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y'))
    const b = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [b], wires: [] })
    const out = applyDeiteration(d, sel, 100)
    expect(Object.keys(out.nodes)).toHaveLength(1)
    expect(out.nodes[a]).toBeDefined()
  })

  it('mentions undecided pairs in the failure when fuel ran out', () => {
    // copy and candidate original are both non-normalizing and structurally
    // different — comparison exhausts fuel, so the failure must say so
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    h.termNode(h.root, p('(\\x. x x x) (\\x. x x x)'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d, sel, 25))
      .toThrowError(/undecided under fuel 25/)
  })
})
