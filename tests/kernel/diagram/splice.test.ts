import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'

const p = (s: string) => parseTerm(s)

function host() {
  const b = new DiagramBuilder()
  const nA = b.termNode(b.root, p('y x'))
  const cut = b.cut(b.root)
  const nB = b.termNode(cut, p('\\x. x'))
  const wShared = b.wire(b.root, [
    { node: nA, port: { kind: 'freeVar', name: 'y' } },
    { node: nB, port: { kind: 'output' } },
  ])
  const wBare = b.wire(cut, [])
  return { d: b.build(), nA, cut, nB, wShared, wBare }
}

describe('removeSubgraph', () => {
  it('drops selected content and trims touching wires to their outside endpoints', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const after = removeSubgraph(h.d, sel)
    expect(after.regions[h.cut]).toBeUndefined()
    expect(after.nodes[h.nB]).toBeUndefined()
    expect(after.wires[h.wBare]).toBeUndefined()
    // wShared survives with only nA's endpoint
    expect(after.wires[h.wShared]?.endpoints).toHaveLength(1)
    expect(after.wires[h.wShared]?.endpoints[0]?.node).toBe(h.nA)
  })

  it('a touching wire trimmed to zero endpoints survives as a bare wire at its scope', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }]) // scoped at root, only endpoint inside the cut
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const after = removeSubgraph(d, sel)
    expect(after.wires[w]).toBeDefined()
    expect(after.wires[w]?.endpoints).toHaveLength(0)
    expect(after.wires[w]?.scope).toBe(d.root)
  })

  it('rejects never-validated selections loudly instead of silently no-op-ing', () => {
    const h = host()
    expect(() => removeSubgraph(h.d, { region: 'ghost', regions: [], nodes: [], wires: [] }))
      .toThrowError(/unknown selection region 'ghost'/)
    // a grandchild subtree root would re-parent across a cut (polarity change) if accepted
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    b.termNode(inner, p('\\x. x'))
    const d = b.build()
    expect(() => removeSubgraph(d, { region: d.root, regions: [inner], nodes: [], wires: [] }))
      .toThrowError(/region 'r2' is not a child of selection region 'r0'/)
  })
})

describe('spliceSubgraph', () => {
  it('extract → remove → splice round-trips structurally (endpoint restored)', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    const removed = removeSubgraph(h.d, sel)
    const restored = spliceSubgraph(removed, h.d.root, pattern, attachments)
    // the shared wire regained a second endpoint
    expect(restored.wires[h.wShared]?.endpoints).toHaveLength(2)
    // one cut exists again, holding one node and one bare wire
    const cuts = Object.entries(restored.regions).filter(([, r]) => r.kind === 'cut')
    expect(cuts).toHaveLength(1)
  })

  it('rejects boundary wires not scoped at the pattern root (the resolved obligation)', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    const w = b.wire(cut, [{ node: n, port: { kind: 'output' } }]) // scoped INSIDE the cut
    const pattern = mkDiagramWithBoundary(b.build(), [w])
    const hostB = new DiagramBuilder()
    const hn = hostB.termNode(hostB.root, p('\\x. x'))
    const hw = hostB.wire(hostB.root, [{ node: hn, port: { kind: 'output' } }])
    expect(() => spliceSubgraph(hostB.build(), 'r0', pattern, [hw]))
      .toThrowError(/boundary wire 'w0' is not scoped at the pattern root; not spliceable/)
  })

  it('rejects attachment arity mismatches and attachments that cannot reach the splice region', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern } = extractSubgraph(h.d, sel)
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, []))
      .toThrowError(/expected 1 attachments, got 0/)
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, ['ghost']))
      .toThrowError(/attachment wire 'ghost' does not exist/)
    // a wire scoped inside the cut cannot serve a splice at the root
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, [h.wBare]))
      .toThrowError(/attachment wire 'w1' \(scope 'r1'\) does not enclose splice region 'r0'/)
  })

  it('generates fresh ids on collision and re-validates the result', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // splice into the ORIGINAL host (not removed): ids collide, fresh ones must be coined
    const doubled = spliceSubgraph(h.d, h.d.root, pattern, attachments)
    const cuts = Object.entries(doubled.regions).filter(([, r]) => r.kind === 'cut')
    expect(cuts).toHaveLength(2)
    // wShared now carries nA + two copies of nB-output
    expect(doubled.wires[h.wShared]?.endpoints).toHaveLength(3)
  })

  it('two boundary stubs may attach to the same host wire', () => {
    // pattern: node 'y x' with both free-var stubs; attach both to one host wire
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y x'))
    const sY = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'y' } }])
    const sX = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'x' } }])
    const pd = pb.build() // pn.out auto-wired internally
    const pattern = mkDiagramWithBoundary(pd, [sY, sX])
    const hb = new DiagramBuilder()
    const hn = hb.termNode(hb.root, p('\\x. x'))
    const hw = hb.wire(hb.root, [{ node: hn, port: { kind: 'output' } }])
    const out = spliceSubgraph(hb.build(), 'r0', pattern, [hw, hw])
    expect(out.wires[hw]?.endpoints).toHaveLength(3) // hn.out + spliced y + spliced x
  })

  it('pushes an intrinsically aliased boundary out by identifying its host attachments once', () => {
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y'))
    const shared = pb.wire(pb.root, [{ node: pn, port: { kind: 'output' } }])
    const pattern = mkDiagramWithBoundary(pb.build(), [shared, shared])

    const hb = new DiagramBuilder()
    const cut = hb.cut(hb.root)
    const outerNode = hb.termNode(cut, p('\\x. x'))
    const innerNode = hb.termNode(cut, p('\\x. \\y. x'))
    const outer = hb.wire(hb.root, [{ node: outerNode, port: { kind: 'output' } }])
    const inner = hb.wire(cut, [{ node: innerNode, port: { kind: 'output' } }])
    const out = spliceSubgraph(hb.build(), cut, pattern, [inner, outer])

    expect(out.wires[inner]).toBeUndefined()
    expect(out.wires[outer]?.scope).toBe(out.root)
    // Both host endpoints plus the pattern endpoint exactly once. Repeating
    // the boundary incidence must not copy the same pattern endpoint twice.
    expect(out.wires[outer]?.endpoints).toHaveLength(3)
  })
})
