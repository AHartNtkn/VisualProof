import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n = h.termNode(rB, p('\\x. x'))
  const a = h.atom(rB, rB)
  const w = h.wire(rB, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(rB)
  return { d: h.build(), rB, n, a, w, cut }
}

describe('spliceSubgraph with a binder map', () => {
  it('splices an open pattern back, binding atoms to the host bubble', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const binderMap = new Map([[ex.binderStubs[0]!, rB]])
    const out = spliceSubgraph(d, cut, ex.pattern, ex.attachments, binderMap)
    // a new atom landed inside the cut, bound to the ORIGINAL host bubble
    const newAtoms = Object.entries(out.nodes).filter(
      ([id, x]) => x.kind === 'atom' && d.nodes[id] === undefined,
    )
    expect(newAtoms).toHaveLength(1)
    const [, atom] = newAtoms[0]!
    expect(atom.kind === 'atom' && atom.binder).toBe(rB)
    expect(atom.region).toBe(cut)
    // the stub bubble itself was NOT copied
    const newBubbles = Object.entries(out.regions).filter(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )
    expect(newBubbles).toHaveLength(0)
    // the attachment wire gained the copy's endpoint
    expect(out.wires[ex.attachments[0]!]!.endpoints).toHaveLength(3)
  })

  it('round-trips: open extract + open splice at the same region is iteration-shaped', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const out = spliceSubgraph(d, rB, ex.pattern, ex.attachments, new Map([[ex.binderStubs[0]!, rB]]))
    expect(Object.keys(out.nodes)).toHaveLength(4) // two originals + two copies
    expect(diagramFingerprint(out)).not.toBe(diagramFingerprint(d))
  })

  it('rejects binder maps whose host id is not a bubble, wrong arity, or not enclosing', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const stub = ex.binderStubs[0]!
    expect(() => spliceSubgraph(d, cut, ex.pattern, ex.attachments, new Map([[stub, cut]])))
      .toThrowError(/binder map target '.*' is not a bubble/)
    expect(() => spliceSubgraph(d, cut, ex.pattern, ex.attachments, new Map([[stub, 'ghost']])))
      .toThrowError(/binder map target 'ghost' does not exist/)
    // wrong arity: an arity-2 bubble enclosing the splice region
    const h2 = new DiagramBuilder()
    const outer2 = h2.bubble(h2.root, 2)
    const inner1 = h2.bubble(outer2, 1)
    const atom2 = h2.atom(inner1, inner1)
    const cut2 = h2.cut(inner1)
    const d2 = h2.build()
    const sel2 = mkSelection(d2, { region: inner1, regions: [], nodes: [atom2], wires: [] })
    const ex2 = extractSubgraph(d2, sel2)
    expect(() => spliceSubgraph(d2, cut2, ex2.pattern, ex2.attachments, new Map([[ex2.binderStubs[0]!, outer2]])))
      .toThrowError(/binder map arity mismatch/)
    // not-enclosing: map the stub to a bubble that does not contain the splice region
    const h3 = new DiagramBuilder()
    const bubA = h3.bubble(h3.root, 1)
    const bubB = h3.bubble(h3.root, 1)
    const atom3 = h3.atom(bubA, bubA)
    const d3 = h3.build()
    const sel3 = mkSelection(d3, { region: bubA, regions: [], nodes: [atom3], wires: [] })
    const ex3 = extractSubgraph(d3, sel3)
    expect(() => spliceSubgraph(d3, bubA, ex3.pattern, ex3.attachments, new Map([[ex3.binderStubs[0]!, bubB]])))
      .toThrowError(/does not enclose the splice region/)
  })

  it('an unmapped stub splices as an ordinary fresh bubble (binder maps are the caller contract)', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    void rB
    // splicing WITHOUT the map copies the stub as a real bubble — that changes
    // meaning (fresh quantifier), so splice must be told explicitly; the plain
    // call still works for genuinely closed patterns, so the guard is on the
    // CALLER side: rules pass the map. Here we just pin that the no-map call
    // produces a fresh bubble rather than silently rebinding.
    const out = spliceSubgraph(d, cut, ex.pattern, ex.attachments)
    const newBubbles = Object.entries(out.regions).filter(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )
    expect(newBubbles).toHaveLength(1) // documented behavior: an unmapped stub is an ordinary bubble
  })
})
