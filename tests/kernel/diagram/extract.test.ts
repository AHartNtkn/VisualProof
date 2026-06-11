import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { boundaryArity } from '../../../src/kernel/diagram/boundary'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

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

describe('extractSubgraph', () => {
  it('produces a valid pattern with root-scoped boundary stubs and an attachment record', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // boundary: exactly the touching wire (wShared), as a root-scoped stub
    expect(boundaryArity(pattern)).toBe(1)
    expect(attachments).toEqual([h.wShared])
    const stubId = pattern.boundary[0]!
    const stub = pattern.diagram.wires[stubId]!
    expect(stub.scope).toBe(pattern.diagram.root)
    // the stub keeps only the selected endpoint (nB's output)
    expect(stub.endpoints).toHaveLength(1)
    expect(stub.endpoints[0]?.node).toBe(h.nB)
    // internal content carried over: the cut, nB, and the bare wire inside
    expect(Object.keys(pattern.diagram.regions)).toHaveLength(2) // fresh root + cut
    expect(pattern.diagram.nodes[h.nB]).toBeDefined()
    expect(pattern.diagram.wires[h.wBare]).toBeDefined()
  })

  it('maps selection-region scopes to the pattern root', () => {
    const h = host()
    const sel = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // wShared is internal here: copied with scope at the fresh root
    expect(pattern.diagram.wires[h.wShared]?.scope).toBe(pattern.diagram.root)
    // nA's other ports (out, v:x) were auto-wired at root scope in the host:
    // those host wires touch only nA, so they become boundary stubs
    expect(boundaryArity(pattern)).toBe(2)
    expect(attachments).toHaveLength(2)
  })

  it('orders boundary stubs deterministically by host wire id', () => {
    const h = host()
    const sel = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    const { attachments } = extractSubgraph(h.d, sel)
    expect([...attachments]).toEqual([...attachments].sort())
  })

  it('extracted pattern is a valid diagram (re-validated through mkDiagram)', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    // construction inside extractSubgraph runs mkDiagram; reaching here means it passed
    expect(() => extractSubgraph(h.d, sel)).not.toThrow()
  })
})

describe('extractSubgraph atom-binder boundary', () => {
  it('extracts atoms whose binder is inside the selection', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 0)
    b.atom(bub, bub)
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [bub], nodes: [], wires: [] })
    expect(() => extractSubgraph(d, sel)).not.toThrow()
  })

  it('allows atoms bound to the anchor to extract as open patterns', () => {
    // atoms bound to an enclosing binder (including the anchor itself)
    // extract as open patterns with stub-bubble layers; only binders off the
    // ancestor chain are rejected
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 0)
    const cut = b.cut(bub)
    const a = b.atom(cut, bub)
    void a
    const d = b.build()
    const sel = mkSelection(d, { region: bub, regions: [cut], nodes: [], wires: [] })
    // Atoms in selected regions whose binders are external (not selected)
    // are now extracted as open patterns
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs.length).toBeGreaterThan(0) // has external binders
  })

})
