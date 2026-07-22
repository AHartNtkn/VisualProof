import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { TERM, relSig, sigEquals } from '../../../src/kernel/diagram/sig'

const p = (s: string) => parseTerm(s)

/**
 * Wire-model counterpart of the deleted open-binder extraction suite. There is
 * no binder machinery: an atom whose head wire lies outside the selection
 * contributes that head wire as an ordinary relational boundary stub, uniformly
 * with any arg wire crossing the boundary.
 */
describe('extraction with externally-scoped relation lines', () => {
  it('an externally-scoped relation line becomes a sig-carrying boundary stub', () => {
    // ∃R at the root; inside a cut, R(t). Select the cut: R's line crosses the
    // boundary. (Counterpart of "builds a stub-bubble layer for an externally
    // bound atom" — the stub is now the head wire, carrying the relational sig.)
    const S = relSig([TERM])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const t = b.termNode(cut, p('\\x. x'))
    const a = b.atom(cut, S)
    b.wire(cut, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ], TERM)
    const headWire = b.wire(b.root, [{ node: a, port: { kind: 'head' } }], S)
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toEqual([headWire])
    expect(ex.pattern.boundary).toHaveLength(1)
    const stub = ex.pattern.diagram.wires[ex.pattern.boundary[0]!]!
    expect(stub.scope).toBe(ex.pattern.diagram.root)
    expect(sigEquals(stub.sig, S)).toBe(true)
    // the extracted atom keeps its head endpoint on the stub
    expect(stub.endpoints).toEqual([{ node: a, port: { kind: 'head' } }])
    // the pattern is a VALID closed diagram (mkDiagram re-validates)
    const pd = ex.pattern.diagram
    expect(() => mkDiagram({
      root: pd.root,
      regions: { ...pd.regions },
      nodes: { ...pd.nodes },
      wires: { ...pd.wires },
    })).not.toThrow()
  })

  it('keeps fully-internal extractions with no boundary stubs', () => {
    // Counterpart of "keeps closed extractions exactly as before (no stubs)":
    // every wire of the selected atom is scoped inside the selection.
    const S = relSig([TERM])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.atom(cut, S)
    b.wire(cut, [{ node: a, port: { kind: 'head' } }], S) // R scoped inside the cut
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toEqual([])
    expect(ex.pattern.boundary).toEqual([])
  })

  it('orders multiple relational stubs deterministically by host wire id', () => {
    // Counterpart of "orders multiple external binders outermost-first": with no
    // binder chain, multiple crossing relation lines order by host wire id.
    const S1 = relSig([TERM])
    const S2 = relSig([])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a1 = b.atom(cut, S1)
    const a2 = b.atom(cut, S2)
    // both head wires scoped at the root (external to the selected cut)
    b.wire(b.root, [{ node: a1, port: { kind: 'head' } }], S1)
    b.wire(b.root, [{ node: a2, port: { kind: 'head' } }], S2)
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect([...ex.attachments]).toEqual([...ex.attachments].sort())
    expect(ex.pattern.boundary).toHaveLength(2)
    // each stub carries its own atom's signature
    const stubSigs = ex.pattern.boundary.map((w) => ex.pattern.diagram.wires[w]!.sig)
    expect(stubSigs.some((s) => sigEquals(s, S1))).toBe(true)
    expect(stubSigs.some((s) => sigEquals(s, S2))).toBe(true)
  })

  it('an arg wire crossing the boundary is a boundary stub exactly like a head wire', () => {
    // Counterpart of "boundary wires stay root-scoped with endpoints inside the
    // stub": arg and head wires are treated uniformly.
    const S = relSig([TERM])
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. x'))
    const cut = b.cut(b.root)
    const a = b.atom(cut, S)
    b.wire(cut, [{ node: a, port: { kind: 'head' } }], S) // head internal
    // arg wire scoped at the root, joining the atom arg to an outside term
    b.wire(b.root, [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: t, port: { kind: 'output' } },
    ], TERM)
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toHaveLength(1) // the crossing arg wire
    const pd = ex.pattern.diagram
    for (const bw of ex.pattern.boundary) {
      expect(pd.wires[bw]!.scope).toBe(pd.root)
      expect(sigEquals(pd.wires[bw]!.sig, TERM)).toBe(true) // an arg line is a TERM line
    }
  })
})
