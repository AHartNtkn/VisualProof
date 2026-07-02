import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkDiagram, type Diagram } from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)

/** Host: bubble rB(1) containing an atom + a term node sharing a wire, plus a cut inside rB. */
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

describe('open extraction', () => {
  it('builds a stub-bubble layer for an externally bound atom', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toHaveLength(1)
    expect(ex.binderAttachments).toEqual([rB])
    const stub = ex.binderStubs[0]!
    const pd = ex.pattern.diagram
    const stubRegion = pd.regions[stub]!
    expect(stubRegion.kind).toBe('bubble')
    expect(stubRegion.kind === 'bubble' && stubRegion.arity).toBe(1)
    expect(stubRegion.kind === 'bubble' && stubRegion.parent).toBe(pd.root)
    // the extracted atom is inside the stub and bound to it
    const atomEntry = Object.values(pd.nodes).find((x) => x.kind === 'atom')!
    expect(atomEntry.kind === 'atom' && atomEntry.binder).toBe(stub)
    expect(atomEntry.region).toBe(stub)
    // the pattern is a VALID closed diagram (mkDiagram re-validates)
    expect(() => mkDiagram({
      root: pd.root,
      regions: { ...pd.regions },
      nodes: { ...pd.nodes },
      wires: { ...pd.wires },
    })).not.toThrow()
  })

  it('keeps closed extractions exactly as before (no stubs)', () => {
    const { d, rB, n } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toEqual([])
    expect(ex.binderAttachments).toEqual([])
    const content = Object.values(ex.pattern.diagram.nodes)
    expect(content).toHaveLength(1)
    expect(content[0]!.region).toBe(ex.pattern.diagram.root)
  })

  it('orders multiple external binders outermost-first', () => {
    const h = new DiagramBuilder()
    const outer = h.bubble(h.root, 1)
    const inner = h.bubble(outer, 2)
    const a1 = h.atom(inner, outer)
    const a2 = h.atom(inner, inner)
    const d = h.build()
    const sel = mkSelection(d, { region: inner, regions: [], nodes: [a1, a2], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderAttachments).toEqual([outer, inner])
    const pd = ex.pattern.diagram
    const [sOuter, sInner] = ex.binderStubs
    expect((pd.regions[sInner!]! as { parent: string }).parent).toBe(sOuter)
    expect((pd.regions[sOuter!]! as { parent: string }).parent).toBe(pd.root)
  })

  it('a binder below the anchor rides inside the selection: the extraction is CLOSED', () => {
    // A binder below the anchor must be selected content to contain its atoms
    // (mkSelection admits no deeper direct nodes), so it always travels with
    // the pattern and never produces a stub.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const a = h.atom(bub, bub)
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [bub], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toEqual([]) // binder inside the selection: closed
    void a
  })

  it('the non-enclosing-binder guard is unreachable through valid hosts and fires loudly on forged ones', () => {
    // mkDiagram enforces that an atom lies inside its binder bubble, so on a
    // validated host every unselected binder of a selected atom encloses the
    // anchor — the rejection is a pure invariant guard. Its loudness is
    // pinned by forging the one host shape that reaches it.
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        b1: { kind: 'bubble', parent: 'r0', arity: 0 },
        c1: { kind: 'cut', parent: 'r0' },
      },
      nodes: { n0: { kind: 'atom', region: 'c1', binder: 'b1' } },
      wires: {},
    })).toThrowError(/must lie inside its binder bubble/)
    const forged = {
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        b1: { kind: 'bubble', parent: 'r0', arity: 0 },
        c1: { kind: 'cut', parent: 'r0' },
      },
      nodes: { n0: { kind: 'atom', region: 'c1', binder: 'b1' } },
      wires: {},
    } as unknown as Diagram
    const sel = mkSelection(forged, { region: 'c1', regions: [], nodes: ['n0'], wires: [] })
    expect(() => extractSubgraph(forged, sel))
      .toThrowError(/atom 'n0' is bound to 'b1', which neither lies in the selection nor encloses its anchor/)
  })

  it('boundary wires stay root-scoped with endpoints inside the stub', () => {
    const { d, rB, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toHaveLength(1) // the shared wire is now a boundary
    const pd = ex.pattern.diagram
    for (const b of ex.pattern.boundary) {
      expect(pd.wires[b]!.scope).toBe(pd.root)
    }
  })
})

describe('closed-only consumers refuse open occurrences by name', () => {
  it('comprehension abstraction refuses externally bound occurrences', async () => {
    const { applyComprehensionAbstract } = await import('../../../src/kernel/rules/comprehension')
    const { mkDiagramWithBoundary } = await import('../../../src/kernel/diagram/boundary')
    const { d, rB, n, a, w } = host()
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const comp = mkDiagramWithBoundary(b.build(), [bw])
    const wrap = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const occ = { sel: mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] }), args: [w] }
    expect(() => applyComprehensionAbstract(d, wrap, comp, [occ]))
      .toThrowError(/bound outside the occurrence cannot be abstracted/)
  })
})
