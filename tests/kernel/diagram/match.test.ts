import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const p = (s: string) => parseTerm(s)

/** Pattern: single node `y x` with its v:y wire as the only boundary stub. */
function nodePattern() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('y x'))
  const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
  return { pattern: mkDiagramWithBoundary(b.build(), [stub]), node: n }
}

describe('findOccurrences basics', () => {
  it('finds a single-node occurrence and discovers its attachment', () => {
    const h = new DiagramBuilder()
    const target = h.termNode(h.root, p('y x'))
    const other = h.termNode(h.root, p('\\x. x'))
    const wire = h.wire(h.root, [
      { node: target, port: { kind: 'freeVar', name: 'y' } },
      { node: other, port: { kind: 'output' } },
    ])
    const host = h.build()
    const { pattern } = nodePattern()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.undecided).toHaveLength(0)
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.region).toBe(host.root)
    expect(r.matches[0]?.nodeMap.get('n0')).toBe(target)
    expect(r.matches[0]?.attachments).toEqual([wire])
  })

  it('subset semantics at the root: extra host content beside the occurrence is fine', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.cut(h.root)
    h.termNode(h.root, p('y x'))
    const host = h.build()
    const { pattern } = nodePattern()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(1)
  })

  it('exact semantics below the root: a host cut with extra content is not a copy', () => {
    const mkPattern = () => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      b.termNode(cut, p('\\x. x'))
      return mkDiagramWithBoundary(b.build(), [])
    }
    const mkHost = (extra: boolean) => {
      const h = new DiagramBuilder()
      const cut = h.cut(h.root)
      h.termNode(cut, p('\\x. x'))
      if (extra) h.termNode(cut, p('\\x. \\y. x'))
      return h.build()
    }
    expect(findOccurrences(mkHost(false), mkPattern(), { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(mkHost(true), mkPattern(), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('restricts to inRegion when given', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    h.termNode(cut, p('y x'))
    h.termNode(h.root, p('y x'))
    const host = h.build()
    const { pattern } = nodePattern()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(2)
    const restricted = findOccurrences(host, pattern, { fuel: 100, inRegion: cut })
    expect(restricted.matches).toHaveLength(1)
    expect(restricted.matches[0]?.region).toBe(cut)
  })

  it('atoms match only when binder images agree', () => {
    const mkPattern = () => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 0)
      b.atom(bub, bub)
      return mkDiagramWithBoundary(b.build(), [])
    }
    const h = new DiagramBuilder()
    const outer = h.bubble(h.root, 0)
    const inner = h.bubble(outer, 0)
    h.atom(inner, outer) // bound to the OUTER bubble
    const host = h.build()
    // pattern (bubble directly holding its own atom) must not match the inner
    // bubble, whose atom is bound elsewhere
    expect(findOccurrences(host, mkPattern(), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('refuses UNSEEDED bare boundary stubs, non-positive fuel, unknown inRegion', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare])
    const h = new DiagramBuilder()
    const host = h.build()
    // a bare boundary wire has no endpoints to anchor a search; unseeded it is
    // refused with an instructive message, not silently guessed
    expect(() => findOccurrences(host, pattern, { fuel: 100 }))
      .toThrowError(/bare boundary wire 'w0' has no endpoints to anchor a search; supply its attachment/)
    const { pattern: ok } = nodePattern()
    expect(() => findOccurrences(host, ok, { fuel: 0 }))
      .toThrowError(/fuel must be a positive integer/)
    expect(() => findOccurrences(host, ok, { fuel: 10, inRegion: 'ghost' }))
      .toThrowError(/unknown region 'ghost'/)
  })

  it('SEEDED bare boundary wire: its image is the supplied host wire, gated only by visibility', () => {
    // pattern: a `\x. x` node plus a bare boundary wire (a pass-through arg)
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare])
    // host: a matching node plus a spare root-scoped wire to anchor the arg to
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const anchor = h.wire(h.root, [])
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100, attachments: [anchor] })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.attachments).toEqual([anchor])
    expect(r.matches[0]?.wireMap.get(bare)).toBe(anchor)
  })

  it('SEEDED bare boundary attachments may not alias: one host wire cannot serve two boundary positions', () => {
    // Two bare boundary lines supplied the SAME host wire must refuse, exactly
    // as endpointful attachments do (the used-images seam rule). Diagonal
    // instantiation (a = b) is a deliberate future design (the queued diagonal
    // abstraction work), not something the matcher may improvise.
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare0 = b.wire(b.root, [])
    const bare1 = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare0, bare1])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const anchor = h.wire(h.root, [])
    const other = h.wire(h.root, [])
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100, attachments: [anchor, anchor] }).matches).toHaveLength(0)
    expect(findOccurrences(host, pattern, { fuel: 100, attachments: [anchor, other] }).matches).toHaveLength(1)
  })

  it('SEEDED bare boundary wire is refused when the supplied wire is not in scope', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare])
    // host: the seed wire is scoped INSIDE a cut, so it does not enclose the
    // root region the occurrence lands in — the visibility gate refuses it
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    const buried = h.wire(cut, [])
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100, inRegion: 'r0', attachments: [buried] })
    expect(r.matches).toHaveLength(0)
  })
})

describe('adversarial ids (soundness and dedup under unconstrained id strings)', () => {
  it('verdict caching cannot alias across node-id boundaries (no forged occurrences)', () => {
    // pattern nodes 'a' (\x.x) and 'a b' (\x. x x): distinct shapes
    const pd = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {
        'a': { kind: 'term', region: 'r0', term: p('\\x. x') },
        'a b': { kind: 'term', region: 'r0', term: p('\\x. x x') },
      },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'a', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'a b', port: { kind: 'output' } }] },
      },
    })
    const pattern = mkDiagramWithBoundary(pd, [])
    // host nodes 'b c' (\x.x) and 'c' (\x.x): both identity — the pattern's
    // \x. x x node has NO image, so zero occurrences exist
    const host = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {
        'b c': { kind: 'term', region: 'r0', term: p('\\x. x') },
        'c': { kind: 'term', region: 'r0', term: p('\\x. x') },
      },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'b c', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'c', port: { kind: 'output' } }] },
      },
    })
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('footprint dedup cannot alias across id boundaries (no dropped occurrences)', () => {
    // pattern: two identity nodes; host: four identity nodes with ids crafted
    // so two DIFFERENT image sets join to the same string — C(4,2)=6 distinct
    // occurrences must all survive
    const mkNode = () => ({ kind: 'term' as const, region: 'r0', term: p('\\x. x') })
    const pb = new DiagramBuilder()
    pb.termNode(pb.root, p('\\x. x'))
    pb.termNode(pb.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(pb.build(), [])
    const host = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { 'a': mkNode(), 'b,c': mkNode(), 'a,b': mkNode(), 'c': mkNode() },
      wires: {
        'wa': { scope: 'r0', endpoints: [{ node: 'a', port: { kind: 'output' } }] },
        'wb,wc': { scope: 'r0', endpoints: [{ node: 'b,c', port: { kind: 'output' } }] },
        'wa,wb': { scope: 'r0', endpoints: [{ node: 'a,b', port: { kind: 'output' } }] },
        'wc': { scope: 'r0', endpoints: [{ node: 'c', port: { kind: 'output' } }] },
      },
    })
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(6)
  })

  it('rejects boundary stubs not scoped at the pattern root (silent never-match hole)', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('y'))
    const stub = b.wire(cut, [{ node: n, port: { kind: 'freeVar', name: 'y' } }]) // scoped INSIDE
    const pattern = mkDiagramWithBoundary(b.build(), [stub])
    const h = new DiagramBuilder()
    const host = h.build()
    expect(() => findOccurrences(host, pattern, { fuel: 100 }))
      .toThrowError(/boundary wire 'w0' is not scoped at the pattern root/)
  })
})
