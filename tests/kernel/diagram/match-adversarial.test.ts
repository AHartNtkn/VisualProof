import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const p = (s: string) => parseTerm(s)

describe('findOccurrences adversarial battery', () => {
  it('matches modulo beta-eta with positional wiring intact', () => {
    // pattern node `y` (one port y); host node `(\x. x) y` — beta-equal closures
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const target = h.termNode(h.root, p('(\\x. x) y'))
    const other = h.termNode(h.root, p('\\x. x'))
    const wire = h.wire(h.root, [
      { node: target, port: { kind: 'freeVar', name: 'y' } },
      { node: other, port: { kind: 'output' } },
    ])
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.attachments).toEqual([wire])
  })

  it('surfaces undecided pairs exactly once and excludes them from matches', () => {
    const omegaA = '(\\x. x x) (\\x. x x)'
    const omegaB = '(\\x. x x x) (\\x. x x x)'
    const b = new DiagramBuilder()
    b.termNode(b.root, p(omegaA))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p(omegaB))
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 25 })
    expect(r.matches).toHaveLength(0)
    expect(r.undecided).toHaveLength(1)
    expect(r.undecided[0]?.detail).toMatch(/did not normalize/)
  })

  it('deduplicates symmetric interior bijections by footprint', () => {
    // pattern: two identical nodes; host: two identical nodes — the two
    // bijections pick the same host subgraph: ONE occurrence
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(1)
  })

  it('distinct partial selections are distinct occurrences', () => {
    // pattern: ONE node; host: two identical nodes — two genuinely different
    // footprints
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(2)
  })

  it('bare wires: exact below the root, subset at the root', () => {
    const mkPattern = (atRoot: boolean) => {
      const b = new DiagramBuilder()
      if (atRoot) {
        b.wire(b.root, [])
      } else {
        const cut = b.cut(b.root)
        b.wire(cut, [])
      }
      return mkDiagramWithBoundary(b.build(), [])
    }
    const mkHost = (rootBare: number, cutBare: number) => {
      const h = new DiagramBuilder()
      for (let i = 0; i < rootBare; i++) h.wire(h.root, [])
      const cut = h.cut(h.root)
      for (let i = 0; i < cutBare; i++) h.wire(cut, [])
      return h.build()
    }
    // nested: pattern cut with ONE bare wire vs host cut with TWO → no match
    expect(findOccurrences(mkHost(0, 2), mkPattern(false), { fuel: 10 }).matches).toHaveLength(0)
    expect(findOccurrences(mkHost(0, 1), mkPattern(false), { fuel: 10 }).matches).toHaveLength(1)
    // root: one bare pattern wire among two host bare wires → matches (subset)
    const rootMatches = findOccurrences(mkHost(2, 0), mkPattern(true), { fuel: 10 })
    // Root subset semantics retains both distinct one-wire host footprints.
    expect(rootMatches.matches.filter((m) => m.region === 'r0')).toHaveLength(2)
  })

  it('rejects when an internal wire is scoped differently in the host', () => {
    // pattern: node in a cut, output wire scoped at the CUT (internal, nested)
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    b.wire(cut, [{ node: n, port: { kind: 'output' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    // host: same shape but the wire is scoped at the ROOT
    const h = new DiagramBuilder()
    const hcut = h.cut(h.root)
    const hn = h.termNode(hcut, p('\\x. x'))
    h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('rejects a scope SWAP that preserves per-region wire counts (reaches the exact-scope check)', () => {
    // pattern: cut with nodes A (\x.x) and B (\x.\y.x); A.out scoped at the
    // CUT, B.out scoped at the pattern ROOT — counts: 1 at cut, 1 at root
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const nA = b.termNode(cut, p('\\x. x'))
    const nB = b.termNode(cut, p('\\x. \\y. x'))
    b.wire(cut, [{ node: nA, port: { kind: 'output' } }])
    b.wire(b.root, [{ node: nB, port: { kind: 'output' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    // host: same shape but the scopes are SWAPPED — counts still 1 and 1,
    // so the count guards pass and only the per-wire scope check can reject
    const h = new DiagramBuilder()
    const hcut = h.cut(h.root)
    const hA = h.termNode(hcut, p('\\x. x'))
    const hB = h.termNode(hcut, p('\\x. \\y. x'))
    h.wire(h.root, [{ node: hA, port: { kind: 'output' } }])
    h.wire(hcut, [{ node: hB, port: { kind: 'output' } }])
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('multi-endpoint boundary stubs require one host wire containing all images', () => {
    // pattern: two nodes whose v-ports share one boundary stub
    const b = new DiagramBuilder()
    const n1 = b.termNode(b.root, p('y'))
    const n2 = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])
    const mkHost = (shared: boolean) => {
      const h = new DiagramBuilder()
      const a = h.termNode(h.root, p('y'))
      const c = h.termNode(h.root, p('y'))
      const o = h.termNode(h.root, p('\\x. x'))
      if (shared) {
        h.wire(h.root, [
          { node: a, port: { kind: 'freeVar', name: 'y' } },
          { node: c, port: { kind: 'freeVar', name: 'y' } },
          { node: o, port: { kind: 'output' } },
        ])
      } else {
        h.wire(h.root, [
          { node: a, port: { kind: 'freeVar', name: 'y' } },
          { node: o, port: { kind: 'output' } },
        ])
      }
      return h.build()
    }
    expect(findOccurrences(mkHost(true), pattern, { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(mkHost(false), pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('nested bubble-with-atom patterns match exactly and respect arity', () => {
    const mkPattern = (arity: number) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, arity)
      b.atom(bub, bub)
      return mkDiagramWithBoundary(b.build(), [])
    }
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    h.atom(bub, bub)
    const host = h.build()
    expect(findOccurrences(host, mkPattern(1), { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(host, mkPattern(2), { fuel: 100 }).matches).toHaveLength(0)
  })
})
