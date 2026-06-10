import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

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

  it('rejects zero-endpoint boundary stubs, non-positive fuel, unknown inRegion', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare])
    const h = new DiagramBuilder()
    const host = h.build()
    expect(() => findOccurrences(host, pattern, { fuel: 100 }))
      .toThrowError(/boundary wire 'w0' has no endpoints/)
    const { pattern: ok } = nodePattern()
    expect(() => findOccurrences(host, ok, { fuel: 0 }))
      .toThrowError(/fuel must be a positive integer/)
    expect(() => findOccurrences(host, ok, { fuel: 10, inRegion: 'ghost' }))
      .toThrowError(/unknown region 'ghost'/)
  })
})
