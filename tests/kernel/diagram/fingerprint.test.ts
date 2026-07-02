import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import {
  diagramFingerprint, boundaryFingerprint, diagramsIsomorphic,
} from '../../../src/kernel/diagram/canonical/fingerprint'

const p = (s: string) => parseTerm(s)

function pair() {
  const mk = (swap: boolean) => {
    const b = new DiagramBuilder()
    const first = b.cut(b.root)
    const second = b.cut(b.root)
    const [x, y] = swap ? [second, first] : [first, second]
    b.termNode(x, p('\\x. x'))
    b.termNode(y, p('\\x. \\y. x'))
    return b.build()
  }
  return [mk(false), mk(true)] as const
}

describe('diagramFingerprint and diagramsIsomorphic', () => {
  it('equal fingerprints iff isomorphic', () => {
    const [d1, d2] = pair()
    expect(diagramFingerprint(d1)).toBe(diagramFingerprint(d2))
    expect(diagramsIsomorphic(d1, d2)).toBe(true)

    const b = new DiagramBuilder()
    b.cut(b.root)
    const d3 = b.build()
    expect(diagramFingerprint(d1)).not.toBe(diagramFingerprint(d3))
    expect(diagramsIsomorphic(d1, d3)).toBe(false)
  })

  it('size shortcut never changes the answer: unequal sizes and equal-size non-isomorphic both reject', () => {
    const b1 = new DiagramBuilder()
    b1.cut(b1.root)
    const b2 = new DiagramBuilder()
    b2.cut(b2.root)
    b2.cut(b2.root)
    expect(diagramsIsomorphic(b1.build(), b2.build())).toBe(false)

    // equal counts, different content: the shortcut cannot fire; the full
    // canonical comparison must reject
    const c1 = new DiagramBuilder()
    c1.termNode(c1.cut(c1.root), p('\\x. x'))
    const c2 = new DiagramBuilder()
    c2.termNode(c2.cut(c2.root), p('\\x. \\y. x'))
    expect(diagramsIsomorphic(c1.build(), c2.build())).toBe(false)
  })
})

describe('boundaryFingerprint', () => {
  it('is order-sensitive and id-invariant', () => {
    const mk = () => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p('y x'))
      const wOut = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
      const wY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
      return { d: b.build(), wOut, wY }
    }
    const a = mk()
    const c = mk()
    const fa = boundaryFingerprint(mkDiagramWithBoundary(a.d, [a.wOut, a.wY]))
    const fc = boundaryFingerprint(mkDiagramWithBoundary(c.d, [c.wOut, c.wY]))
    const faRev = boundaryFingerprint(mkDiagramWithBoundary(a.d, [a.wY, a.wOut]))
    expect(fa).toBe(fc)
    expect(fa).not.toBe(faRev)
  })
})
