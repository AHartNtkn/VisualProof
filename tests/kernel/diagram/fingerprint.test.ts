import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm, boundaryForm } from '../../../src/kernel/diagram/canonical/explore'
import type { Diagram } from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)
const isomorphic = (a: Diagram, b: Diagram) => exploreForm(a) === exploreForm(b)

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

describe('exploreForm as isomorphism key', () => {
  it('equal forms iff isomorphic', () => {
    const [d1, d2] = pair()
    expect(exploreForm(d1)).toBe(exploreForm(d2))
    expect(isomorphic(d1, d2)).toBe(true)

    const b = new DiagramBuilder()
    b.cut(b.root)
    const d3 = b.build()
    expect(exploreForm(d1)).not.toBe(exploreForm(d3))
    expect(isomorphic(d1, d3)).toBe(false)
  })

  it('unequal sizes and equal-size non-isomorphic both reject', () => {
    const b1 = new DiagramBuilder()
    b1.cut(b1.root)
    const b2 = new DiagramBuilder()
    b2.cut(b2.root)
    b2.cut(b2.root)
    expect(isomorphic(b1.build(), b2.build())).toBe(false)

    // equal counts, different content: the full canonical comparison must reject
    const c1 = new DiagramBuilder()
    c1.termNode(c1.cut(c1.root), p('\\x. x'))
    const c2 = new DiagramBuilder()
    c2.termNode(c2.cut(c2.root), p('\\x. \\y. x'))
    expect(isomorphic(c1.build(), c2.build())).toBe(false)
  })
})

describe('boundaryForm', () => {
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
    const fa = boundaryForm(mkDiagramWithBoundary(a.d, [a.wOut, a.wY]))
    const fc = boundaryForm(mkDiagramWithBoundary(c.d, [c.wOut, c.wY]))
    const faRev = boundaryForm(mkDiagramWithBoundary(a.d, [a.wY, a.wOut]))
    expect(fa).toBe(fc)
    expect(fa).not.toBe(faRev)
  })
})
