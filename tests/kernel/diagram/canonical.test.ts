import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'

const p = (s: string) => parseTerm(s)

describe('exploreForm', () => {
  it('is invariant under construction order (id renaming)', () => {
    // same diagram, two construction orders → different ids, same canonical form
    const b1 = new DiagramBuilder()
    const cut1 = b1.cut(b1.root)
    const t1 = b1.termNode(cut1, p('\\x. x'))
    const s1 = b1.termNode(b1.root, p('\\x. \\y. x'))
    b1.wire(b1.root, [
      { node: s1, port: { kind: 'output' } },
      { node: t1, port: { kind: 'output' } },
    ])
    const b2 = new DiagramBuilder()
    const s2 = b2.termNode(b2.root, p('\\x. \\y. x'))
    const cut2 = b2.cut(b2.root)
    const t2 = b2.termNode(cut2, p('\\x. x'))
    b2.wire(b2.root, [
      { node: t2, port: { kind: 'output' } },
      { node: s2, port: { kind: 'output' } },
    ])
    expect(exploreForm(b1.build())).toBe(exploreForm(b2.build()))
  })

  it('is invariant under per-node free-variable renaming', () => {
    const mk = (term: string) => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p(term))
      const m = b.termNode(b.root, p('\\x. x'))
      const names = term.includes('y') ? ['y', 'z'] : ['a', 'b']
      b.wire(b.root, [
        { node: n, port: { kind: 'freeVar', name: names[0]! } },
        { node: m, port: { kind: 'output' } },
      ])
      return b.build()
    }
    expect(exploreForm(mk('y z'))).toBe(exploreForm(mk('a b')))
  })

  it('distinguishes wiring differences', () => {
    // X(t, t) with both args on one wire vs X(t, s) on two wires
    const mk = (shared: boolean) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 2)
      const t = b.termNode(bub, p('\\x. x'))
      const a = b.atom(bub, bub)
      if (shared) {
        b.wire(bub, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
          { node: a, port: { kind: 'arg', index: 1 } },
        ])
      } else {
        b.wire(bub, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
        ])
      }
      return b.build()
    }
    expect(exploreForm(mk(true))).not.toBe(exploreForm(mk(false)))
  })

  it('distinguishes cut from bubble and arity from arity', () => {
    const mk = (kind: 'cut' | 'bubble', arity?: number) => {
      const b = new DiagramBuilder()
      if (kind === 'cut') b.cut(b.root)
      else b.bubble(b.root, arity!)
      return b.build()
    }
    expect(exploreForm(mk('cut'))).not.toBe(exploreForm(mk('bubble', 0)))
    expect(exploreForm(mk('bubble', 0))).not.toBe(exploreForm(mk('bubble', 1)))
  })

  it('handles symmetric diagrams via individualization (two identical disconnected cuts)', () => {
    const mk = (swap: boolean) => {
      const b = new DiagramBuilder()
      const first = b.cut(b.root)
      const second = b.cut(b.root)
      const [x, y] = swap ? [second, first] : [first, second]
      b.termNode(x, p('\\x. x'))
      b.termNode(y, p('\\x. x'))
      return b.build()
    }
    // refinement alone cannot split the two cuts; individualization must, and
    // the result must not depend on construction order
    expect(exploreForm(mk(false))).toBe(exploreForm(mk(true)))
  })

  it('distinguishes wire scope (same endpoints, different quantifier location)', () => {
    const mk = (scopeAtRoot: boolean) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const t = b.termNode(cut, p('\\x. x'))
      b.wire(scopeAtRoot ? b.root : cut, [{ node: t, port: { kind: 'output' } }])
      return b.build()
    }
    expect(exploreForm(mk(true))).not.toBe(exploreForm(mk(false)))
  })

  it('pins boundary wires by order when given', () => {
    const mk = () => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p('y x'))
      const wOut = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
      const wY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
      return { d: b.build(), wOut, wY }
    }
    const a = mk()
    const b2 = mk()
    expect(exploreForm(a.d, [a.wOut, a.wY])).toBe(exploreForm(b2.d, [b2.wOut, b2.wY]))
    expect(exploreForm(a.d, [a.wOut, a.wY])).not.toBe(exploreForm(a.d, [a.wY, a.wOut]))
  })

  it('throws on pinned wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => exploreForm(b.build(), ['ghost'])).toThrowError(/pinned wire 'ghost' does not exist/)
  })

  it('records the full ordered incidence vector for an aliased boundary', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const u = b.wire(b.root, [])
    const d = b.build()
    expect(exploreForm(d, [w, w, u])).not.toBe(exploreForm(d, [w, u, w]))
    expect(exploreForm(d, [w, w, u])).not.toBe(exploreForm(d, [w, u, u]))
  })
})
