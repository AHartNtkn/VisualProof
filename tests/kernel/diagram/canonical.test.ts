import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { canonicalForm } from '../../../src/kernel/diagram/canonical/canonical'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('canonicalForm', () => {
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
    expect(canonicalForm(b1.build())).toBe(canonicalForm(b2.build()))
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
    expect(canonicalForm(mk('y z'))).toBe(canonicalForm(mk('a b')))
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
    expect(canonicalForm(mk(true))).not.toBe(canonicalForm(mk(false)))
  })

  it('distinguishes cut from bubble and arity from arity', () => {
    const mk = (kind: 'cut' | 'bubble', arity?: number) => {
      const b = new DiagramBuilder()
      if (kind === 'cut') b.cut(b.root)
      else b.bubble(b.root, arity!)
      return b.build()
    }
    expect(canonicalForm(mk('cut'))).not.toBe(canonicalForm(mk('bubble', 0)))
    expect(canonicalForm(mk('bubble', 0))).not.toBe(canonicalForm(mk('bubble', 1)))
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
    expect(canonicalForm(mk(false))).toBe(canonicalForm(mk(true)))
  })

  it('distinguishes wire scope (same endpoints, different quantifier location)', () => {
    const mk = (scopeAtRoot: boolean) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const t = b.termNode(cut, p('\\x. x'))
      b.wire(scopeAtRoot ? b.root : cut, [{ node: t, port: { kind: 'output' } }])
      return b.build()
    }
    expect(canonicalForm(mk(true))).not.toBe(canonicalForm(mk(false)))
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
    expect(canonicalForm(a.d, [a.wOut, a.wY])).toBe(canonicalForm(b2.d, [b2.wOut, b2.wY]))
    expect(canonicalForm(a.d, [a.wOut, a.wY])).not.toBe(canonicalForm(a.d, [a.wY, a.wOut]))
  })

  it('throws on pinned wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => canonicalForm(b.build(), ['ghost'])).toThrowError(/pinned wire 'ghost' does not exist/)
  })

  it('throws on duplicate pinned wires', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    expect(() => canonicalForm(b.build(), [w, w])).toThrowError(/duplicate pinned wire 'w0'/)
  })
})
