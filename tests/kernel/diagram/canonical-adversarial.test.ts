import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'

const p = (s: string) => parseTerm(s)

describe('exploreForm adversarial battery', () => {
  it('distinguishes atom binder depth (inner vs outer bubble of equal arity)', () => {
    const mk = (inner: boolean) => {
      const b = new DiagramBuilder()
      const outer = b.bubble(b.root, 1)
      const innerB = b.bubble(outer, 1)
      b.atom(innerB, inner ? innerB : outer)
      return b.build()
    }
    expect(exploreForm(mk(true))).not.toBe(exploreForm(mk(false)))
  })

  it('distinguishes which of two same-shape nodes a third connects to, under symmetry', () => {
    // two identical cuts each holding `\x. y x`; a shared term node wires to
    // the free var of ONE of them; swapping which one must not matter (iso),
    // but wiring to BOTH must differ from wiring to one
    const mk = (both: boolean) => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      const n1 = b.termNode(c1, p('\\x. y x'))
      const n2 = b.termNode(c2, p('\\x. y x'))
      const hub = b.termNode(b.root, p('\\x. x'))
      if (both) {
        b.wire(b.root, [
          { node: hub, port: { kind: 'output' } },
          { node: n1, port: { kind: 'freeVar', name: 'y' } },
          { node: n2, port: { kind: 'freeVar', name: 'y' } },
        ])
      } else {
        b.wire(b.root, [
          { node: hub, port: { kind: 'output' } },
          { node: n1, port: { kind: 'freeVar', name: 'y' } },
        ])
      }
      return b.build()
    }
    const one = mk(false)
    const two = mk(true)
    expect(exploreForm(one)).not.toBe(exploreForm(two))
    // and the one-sided version is invariant under which side is chosen
    const mkOther = () => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      const n1 = b.termNode(c1, p('\\x. y x'))
      const n2 = b.termNode(c2, p('\\x. y x'))
      const hub = b.termNode(b.root, p('\\x. x'))
      b.wire(b.root, [
        { node: hub, port: { kind: 'output' } },
        { node: n2, port: { kind: 'freeVar', name: 'y' } },
      ])
      void n1
      return b.build()
    }
    expect(exploreForm(one)).toBe(exploreForm(mkOther()))
  })

  it('distinguishes arg-position wiring on an atom (X(s,t) vs X(t,s))', () => {
    const mk = (swapped: boolean) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 2)
      const s = b.termNode(bub, p('\\x. x'))
      const t = b.termNode(bub, p('\\x. \\y. x'))
      const a = b.atom(bub, bub)
      b.wire(bub, [
        { node: s, port: { kind: 'output' } },
        { node: a, port: { kind: 'arg', index: swapped ? 1 : 0 } },
      ])
      b.wire(bub, [
        { node: t, port: { kind: 'output' } },
        { node: a, port: { kind: 'arg', index: swapped ? 0 : 1 } },
      ])
      return b.build()
    }
    expect(exploreForm(mk(false))).not.toBe(exploreForm(mk(true)))
  })

  it('three-way symmetry: triple identical cuts canonicalize order-independently', () => {
    const perms: number[][] = [
      [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
    ]
    const forms = perms.map((perm) => {
      const b = new DiagramBuilder()
      const cuts = [b.cut(b.root), b.cut(b.root), b.cut(b.root)]
      const contents = [p('\\x. x'), p('\\x. \\y. x'), p('\\x. \\y. y')]
      perm.forEach((ci, i) => b.termNode(cuts[ci]!, contents[i]!))
      return exploreForm(b.build())
    })
    expect(new Set(forms).size).toBe(1)
  })

  it('zero-endpoint wires count and scope placement matter', () => {
    const mk = (count: number) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      for (let i = 0; i < count; i++) b.wire(cut, [])
      return b.build()
    }
    expect(exploreForm(mk(1))).not.toBe(exploreForm(mk(2)))
  })

  it('term content distinguishes beyond shape of wiring', () => {
    const mk = (term: string) => {
      const b = new DiagramBuilder()
      b.termNode(b.root, p(term))
      return b.build()
    }
    expect(exploreForm(mk('\\x. x'))).not.toBe(exploreForm(mk('\\x. \\y. x')))
  })
})
