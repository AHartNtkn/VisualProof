import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
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

  it('distinguishes wiring differences (atom X(t,t) shared vs X(t,·) separate)', () => {
    // X(t, t) with both args on one wire vs X(t, ·) on two wires
    const sig = relSig([IOTA, IOTA])
    const mk = (shared: boolean) => {
      const b = new DiagramBuilder()
      const t = b.termNode(b.root, p('\\x. x'))
      const a = b.atom(b.root, sig)
      b.wire(b.root, [{ node: a, port: { kind: 'head' } }], sig)
      if (shared) {
        b.wire(b.root, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
          { node: a, port: { kind: 'arg', index: 1 } },
        ])
      } else {
        b.wire(b.root, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
        ])
        // arg 1 is auto-wired to its own singleton by build()
      }
      return b.build()
    }
    expect(exploreForm(mk(true))).not.toBe(exploreForm(mk(false)))
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

  it('distinguishes wire scope (same endpoints, different existential location)', () => {
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

describe('exploreForm — signature-indexed wires (Task 4 scenarios)', () => {
  it('(a) two same-scope relational wires are order-independent (wire insertion order is not canonical)', () => {
    // Two relational wires at the root scope, each carrying one atom head, of
    // DISTINGUISHABLE sort (arity 1 vs arity 0). Building the wires record in
    // opposite insertion orders must yield the identical canonical form: the
    // labeling orders wires by refined color, never by insertion. If it sorted
    // by insertion order, the arity-1 and arity-0 wire lines would appear
    // swapped and the two forms would differ.
    const sigA = relSig([IOTA]) // atom nA: head + a0
    const sigB = relSig([]) // atom nB: head only
    const nodes = {
      nA: { kind: 'atom', region: 'r0', sig: sigA },
      nB: { kind: 'atom', region: 'r0', sig: sigB },
    } as const
    const hA = { scope: 'r0', sig: sigA, endpoints: [{ node: 'nA', port: { kind: 'head' } }] } as const
    const hB = { scope: 'r0', sig: sigB, endpoints: [{ node: 'nB', port: { kind: 'head' } }] } as const
    const aA0 = { scope: 'r0', sig: IOTA, endpoints: [{ node: 'nA', port: { kind: 'arg', index: 0 } }] } as const

    const forward = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { ...nodes },
      wires: { hA, hB, aA0 }, // relational wires inserted A then B
    })
    const reversed = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { ...nodes },
      wires: { hB, hA, aA0 }, // relational wires inserted B then A
    })
    expect(exploreForm(forward)).toBe(exploreForm(reversed))
  })

  it('(b) wires of different sort at the same scope yield different forms (sigKey enters the wire color)', () => {
    // Two diagrams that are structurally identical except for the sort of a
    // single endpoint-free relational wire at the root. They must differ: the
    // wire's signature is intrinsic content and enters the canonical form.
    const mk = (args: readonly (typeof IOTA)[]) => {
      const b = new DiagramBuilder()
      b.relWire(b.root, relSig(args))
      return b.build()
    }
    expect(exploreForm(mk([]))).not.toBe(exploreForm(mk([IOTA])))
    expect(exploreForm(mk([IOTA]))).not.toBe(exploreForm(mk([IOTA, IOTA])))
    // …and the SAME sort at the same scope stays equal
    expect(exploreForm(mk([IOTA]))).toBe(exploreForm(mk([IOTA])))
  })

  it('(c) body nodes agree iff their content has an equal canonical fingerprint', () => {
    // A body node fingerprints its payload by the boundary-anchored canonical
    // form of its content diagram. Contents isomorphic up to free-port names
    // share a fingerprint; a different content shape does not.
    const bodyDiagram = (contentTerm: string) => {
      const cb = new DiagramBuilder()
      cb.termNode(cb.root, p(contentTerm))
      const content = mkDiagramWithBoundary(cb.build(), [])
      return mkDiagram({
        root: 'r0',
        regions: { r0: { kind: 'sheet' } },
        nodes: { nb: { kind: 'body', region: 'r0', sig: relSig([]), content } },
        wires: { wo: { scope: 'r0', sig: relSig([]), endpoints: [{ node: 'nb', port: { kind: 'output' } }] } },
      })
    }
    // 'y' and 'z' are the same term up to the (non-semantic) free-port name
    expect(exploreForm(bodyDiagram('y'))).toBe(exploreForm(bodyDiagram('z')))
    // a genuinely different content shape must not collide
    expect(exploreForm(bodyDiagram('y'))).not.toBe(exploreForm(bodyDiagram('\\x. x')))
  })
})
