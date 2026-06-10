import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Comprehension of arity 1: "the argument is the identity function". */
function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w0])
}

describe('applyComprehensionInstantiate', () => {
  it('replaces each atom by a comprehension copy and dissolves the bubble', () => {
    // ¬(∃R. R(v)) instantiated with "is the identity" → ¬(v = λx.x)
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const atom = h.atom(bub, bub)
    void h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())

    const e = new DiagramBuilder()
    const ecut = e.cut(e.root)
    const en = e.termNode(ecut, p('\\x. x'))
    e.wire(ecut, [{ node: en, port: { kind: 'output' } }])
    expect(diagramFingerprint(out)).toBe(diagramFingerprint(e.build()))
  })

  it('duplicates the comprehension across multiple atoms', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const a1 = h.atom(bub, bub)
    const a2 = h.atom(bub, bub)
    const w = h.wire(cut, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())
    expect(Object.values(out.nodes)).toHaveLength(2)
    expect(out.wires[w]?.endpoints).toHaveLength(2)
    expect(out.regions[bub]).toBeUndefined()
  })

  it('with zero atoms it just dissolves the bubble', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const n = h.termNode(bub, p('\\x. x'))
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())
    expect(out.regions[bub]).toBeUndefined()
    expect(out.nodes[n]?.region).toBe(cut)
  })

  it('rejects positive bubbles, non-bubbles, and arity mismatches, by name', () => {
    const h = new DiagramBuilder()
    const posBub = h.bubble(h.root, 1)
    const cut = h.cut(h.root)
    const negBub = h.bubble(cut, 2)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, posBub, identityComp()))
      .toThrowError(/requires a negative bubble/)
    expect(() => applyComprehensionInstantiate(d, cut, identityComp()))
      .toThrowError(/requires a bubble/)
    expect(() => applyComprehensionInstantiate(d, negBub, identityComp()))
      .toThrowError(/arity mismatch/)
  })

  it('handles atoms with identified arguments: R(x,x)', () => {
    // arity-2 comprehension: "arg0 and arg1 are outputs of one identity node"
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    // a second, bare boundary wire for arg 1
    const w1 = b.wire(b.root, [])
    const comp = mkDiagramWithBoundary(b.build(), [w0, w1])

    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 2)
    const atom = h.atom(bub, bub)
    h.wire(cut, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, comp)
    // the copy's output landed on the SAME wire both boundary stubs map to
    const termNodes = Object.values(out.nodes).filter((x) => x.kind === 'term')
    expect(termNodes).toHaveLength(1)
  })

  it('instantiates at depth 3 (negative) but not depth 2 (positive)', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const c3 = h.cut(c2)
    const bubDeep = h.bubble(c3, 1)
    const bubShallow = h.bubble(c2, 1)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, bubDeep, identityComp())).not.toThrow()
    expect(() => applyComprehensionInstantiate(d, bubShallow, identityComp()))
      .toThrowError(/requires a negative bubble/)
  })
})
