import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** The open comp "x : R′(x)": one atom bound to a stub, arg on the boundary. */
function rPrimeComp() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const atom = b.atom(stub, stub)
  const bx = b.wire(b.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { comp: mkDiagramWithBoundary(b.build(), [bx]), stub }
}

/** Host: cut[ rOuter(1)[ rInner(1)[ atom bound rInner on w ] ] ] — rInner negative. */
function host() {
  const h = new DiagramBuilder()
  const cut = h.cut(h.root)
  const rOuter = h.bubble(cut, 1)
  const rInner = h.bubble(rOuter, 1)
  const a = h.atom(rInner, rInner)
  const n = h.termNode(rInner, p('\\x. x'))
  const w = h.wire(rInner, [
    { node: a, port: { kind: 'arg', index: 0 } },
    { node: n, port: { kind: 'output' } },
  ])
  return { d: h.build(), cut, rOuter, rInner, a, n, w }
}

describe('open comprehension instantiation', () => {
  it('instantiates ∀R with "x : R′(x)" — atoms rebind to the ENCLOSING bubble', () => {
    const { d, rOuter, rInner, w } = host()
    const { comp, stub } = rPrimeComp()
    const out = applyComprehensionInstantiate(d, rInner, comp, new Map([[stub, rOuter]]))
    expect(out.regions[rInner]).toBeUndefined() // dissolved
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(atoms[0]!.kind === 'atom' && atoms[0]!.binder).toBe(rOuter)
    // the new atom landed on the original argument wire
    expect(out.wires[w]!.endpoints.some((ep) => ep.port.kind === 'arg')).toBe(true)
    // no fresh bubble was minted
    const bubbles = Object.entries(out.regions).filter(([, r]) => r.kind === 'bubble')
    expect(bubbles.map(([id]) => id)).toEqual([rOuter])
  })

  it('refuses a binder target that does not PROPERLY enclose the bubble, by name', () => {
    const { d, rInner } = host()
    const { comp, stub } = rPrimeComp()
    // the bubble itself: comprehension would mention the variable being eliminated
    expect(() => applyComprehensionInstantiate(d, rInner, comp, new Map([[stub, rInner]])))
      .toThrowError(/must properly enclose the instantiated bubble/)
    // a sibling bubble: not on the ancestor chain at all
    const h2 = new DiagramBuilder()
    const c2 = h2.cut(h2.root)
    const sib = h2.bubble(c2, 1)
    const rI2 = h2.bubble(c2, 1)
    h2.atom(rI2, rI2)
    const d2 = h2.build()
    const { comp: comp2, stub: stub2 } = rPrimeComp()
    expect(() => applyComprehensionInstantiate(d2, rI2, comp2, new Map([[stub2, sib]])))
      .toThrowError(/must properly enclose the instantiated bubble/)
  })

  it('the closed path is unchanged: no binders argument behaves exactly as before', () => {
    const { d, rInner } = host()
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. \\y. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const closed = mkDiagramWithBoundary(b.build(), [bw])
    const out = applyComprehensionInstantiate(d, rInner, closed)
    expect(Object.values(out.nodes).filter((x) => x.kind === 'atom')).toHaveLength(0)
    expect(out.regions[rInner]).toBeUndefined()
  })

  it('still gates on the bubble being negative, before any binder work', () => {
    const h = new DiagramBuilder()
    const rPos = h.bubble(h.root, 1) // positive position
    h.atom(rPos, rPos)
    const d = h.build()
    const { comp, stub } = rPrimeComp()
    expect(() => applyComprehensionInstantiate(d, rPos, comp, new Map([[stub, 'ghost']])))
      .toThrowError(/requires a negative bubble/)
  })
})
