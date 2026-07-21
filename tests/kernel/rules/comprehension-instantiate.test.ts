import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

const p = (s: string) => parseTerm(s)
const pc = (s: string) => parseTerm(s)

/** Comprehension of arity 1: "the argument is the identity function". */
function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w0])
}

/**
 * Parameterized comp of arity 1 with ONE parameter: R(x) := "x —o— q" where q
 * rides the parameter wire. Boundary = [stub x, parameter q].
 */
function paramComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('q'))
  const wx = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  const wq = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'q' } }])
  return mkDiagramWithBoundary(b.build(), [wx, wq])
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
    const out = applyComprehensionInstantiate(d, bub, identityComp(), [])

    const e = new DiagramBuilder()
    const ecut = e.cut(e.root)
    const en = e.termNode(ecut, p('\\x. x'))
    e.wire(ecut, [{ node: en, port: { kind: 'output' } }])
    expect(exploreForm(out)).toBe(exploreForm(e.build()))
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
    const out = applyComprehensionInstantiate(d, bub, identityComp(), [])
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
    const out = applyComprehensionInstantiate(d, bub, identityComp(), [])
    expect(out.regions[bub]).toBeUndefined()
    expect(out.nodes[n]?.region).toBe(cut)
  })

  it('rejects positive bubbles, non-bubbles, and arity mismatches, by name', () => {
    const h = new DiagramBuilder()
    const posBub = h.bubble(h.root, 1)
    const cut = h.cut(h.root)
    const negBub = h.bubble(cut, 2)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, posBub, identityComp(), []))
      .toThrowError(/requires a negative bubble/)
    expect(() => applyComprehensionInstantiate(d, cut, identityComp(), []))
      .toThrowError(/requires a bubble/)
    expect(() => applyComprehensionInstantiate(d, negBub, identityComp(), []))
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
    const out = applyComprehensionInstantiate(d, bub, comp, [])
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
    expect(() => applyComprehensionInstantiate(d, bubDeep, identityComp(), [])).not.toThrow()
    expect(() => applyComprehensionInstantiate(d, bubShallow, identityComp(), []))
      .toThrowError(/requires a negative bubble/)
  })

  it('splice lands at atom.region not bubble.parent when atom is deeper than the bubble', () => {
    // atom lives inside an inner cut nested inside the bubble; the spliced term
    // node must land at that inner cut, not at the bubble's parent (the outer cut)
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const bub = h.bubble(c1, 1)
    const c2 = h.cut(bub) // atom sits here — deeper than bub
    const atom = h.atom(c2, bub)
    h.wire(c1, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp(), [])
    // bub dissolved
    expect(out.regions[bub]).toBeUndefined()
    // c2 promoted to child of c1
    const c2after = out.regions[c2]
    expect(c2after?.kind).toBe('cut')
    if (c2after?.kind === 'cut') expect(c2after.parent).toBe(c1)
    // the term node from identityComp must be inside c2, not c1
    const termNodes = Object.values(out.nodes).filter((n) => n.kind === 'term')
    expect(termNodes).toHaveLength(1)
    expect(termNodes[0]!.region).toBe(c2)
  })

  it('bubble-scoped wires land at bubble.parent (not root) after dissolution', () => {
    // bubble.parent = c1 (a cut), not root; a wire scoped at bub must move to c1
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const bub = h.bubble(c1, 1)
    h.termNode(bub, p('\\x. x'))
    // the auto-wire for the term node's output will be scoped at bub
    const d = h.build()
    const bubScopedIds = Object.entries(d.wires)
      .filter(([, w]) => w.scope === bub)
      .map(([id]) => id)
    expect(bubScopedIds.length).toBeGreaterThan(0)
    const out = applyComprehensionInstantiate(d, bub, identityComp(), [])
    for (const wid of bubScopedIds) {
      expect(out.wires[wid]?.scope).toBe(c1)
    }
  })
})

describe('parameterized comprehension instantiation', () => {
  /** Host: cut[ bubble(1)[ atom ] ] with the atom's arg wire scoped at the cut. */
  function paramHost(paramScope: 'root' | 'parent') {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const atom = h.atom(bub, bub)
    const wArg = h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const wParam = h.wire(paramScope === 'root' ? h.root : cut, [])
    return { d: h.build(), cut, bub, atom, wArg, wParam }
  }

  it('splices the copy with its parameter port on the GIVEN host wire (root-scoped parameter)', () => {
    const { d, bub, wArg, wParam } = paramHost('root')
    const out = applyComprehensionInstantiate(d, bub, paramComp(), [wParam])
    expect(out.regions[bub]).toBeUndefined()
    const termEntries = Object.entries(out.nodes).filter(([, n]) => n.kind === 'term')
    expect(termEntries).toHaveLength(1)
    const copy = termEntries[0]![0]
    // wire identity: the parameter port rides wParam itself, not a fresh wire
    expect(out.wires[wParam]!.endpoints).toEqual([
      { node: copy, port: { kind: 'freeVar', name: 's0' } },
    ])
    // and the leading stub landed on the atom's arg wire, as before
    expect(out.wires[wArg]!.endpoints).toEqual([
      { node: copy, port: { kind: 'output' } },
    ])
  })

  it('splices the copy with its parameter port on the GIVEN host wire (parameter at the bubble parent)', () => {
    const { d, cut, bub, wParam } = paramHost('parent')
    const out = applyComprehensionInstantiate(d, bub, paramComp(), [wParam])
    const termEntries = Object.entries(out.nodes).filter(([, n]) => n.kind === 'term')
    expect(termEntries).toHaveLength(1)
    expect(out.wires[wParam]!.endpoints).toEqual([
      { node: termEntries[0]![0], port: { kind: 'freeVar', name: 's0' } },
    ])
    expect(out.wires[wParam]!.scope).toBe(cut)
  })

  it('refuses a bubble-scoped parameter that would be captured by the instantiated relation', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const atom = h.atom(bub, bub)
    h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const captured = h.wire(bub, [])
    const d = h.build()

    expect(() => applyComprehensionInstantiate(d, bub, paramComp(), [captured]))
      .toThrowError(/parameter attachment wire .* must properly enclose the instantiated bubble/)
  })

  it('attaches the SAME parameter wire to every copy — parameters are shared across instances', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const a1 = h.atom(bub, bub)
    const a2 = h.atom(bub, bub)
    h.wire(cut, [{ node: a1, port: { kind: 'arg', index: 0 } }])
    h.wire(cut, [{ node: a2, port: { kind: 'arg', index: 0 } }])
    const wParam = h.wire(h.root, [])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, paramComp(), [wParam])
    const eps = out.wires[wParam]!.endpoints
    expect(eps).toHaveLength(2)
    expect(new Set(eps.map((ep) => ep.node)).size).toBe(2)
    for (const ep of eps) expect(ep.port.kind).toBe('freeVar')
  })

  it('refuses attachment-count mismatches in both directions, naming all three numbers', () => {
    const { d, bub, wParam } = paramHost('root')
    // too few: boundary 2, arity 1, 0 attachments
    expect(() => applyComprehensionInstantiate(d, bub, paramComp(), []))
      .toThrowError(/arity mismatch: .*arity 1 and 0 parameter attachments.*2 boundary wires/)
    // too many: boundary 1, arity 1, 1 attachment
    expect(() => applyComprehensionInstantiate(d, bub, identityComp(), [wParam]))
      .toThrowError(/arity mismatch: .*arity 1 and 1 parameter attachments.*1 boundary wire/)
  })

  it('refuses a nonexistent attachment wire even when the bubble binds zero atoms', () => {
    // zero atoms means no splice ever runs — the RULE itself must check existence
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, bub, paramComp(), ['ghost']))
      .toThrowError(/parameter attachment wire 'ghost' does not exist/)
  })

  it('refuses a parameter wire scoped INSIDE the bubble when copies land outside its scope', () => {
    // Quantifier-scope forgery probe: the parameter wire lives in a cut inside
    // the bubble; the atom (where the copy lands) is at the bubble itself, NOT
    // enclosed by that cut. The rule-level fixed-parameter gate must refuse.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const atom = h.atom(bub, bub)
    h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const inner = h.cut(bub)
    const wInside = h.wire(inner, [])
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, bub, paramComp(), [wInside]))
      .toThrowError(/parameter attachment wire .* must properly enclose the instantiated bubble/)
  })

  it('instantiates the flat plusComm comp — pair PLUS x b / PLUS b x riding the ambient b-line', () => {
    // R(x) := pair PLUS x b —o— PLUS b x, x the stub, b the parameter
    const b = new DiagramBuilder()
    const P1 = b.termNode(b.root, pc('PLUS q q_0'))
    const P2 = b.termNode(b.root, pc('PLUS q_0 q'))
    const wx = b.wire(b.root, [
      { node: P1, port: { kind: 'freeVar', name: 'q' } },
      { node: P2, port: { kind: 'freeVar', name: 'q' } },
    ])
    const wq = b.wire(b.root, [
      { node: P1, port: { kind: 'freeVar', name: 'q_0' } },
      { node: P2, port: { kind: 'freeVar', name: 'q_0' } },
    ])
    b.wire(b.root, [{ node: P1, port: { kind: 'output' } }, { node: P2, port: { kind: 'output' } }])
    const comp = mkDiagramWithBoundary(b.build(), [wx, wq])

    // Host: the general ℕ(a) bubble shape (base, closure, conclusion atoms)
    // plus an ambient root-scoped b-line.
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const rB = h.bubble(cut1, 1)
    const nz = h.termNode(rB, pc('ZERO'))
    const a0 = h.atom(rB, rB)
    const w0 = h.wire(h.root, [
      { node: nz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ])
    const cut2 = h.cut(rB)
    const a1 = h.atom(cut2, rB)
    const ny = h.termNode(cut2, pc('SUCC y'))
    h.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ny, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut3 = h.cut(cut2)
    const a2 = h.atom(cut3, rB)
    h.wire(cut2, [
      { node: ny, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const cut4 = h.cut(rB)
    const a3 = h.atom(cut4, rB)
    const wa = h.wire(h.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
    const wb = h.wire(h.root, [])
    const d = h.build()

    const out = applyComprehensionInstantiate(d, rB, comp, [wb])
    expect(out.regions[rB]).toBeUndefined()
    expect(Object.values(out.nodes).filter((n) => n.kind === 'atom')).toHaveLength(0)
    // 2 original term nodes + 4 atom occurrences × 2 pair nodes
    expect(Object.values(out.nodes).filter((n) => n.kind === 'term')).toHaveLength(10)
    // every copy rides the SAME ambient b-line: 4 copies × 2 freeVar ports
    const bEps = out.wires[wb]!.endpoints
    expect(bEps).toHaveLength(8)
    for (const ep of bEps) expect(ep.port.kind).toBe('freeVar')
    // the conclusion copy's stub landed on the a-line
    const aEps = out.wires[wa]!.endpoints
    expect(aEps).toHaveLength(2)
    for (const ep of aEps) expect(ep.port.kind).toBe('freeVar')
    // the base copy's stub joined the ZERO line: zero output + 2 freeVar ports
    const zEps = out.wires[w0]!.endpoints
    expect(zEps).toHaveLength(3)
    expect(zEps.filter((ep) => ep.port.kind === 'output')).toHaveLength(1)
    expect(zEps.filter((ep) => ep.port.kind === 'freeVar')).toHaveLength(2)
    // each copy's pair shares one fresh output wire: 4 wires with 2 output endpoints
    const pairWires = Object.values(out.wires).filter(
      (w) => w.endpoints.length === 2 && w.endpoints.every((ep) => ep.port.kind === 'output'),
    )
    expect(pairWires).toHaveLength(4)
  })
})
