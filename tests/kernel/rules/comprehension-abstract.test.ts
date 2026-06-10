import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyComprehensionAbstract } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Comprehension of arity 1: "the argument is the identity function". */
function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('applyComprehensionAbstract', () => {
  it('wraps content in a fresh bubble, replacing the occurrence by an atom', () => {
    // (v = λx.x) ∧ hub(v)  ⟹  ∃R. (R(v) ∧ hub(v))
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const hub = h.termNode(h.root, p('y'))
    const w = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n, hub], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [occ])

    const e = new DiagramBuilder()
    const bub = e.bubble(e.root, 1)
    const ehub = e.termNode(bub, p('y'))
    const eatom = e.atom(bub, bub)
    e.wire(e.root, [
      { node: ehub, port: { kind: 'freeVar', name: 'y' } },
      { node: eatom, port: { kind: 'arg', index: 0 } },
    ])
    // hub's output wire stays scoped at root in the actual result (the rule
    // never rescopes wires), so the expected diagram pins it there explicitly
    e.wire(e.root, [{ node: ehub, port: { kind: 'output' } }])
    expect(diagramFingerprint(out)).toBe(diagramFingerprint(e.build()))
  })

  it('abstracts several disjoint occurrences consistently', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const w1 = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n1))![0]
    const w2 = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n2))![0]
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n1, n2], wires: [] })
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n1], wires: [] }), args: [w1] },
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n2], wires: [] }), args: [w2] },
    ])
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(2)
    expect(Object.values(out.nodes).filter((x) => x.kind === 'term')).toHaveLength(0)
  })

  it('rejects occurrences that do not match the comprehension, by fingerprint', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. \\y. x'))
    const d = h.build()
    const w = Object.keys(d.wires)[0]!
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ]))
      .toThrowError(/does not match the comprehension/)
  })

  it('rejects argument-order mismatches: swapped args change the pinned fingerprint', () => {
    // comprehension of arity 2: arg0 is the output, arg1 is the free var y
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('y'))
    const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
    const comp = mkDiagramWithBoundary(b.build(), [b0, b1])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const w1 = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const mk = (args: readonly string[]) => ({
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args,
    })
    expect(() => applyComprehensionAbstract(d, wrap, comp, [mk([w1, w0])]))
      .toThrowError(/does not match the comprehension/)
    expect(() => applyComprehensionAbstract(d, wrap, comp, [mk([w0, w1])])).not.toThrow()
  })

  it('rejects duplicate argument wires with the distinctness error, not a downstream one', () => {
    // without the explicit check, [w0, w0] would surface as a DiagramError
    // ('duplicate boundary wire') from mkDiagramWithBoundary instead of the
    // rule-level message naming the occurrence
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('y'))
    const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
    const comp = mkDiagramWithBoundary(b.build(), [b0, b1])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w0, w0] }
    expect(() => applyComprehensionAbstract(d, wrap, comp, [occ]))
      .toThrowError(/argument wires are not distinct/)
  })

  it('rejects negative wrap regions, overlapping and out-of-wrap occurrences, by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const outside = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const wN = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n))![0]
    const wO = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === outside))![0]

    const negWrap = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    const negOcc = { sel: mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] }), args: [wN] }
    expect(() => applyComprehensionAbstract(d, negWrap, identityComp(), [negOcc]))
      .toThrowError(/requires a positive region/)

    const rootWrap = mkSelection(d, { region: d.root, regions: [], nodes: [], wires: [] })
    const outOcc = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [outside], wires: [] }), args: [wO] }
    expect(() => applyComprehensionAbstract(d, rootWrap, identityComp(), [outOcc]))
      .toThrowError(/outside the wrapped content/)

    const h2 = new DiagramBuilder()
    const m = h2.termNode(h2.root, p('\\x. x'))
    const d2 = h2.build()
    const wM = Object.keys(d2.wires)[0]!
    const wrap2 = mkSelection(d2, { region: d2.root, regions: [], nodes: [m], wires: [] })
    const occ2 = { sel: mkSelection(d2, { region: d2.root, regions: [], nodes: [m], wires: [] }), args: [wM] }
    expect(() => applyComprehensionAbstract(d2, wrap2, identityComp(), [occ2, occ2]))
      .toThrowError(/occurrences overlap/)
  })

  it('with zero occurrences it wraps content in a vacuous bubble', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [])
    const bub = Object.entries(out.regions).find(([, r]) => r.kind === 'bubble')
    expect(bub).toBeDefined()
    expect(out.nodes[n]?.region).toBe(bub![0])
  })

  it('abstracts inside a doubly-cut (positive) region', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const n = h.termNode(c2, p('\\x. x'))
    const d = h.build()
    const w = Object.keys(d.wires)[0]!
    const wrap = mkSelection(d, { region: c2, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: c2, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [occ])
    const bub = Object.entries(out.regions).find(([, r]) => r.kind === 'bubble')!
    expect(bub[1].kind === 'bubble' && bub[1].parent).toBe(c2)
  })

  it('parents the atom at a nested occurrence anchor, not at the bubble top', () => {
    // R must replace G at G's position: hoisting the atom to the bubble top
    // would move R out of the cut, flipping its polarity inside φ. The arg
    // wire is root-scoped so the hoisted variant would still validate — only
    // the region assertion distinguishes them.
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const n = h.termNode(c1, p('\\x. x'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [c1], nodes: [], wires: [] })
    const occ = { sel: mkSelection(d, { region: c1, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [occ])
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(atoms[0]!.region).toBe(c1)
  })

  it('attaches the atom arg-i endpoint to args[i], in order', () => {
    // reversed attachment would still validate (each port wired once) and is
    // isomorphic when nothing else hangs on the wires — assert the endpoints
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('y'))
    const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
    const comp = mkDiagramWithBoundary(b.build(), [b0, b1])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const w1 = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w0, w1] }
    const out = applyComprehensionAbstract(d, wrap, comp, [occ])
    expect(out.wires[w0]!.endpoints.map((ep) => ep.port)).toEqual([{ kind: 'arg', index: 0 }])
    expect(out.wires[w1]!.endpoints.map((ep) => ep.port)).toEqual([{ kind: 'arg', index: 1 }])
  })
})
