import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyComprehensionAbstract, diagonalize } from '../../../src/kernel/rules/comprehension'

const p = (s: string) => parseTerm(s)

/** Binary comp G(a,b): node `y` with output on b0 and free var y on b1. */
function binaryComp() {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('y'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [b0, b1])
}

/** Ternary comp G(a,b,c): node `f g` — output=b0, free var f=b1, free var g=b2. */
function ternaryComp() {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('f g'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'f' } }])
  const b2 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'g' } }])
  return mkDiagramWithBoundary(b.build(), [b0, b1, b2])
}

describe('diagonalize', () => {
  it('the identity pattern merges nothing — same boundary-pinned form', () => {
    const comp = binaryComp()
    const diag = diagonalize(comp, [0, 1])
    expect(exploreForm(diag.diagram, diag.boundary)).toBe(exploreForm(comp.diagram, comp.boundary))
    expect(diag.boundary).toHaveLength(2)
  })

  it('the ternary identity pattern also merges nothing', () => {
    const comp = ternaryComp()
    const diag = diagonalize(comp, [0, 1, 2])
    expect(exploreForm(diag.diagram, diag.boundary)).toBe(exploreForm(comp.diagram, comp.boundary))
    expect(diag.boundary).toHaveLength(3)
  })

  it('merging two positions collapses the boundary to one wire, unioning endpoints', () => {
    const comp = binaryComp()
    const diag = diagonalize(comp, [0, 0])
    expect(diag.boundary).toHaveLength(1)
    const merged = diag.diagram.wires[diag.boundary[0]!]!
    // the single node's output AND free var now ride the one merged wire
    expect(merged.endpoints).toHaveLength(2)
    const kinds = merged.endpoints.map((ep) => ep.port.kind).sort()
    expect(kinds).toEqual(['freeVar', 'output'])
  })

  it('does not mutate the input comprehension', () => {
    const comp = binaryComp()
    const before = exploreForm(comp.diagram, comp.boundary)
    diagonalize(comp, [0, 0])
    expect(exploreForm(comp.diagram, comp.boundary)).toBe(before)
    expect(comp.boundary).toHaveLength(2)
  })

  it('the collapsed order is first-appearance of the classes', () => {
    // (0,1)-merge keeps c separate as the second boundary entry
    const comp = ternaryComp()
    const diag = diagonalize(comp, [0, 0, 1])
    expect(diag.boundary).toHaveLength(2)
    // first entry = merged {a,b}, second = c (q_0), by first appearance
    const w0 = diag.diagram.wires[diag.boundary[0]!]!
    const w1 = diag.diagram.wires[diag.boundary[1]!]!
    expect(w0.endpoints).toHaveLength(2)
    expect(w1.endpoints).toHaveLength(1)
  })

  it('rejects an alias pattern whose length is not the arity', () => {
    expect(() => diagonalize(binaryComp(), [0]))
      .toThrowError(/alias pattern length 1 does not match comprehension arity 2/)
  })
})

describe('applyComprehensionAbstract — diagonal occurrences', () => {
  it('abstracts a diagonal occurrence φ(x,x): both arg ports land on one wire', () => {
    // occurrence: node `y` with output and free var BOTH on wire x
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    const out = applyComprehensionAbstract(d, wrap, binaryComp(), [occ])

    // the term node is gone, replaced by one arity-2 atom
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(Object.values(out.nodes).filter((m) => m.kind === 'term')).toHaveLength(0)
    const atomId = atoms[0]![0]
    // both arg-0 and arg-1 ports of that atom ride the single wire x
    const xEps = out.wires[x]!.endpoints
    expect(xEps).toHaveLength(2)
    expect(xEps.every((ep) => ep.node === atomId)).toBe(true)
    expect(xEps.map((ep) => ep.port.kind === 'arg' && ep.port.index).sort()).toEqual([0, 1])
  })

  it('abstracts a triple diagonal ψ(x,x,x): all three arg ports on one wire', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
      { node: n, port: { kind: 'freeVar', name: 'g' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x, x] }
    const out = applyComprehensionAbstract(d, wrap, ternaryComp(), [occ])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const atomId = atoms[0]![0]
    const xEps = out.wires[x]!.endpoints
    expect(xEps).toHaveLength(3)
    expect(xEps.every((ep) => ep.node === atomId)).toBe(true)
    expect(xEps.map((ep) => ep.port.kind === 'arg' && ep.port.index).sort()).toEqual([0, 1, 2])
  })

  it('abstracts a mixed diagonal ψ(x,x,y): args 0,1 on x and arg 2 on y', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
    ])
    const y = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x, y] }
    const out = applyComprehensionAbstract(d, wrap, ternaryComp(), [occ])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const atomId = atoms[0]![0]
    const xEps = out.wires[x]!.endpoints
    expect(xEps.map((ep) => ep.port.kind === 'arg' && ep.port.index).sort()).toEqual([0, 1])
    expect(xEps.every((ep) => ep.node === atomId)).toBe(true)
    const yEps = out.wires[y]!.endpoints
    expect(yEps).toHaveLength(1)
    expect(yEps[0]!.node).toBe(atomId)
    expect(yEps[0]!.port.kind === 'arg' && yEps[0]!.port.index).toBe(2)
  })

  it('a NEAR-diagonal occurrence (one node different) is refused by fingerprint', () => {
    // occurrence body is `\z. y` (one lambda more than the comp body `y`),
    // output and free var both on one wire; the diagonalized comp does not match.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\z. y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => applyComprehensionAbstract(d, wrap, binaryComp(), [occ]))
      .toThrowError(/does not match the comprehension/)
  })

  it('an occurrence matching the UNdiagonalized comp is refused under a diagonal call', () => {
    // node `y` with output on x and free var on a DISTINCT wire z: this is the
    // non-diagonal φ(x,z). Calling with args [x,x] leaves z unused → refuse.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => applyComprehensionAbstract(d, wrap, binaryComp(), [occ]))
      .toThrowError(/is not used by any argument position/)
  })

  it('a diagonal occurrence is refused under a NON-diagonal call (arg wire not an attachment)', () => {
    // node `y` with output AND free var both on x (a genuine diagonal). Calling
    // with args [x, z] references z, which is not one of the occurrence's wires.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ])
    const z = h.wire(h.root, [])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, z] }
    expect(() => applyComprehensionAbstract(d, wrap, binaryComp(), [occ]))
      .toThrowError(/argument wire '.*' is not one of its attachment wires/)
  })

  it('the polarity gate still fires for a diagonal occurrence in a negative region', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('y'))
    const x = h.wire(cut, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => applyComprehensionAbstract(d, wrap, binaryComp(), [occ]))
      .toThrowError(/requires a positive region/)
  })

  it('refuses an arity mismatch: too few argument positions for the comp', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x] }
    expect(() => applyComprehensionAbstract(d, wrap, binaryComp(), [occ]))
      .toThrowError(/has 1 argument positions but the comprehension has arity 2/)
  })
})
