import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyComprehensionAbstract, applyComprehensionInstantiate, diagonalize } from '../../../src/kernel/rules/comprehension'
import type { Diagram, NodeId, WireId } from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)

/** Ternary comp G(a,b,c): node `f g` — output=b0, free var f=b1, free var g=b2. */
function ternaryComp() {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('f g'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'f' } }])
  const b2 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'g' } }])
  return mkDiagramWithBoundary(b.build(), [b0, b1, b2])
}

/** Binary comp G(a,b): node `y` — output=b0, free var y=b1. */
function binaryComp() {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('y'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [b0, b1])
}

/**
 * A (0,1)-merge occurrence of the ternary body `f g`: output AND free var f
 * ride wire x; free var g rides a DISTINCT wire y. This occurrence IS the
 * diagonalized comp under alias pattern (0,0,1) and nothing else. Every
 * cross-pattern call must refuse it; only the honest (0,1) call verifies.
 */
function merge01Occurrence() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('f g'))
  const x = h.wire(h.root, [
    { node: n, port: { kind: 'output' } },
    { node: n, port: { kind: 'freeVar', name: 'f' } },
  ])
  const y = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }])
  const d = h.build()
  const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
  return { d, x, y, wrap: sel(), sel }
}

describe('Plan 16 adversarial — diagonalized-form confusion (Part A1)', () => {
  it('the honest (0,1)-merge call VERIFIES (positive control)', () => {
    const { d, x, y, wrap, sel } = merge01Occurrence()
    expect(() => applyComprehensionAbstract(d, wrap, ternaryComp(), [{ sel: sel(), args: [x, x, y] }]))
      .not.toThrow()
  })

  it('a (0,1)-merge occurrence is REFUSED under a (0,2)-merge call', () => {
    // args [x,y,x]: positions 0,2 alias → diagonalize merges comp boundaries
    // out+g. But the occurrence merges out+f. Genuine fingerprint mismatch —
    // not caught by the unused/arity gates (both x and y are used).
    const { d, x, y, wrap, sel } = merge01Occurrence()
    expect(() => applyComprehensionAbstract(d, wrap, ternaryComp(), [{ sel: sel(), args: [x, y, x] }]))
      .toThrowError(/does not match the comprehension/)
  })

  it('a (0,1)-merge occurrence is REFUSED under a (1,2)-merge call', () => {
    // args [x,y,y]: positions 1,2 alias → diagonalize merges comp f+g. The
    // occurrence merges out+f. Fingerprint mismatch.
    const { d, x, y, wrap, sel } = merge01Occurrence()
    expect(() => applyComprehensionAbstract(d, wrap, ternaryComp(), [{ sel: sel(), args: [x, y, y] }]))
      .toThrowError(/does not match the comprehension/)
  })

  it('a (0,1)-merge occurrence is REFUSED under a FULLY diagonal (0,1,2) call', () => {
    // args [x,x,x]: the g-carrying wire y is never referenced → unused gate.
    const { d, x, wrap, sel } = merge01Occurrence()
    expect(() => applyComprehensionAbstract(d, wrap, ternaryComp(), [{ sel: sel(), args: [x, x, x] }]))
      .toThrowError(/is not used by any argument position/)
  })

  it('a fully-diagonal occurrence φ(x,x,x) is REFUSED under a partial (0,1) call', () => {
    // Occurrence: out, f, g all on x. A (0,1)-merge call [x,x,z] references a
    // wire z that is not one of the occurrence's attachments.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
      { node: n, port: { kind: 'freeVar', name: 'g' } },
    ])
    const z = h.wire(h.root, [])
    const d = h.build()
    const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyComprehensionAbstract(d, sel(), ternaryComp(), [{ sel: sel(), args: [x, x, z] }]))
      .toThrowError(/is not one of its attachment wires/)
  })
})

describe('Plan 16 adversarial — unused-attachment smuggling (Part A2)', () => {
  it('a dangling third wire hidden behind an aliased pair is REFUSED', () => {
    // Binary comp (arity 2). Occurrence body `f g` has THREE ports: out+f are
    // aliased onto x (the pair that "covers" the arity), while g dangles out on
    // wire w. Content is leaking out of the abstraction through w; the
    // every-attachment-used gate must name w.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
    ])
    const w = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }])
    const d = h.build()
    const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyComprehensionAbstract(d, sel(), binaryComp(), [{ sel: sel(), args: [x, x] }]))
      .toThrowError(new RegExp(`attachment wire '${w}' is not used by any argument position`))
  })
})

describe('Plan 16 adversarial — merge collision (Part A3)', () => {
  it('collapsing all three ternary positions yields ONE valid boundary wire with 3 distinct endpoints', () => {
    // out, f, g of the single node all merge onto one wire. mkDiagram (called
    // inside diagonalize) must accept it: the three ports are distinct, so the
    // union carries no duplicate endpoint.
    const diag = diagonalize(ternaryComp(), [0, 0, 0])
    expect(diag.boundary).toHaveLength(1)
    const merged = diag.diagram.wires[diag.boundary[0]!]!
    expect(merged.endpoints).toHaveLength(3)
    const kinds = merged.endpoints.map((ep) => ep.port.kind).sort()
    expect(kinds).toEqual(['freeVar', 'freeVar', 'output'])
    // no two endpoints share a (node, port) — the partition invariant held
    const keys = merged.endpoints.map((ep) => `${ep.node}|${JSON.stringify(ep.port)}`)
    expect(new Set(keys).size).toBe(3)
  })
})

describe('Plan 16 adversarial — instantiate/abstract asymmetry on the instantiated result (Part A4)', () => {
  // ∃R.R(x,x) with the bubble at a NEGATIVE region (cut1) whose atom lives one
  // cut deeper — so the atom's region (inner) is POSITIVE (cut depth 2). After
  // instantiation the produced φ(x,x) sits at that positive region, where
  // re-abstraction is legal. This exercises the round-trip on the ACTUAL
  // instantiation output, not a hand-built φ — the asymmetry the plan demands:
  // the instantiated diagonal must re-abstract diagonally and REFUSE a
  // non-diagonal re-abstraction (its sole attachment is the shared wire).
  function instantiatedDiagonalPhi(): {
    inst: Diagram; phiId: NodeId; region: string; xId: WireId; zId: WireId
  } {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const bub = h.bubble(cut1, 2)
    const inner = h.cut(bub)
    const atom = h.atom(inner, bub)
    h.wire(inner, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    // a real, independent wire at the same region — a non-attachment decoy
    const zId = h.wire(inner, [])
    const inst = applyComprehensionInstantiate(h.build(), bub, binaryComp(), [])
    const phiEntry = Object.entries(inst.nodes).find(([, n]) => n.kind === 'term')
    if (phiEntry === undefined) throw new Error('instantiation produced no φ term node')
    const xEntry = Object.entries(inst.wires).find(
      ([, w]) => w.endpoints.length === 2 && w.endpoints.every((ep) => ep.node === phiEntry[0]),
    )
    if (xEntry === undefined) throw new Error('instantiation produced no diagonal wire')
    return { inst, phiId: phiEntry[0], region: phiEntry[1].region, xId: xEntry[0], zId }
  }

  it('the instantiated φ(x,x) re-abstracts DIAGONALLY back to one atom on the shared wire', () => {
    const { inst, phiId, region, xId } = instantiatedDiagonalPhi()
    const sel = () => mkSelection(inst, { region, regions: [], nodes: [phiId], wires: [] })
    const out = applyComprehensionAbstract(inst, sel(), binaryComp(), [{ sel: sel(), args: [xId, xId] }])
    const atoms = Object.entries(out.nodes).filter(([, n]) => n.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const aId = atoms[0]![0]
    const xEps = out.wires[xId]!.endpoints
    expect(xEps).toHaveLength(2)
    expect(xEps.every((ep) => ep.node === aId)).toBe(true)
    expect(xEps.map((ep) => ep.port.kind === 'arg' && ep.port.index).sort()).toEqual([0, 1])
  })

  it('the instantiated φ(x,x) REFUSES a non-diagonal re-abstraction naming a real non-attachment wire', () => {
    const { inst, phiId, region, xId, zId } = instantiatedDiagonalPhi()
    const sel = () => mkSelection(inst, { region, regions: [], nodes: [phiId], wires: [] })
    // z is a genuine wire in `inst` but not one of the occurrence's attachments;
    // the diagonal φ's only crossing wire is x, so [x,z] is a non-diagonal claim.
    expect(() => applyComprehensionAbstract(inst, sel(), binaryComp(), [{ sel: sel(), args: [xId, zId] }]))
      .toThrowError(/argument wire '.*' is not one of its attachment wires/)
  })
})

describe('Plan 16 adversarial — instantiation polarity gate (Part A5)', () => {
  it('a diagonal ∃R.R(x,x) at a POSITIVE region refuses instantiation', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 2) // positive: root-level bubble
    const atom = h.atom(bub, bub)
    h.wire(h.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, bub, binaryComp(), []))
      .toThrowError(/requires a negative bubble/)
  })
})
