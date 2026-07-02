import { describe, it, expect } from 'vitest'
import { buildFregeTheory, natRelation } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'
import type { Diagram, DiagramNode, WireId } from '../../src/kernel/diagram/diagram'
import type { Theorem } from '../../src/kernel/proof/theorem'

/** The reference nodes of a theorem side, as `defId/arity` strings, sorted. */
function refKinds(side: Theorem['lhs']): string[] {
  return Object.values(side.diagram.nodes)
    .filter((n): n is Extract<DiagramNode, { kind: 'ref' }> => n.kind === 'ref')
    .map((n) => `${n.defId}/${n.arity}`).sort()
}

/** The wire carrying node `id`'s argument at `index`. */
function argWire(d: Diagram, id: string, index: number): WireId {
  return Object.entries(d.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === id && ep.port.kind === 'arg' && ep.port.index === index))![0]
}

describe('the bundled Frege theory', () => {
  it('verifies end to end: relations resolve, conversion + induction theorems replay', () => {
    const ctx = verifyTheory(buildFregeTheory())
    expect([...ctx.theorems.keys()]).toEqual(['plusAssoc', 'plusLeftUnit', 'plusRightUnit', 'succShiftS', 'plusComm'])
    expect([...ctx.relations.keys()].sort()).toEqual(['nat', 'plus', 'succ', 'zero'])
  })

  it('round-trips through the file format with re-verification', () => {
    const text = JSON.stringify(theoryToJson(buildFregeTheory()))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(5)
    expect(ctx.relations.has('nat')).toBe(true)
  })

  it('the relations are pure: no term node anywhere carries a term constant', () => {
    const hasConst = (t: DiagramNode): boolean => {
      if (t.kind !== 'term') return false
      const walk = (u: { kind: string; body?: unknown; fn?: unknown; arg?: unknown }): boolean =>
        u.kind === 'const' ||
        (u.body !== undefined && walk(u.body as never)) ||
        (u.fn !== undefined && (walk(u.fn as never) || walk(u.arg as never)))
      return walk(t.term as never)
    }
    const theory = buildFregeTheory()
    for (const rel of Object.values(theory.relations)) {
      expect(Object.values(rel.diagram.nodes).some(hasConst)).toBe(false)
    }
  })

  it('plusLeftUnit / plusRightUnit: Zero + Plus premises reduce the sum to an identity', () => {
    const theory = buildFregeTheory()
    for (const name of ['plusLeftUnit', 'plusRightUnit']) {
      const t = theory.theorems.find((x) => x.name === name)!
      expect(t.lhs.boundary).toHaveLength(2)
      expect(t.rhs.boundary).toHaveLength(2)
      // lhs: exactly a zero reference and a plus reference
      expect(refKinds(t.lhs)).toEqual(['plus/3', 'zero/1'])
      // rhs: no references left — a single identity term node o = a
      expect(refKinds(t.rhs)).toEqual([])
      const rhsTerms = Object.values(t.rhs.diagram.nodes).filter((n) => n.kind === 'term')
      expect(rhsTerms).toHaveLength(1)
    }
  })

  it('plusAssoc: (a+b)+c into a+(b+c), two Plus references per side, 4-line boundary', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'plusAssoc')!
    expect(t.lhs.boundary).toHaveLength(4)
    expect(t.rhs.boundary).toHaveLength(4)
    expect(refKinds(t.lhs)).toEqual(['plus/3', 'plus/3'])
    expect(refKinds(t.rhs)).toEqual(['plus/3', 'plus/3'])
  })

  it('succShiftS: ℕ-guarded shift; boundary [a,b,o]; lhs Succ∧Plus, rhs Plus∧Succ', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'succShiftS')!
    expect(t.lhs.boundary).toHaveLength(3)
    expect(t.rhs.boundary).toHaveLength(3)
    // ℕ(a) is a folded guard on both sides
    expect(refKinds(t.lhs)).toEqual(['nat/1', 'plus/3', 'succ/2'])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'plus/3', 'succ/2'])
    // the boundary is exactly [wa, wb, wo]; on the lhs the nat guards a and the
    // Plus reads a as its first argument (both nat.arg0 and plus.arg0 ride wa)
    const ld = t.lhs.diagram
    const natId = Object.entries(ld.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const plusId = Object.entries(ld.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    const [wa] = t.lhs.boundary
    expect(argWire(ld, natId, 0)).toBe(wa)
    expect(argWire(ld, plusId, 0)).toBe(wa)
    // on the rhs the successor lands on the output: Succ.arg1 rides wo
    const rd = t.rhs.diagram
    const succId = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    const wo = t.rhs.boundary[2]
    expect(argWire(rd, succId, 1)).toBe(wo)
  })

  it('plusComm: two ℕ guards + Plus(a,b,o) ⟹ two ℕ guards + Plus(b,a,o), args crossed', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'plusComm')!
    expect(t.lhs.boundary).toHaveLength(3)
    expect(t.rhs.boundary).toHaveLength(3)
    expect(refKinds(t.lhs)).toEqual(['nat/1', 'nat/1', 'plus/3'])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'nat/1', 'plus/3'])
    const [wa, wb, wo] = t.lhs.boundary
    // lhs Plus reads (a, b, o); rhs Plus reads (b, a, o) — the commutation cross
    const lp = Object.entries(t.lhs.diagram.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    expect([argWire(t.lhs.diagram, lp, 0), argWire(t.lhs.diagram, lp, 1), argWire(t.lhs.diagram, lp, 2)]).toEqual([wa, wb, wo])
    const [wa2, wb2, wo2] = t.rhs.boundary
    const rp = Object.entries(t.rhs.diagram.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    expect([argWire(t.rhs.diagram, rp, 0), argWire(t.rhs.diagram, rp, 1), argWire(t.rhs.diagram, rp, 2)]).toEqual([wb2, wa2, wo2])
  })

  it('the bundled ℕ is inCutNat: the zero-evidence is inside the guard, not root-witnessable', () => {
    // Non-vacuity lock: the zero-evidence is a `zero` reference living strictly
    // inside the guard bubble, its arg line scoped there — no top-level zero
    // witness leaks. The ONLY root-scoped wire is the boundary x-line.
    const nat = buildFregeTheory().relations['nat']!
    const d = nat.diagram
    const zeroEntry = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'zero')
    expect(zeroEntry).toBeDefined()
    const [zeroId, zeroNode] = zeroEntry!
    // (a) the zero-evidence reference is not a child of the body root
    expect(zeroNode.region).not.toBe(d.root)
    // (b) its argument line's scope is NOT the body root
    const w0 = Object.entries(d.wires).find(
      ([, w]) => w.endpoints.some((ep) => ep.node === zeroId && ep.port.kind === 'arg'))
    expect(w0).toBeDefined()
    expect(w0![1].scope).not.toBe(d.root)
    // (c) the ONLY root-scoped wire is the boundary x-line
    const rootWires = Object.entries(d.wires).filter(([, w]) => w.scope === d.root)
    expect(rootWires.map(([id]) => id)).toEqual([...nat.boundary])
  })

  it('the named ℕ relation is arity 1 with a stable fingerprint', () => {
    const theory = buildFregeTheory()
    expect(theory.relations['nat']).toBeDefined()
    expect(theory.relations['nat']!.boundary).toHaveLength(1)
    expect(boundaryFingerprint(theory.relations['nat']!)).toBeTruthy()
    expect(boundaryFingerprint(natRelation())).toBe(boundaryFingerprint(theory.relations['nat']!))
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
