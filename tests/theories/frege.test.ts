import { describe, it, expect } from 'vitest'
import { buildFregeTheory, natRelation } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'
import type { Diagram, DiagramNode, WireId } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyTheorem, type Theorem } from '../../src/kernel/proof/theorem'

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
    expect([...ctx.theorems.keys()]).toEqual(['plusAssoc', 'plusLeftUnit', 'plusRightUnit', 'zeroIsNat', 'succNat', 'oneIsNat', 'succShiftS', 'plusComm'])
    expect([...ctx.relations.keys()].sort()).toEqual(['nat', 'plus', 'succ', 'zero'])
  })

  it('round-trips through the file format with re-verification', () => {
    const text = JSON.stringify(theoryToJson(buildFregeTheory()))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(8)
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

  it('zeroIsNat: Zero(z) ⟹ nat(z) ∧ Zero(z); boundary [z]; nat and zero co-ride z', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'zeroIsNat')!
    expect(t.lhs.boundary).toHaveLength(1)
    expect(t.rhs.boundary).toHaveLength(1)
    // lhs is the bare Zero premise; rhs adds the nat guard, retaining Zero
    expect(refKinds(t.lhs)).toEqual(['zero/1'])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'zero/1'])
    // both the produced nat guard and the retained Zero ride the boundary z-line
    const rd = t.rhs.diagram
    const [wz] = t.rhs.boundary
    const natId = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const zeroId = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'zero')![0]
    expect(argWire(rd, natId, 0)).toBe(wz)
    expect(argWire(rd, zeroId, 0)).toBe(wz)
  })

  it('succNat: nat(n) ∧ Succ(n,s) ⟹ Succ(n,s) ∧ nat(s); guard rides the successor', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'succNat')!
    expect(t.lhs.boundary).toHaveLength(2)
    expect(t.rhs.boundary).toHaveLength(2)
    expect(refKinds(t.lhs)).toEqual(['nat/1', 'succ/2'])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'succ/2'])
    // lhs: nat guards n = Succ's predecessor (nat.arg0 and succ.arg0 both on wn)
    const ld = t.lhs.diagram
    const [wn] = t.lhs.boundary
    const lNat = Object.entries(ld.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const lSuc = Object.entries(ld.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    expect(argWire(ld, lNat, 0)).toBe(wn)
    expect(argWire(ld, lSuc, 0)).toBe(wn)
    // rhs: nat now guards s = Succ's output (nat.arg0 and succ.arg1 both on ws)
    const rd = t.rhs.diagram
    const ws = t.rhs.boundary[1]
    const rNat = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const rSuc = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    expect(argWire(rd, rNat, 0)).toBe(ws)
    expect(argWire(rd, rSuc, 1)).toBe(ws)
  })

  it('oneIsNat: Zero(z) ∧ Succ(z,o) ⟹ nat(o) ∧ Zero(z) ∧ Succ(z,o); guard on the successor', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'oneIsNat')!
    expect(t.lhs.boundary).toHaveLength(2)
    expect(t.rhs.boundary).toHaveLength(2)
    expect(refKinds(t.lhs)).toEqual(['succ/2', 'zero/1'])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'succ/2', 'zero/1'])
    // the produced nat guards o = the successor output (o-line is boundary[1])
    const rd = t.rhs.diagram
    const wo = t.rhs.boundary[1]
    const rNat = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const rSuc = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    expect(argWire(rd, rNat, 0)).toBe(wo)
    expect(argWire(rd, rSuc, 1)).toBe(wo)
  })

  it('smoke: oneIsNat certifies nat(1), which then satisfies a plusComm citation', () => {
    const theory = buildFregeTheory()
    const oneIsNat = theory.theorems.find((x) => x.name === 'oneIsNat')!
    const plusComm = theory.theorems.find((x) => x.name === 'plusComm')!

    // host: Zero(z) ∧ Succ(z,o) ∧ nat(b) ∧ Plus(o,b,sum)
    const h = new DiagramBuilder()
    const zRef = h.ref(h.root, 'zero', 1)
    const sRef = h.ref(h.root, 'succ', 2)
    const bNat = h.ref(h.root, 'nat', 1)
    const pRef = h.ref(h.root, 'plus', 3)
    const wz = h.wire(h.root, [{ node: zRef, port: { kind: 'arg', index: 0 } }, { node: sRef, port: { kind: 'arg', index: 0 } }])
    const wo = h.wire(h.root, [{ node: sRef, port: { kind: 'arg', index: 1 } }, { node: pRef, port: { kind: 'arg', index: 0 } }])
    const wb = h.wire(h.root, [{ node: bNat, port: { kind: 'arg', index: 0 } }, { node: pRef, port: { kind: 'arg', index: 1 } }])
    const wsum = h.wire(h.root, [{ node: pRef, port: { kind: 'arg', index: 2 } }])
    const d = h.build()

    // certify nat(o) — o is Succ of a Zero, i.e. 1
    const d1 = applyTheorem(d, oneIsNat, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [zRef, sRef], wires: [] }), args: [wz, wo],
    }, 'forward')
    const natO = Object.entries(d1.nodes).find(([id, n]) =>
      n.kind === 'ref' && n.defId === 'nat' && id !== bNat &&
      d1.wires[wo]!.endpoints.some((ep) => ep.node === id))![0]
    expect(natO).toBeDefined()

    // feed nat(1) ∧ nat(b) ∧ Plus(o,b,sum) into plusComm → Plus(b,o,sum)
    const d2 = applyTheorem(d1, plusComm, {
      sel: mkSelection(d1, { region: d1.root, regions: [], nodes: [natO, bNat, pRef], wires: [] }), args: [wo, wb, wsum],
    }, 'forward')
    // the Plus now reads (b, o, sum): its first argument rides wb
    const plusAfter = Object.entries(d2.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    expect(argWire(d2, plusAfter, 0)).toBe(wb)
    expect(argWire(d2, plusAfter, 1)).toBe(wo)
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
