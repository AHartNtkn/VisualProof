import { describe, it, expect } from 'vitest'
import { buildFregeTheory, natRelation } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryForm } from '../../src/kernel/diagram/canonical/explore'
import type { Diagram, DiagramNode, WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyTheorem, type Theorem } from '../../src/kernel/proof/theorem'
import { applyStep } from '../../src/kernel/proof/step'

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

  it('zeroIsNat: the closed sentence ⟹ ∃z. Zero(z) ∧ nat(z); no boundary; nat and zero co-ride the existential z', () => {
    const theory = buildFregeTheory()
    const t = theory.theorems.find((x) => x.name === 'zeroIsNat')!
    const rules = t.steps.map((step) => step.rule)
    expect(rules).toContain('anchoredWireSplit')
    expect(rules).toContain('anchoredWireContract')
    expect(rules).toContain('relationSpawn')
    expect(rules).toContain('boundRelationSpawn')
    expect(rules).not.toContain('insertion')

    const ctx = verifyTheory(theory)
    let replayed = t.lhs.diagram
    let observedSplit = false
    for (const step of t.steps) {
      if (step.rule !== 'anchoredWireSplit') {
        replayed = applyStep(replayed, step, ctx)
        continue
      }
      observedSplit = true
      const originalWire = replayed.wires[step.wire]
      expect(originalWire).toBeDefined()
      const originalScope = originalWire!.scope
      expect(replayed.regions[originalScope]?.kind).toBe('bubble')
      const baseEndpoint = originalWire!.endpoints.find((endpoint) => {
        const node = replayed.nodes[endpoint.node]
        return node?.kind === 'atom' && node.region === originalScope && endpoint.port.kind === 'arg'
      })
      expect(baseEndpoint).toBeDefined()
      const movedEndpoint = step.endpoints[0]
      expect(movedEndpoint).toBeDefined()

      replayed = applyStep(replayed, step, ctx)

      const retainedWire = replayed.wires[step.wire]
      expect(retainedWire).toBeDefined()
      expect(retainedWire!.scope).toBe(originalScope)
      expect(retainedWire!.endpoints).toContainEqual(baseEndpoint)
      expect(retainedWire!.endpoints).toContainEqual({ node: step.witness, port: { kind: 'output' } })
      expect(retainedWire!.endpoints).not.toContainEqual(movedEndpoint)
    }
    expect(observedSplit).toBe(true)
    // a standalone fact, so both sides are closed sentences (empty boundary)
    expect(t.lhs.boundary).toHaveLength(0)
    expect(t.rhs.boundary).toHaveLength(0)
    // lhs is the blank sheet — no references at all
    expect(refKinds(t.lhs)).toEqual([])
    // rhs asserts nat(z) ∧ Zero(z), both guards riding one existential z-line
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'zero/1'])
    const rd = t.rhs.diagram
    const natId = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const zeroId = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'zero')![0]
    const wz = argWire(rd, natId, 0)
    expect(argWire(rd, zeroId, 0)).toBe(wz)
    // z is a genuine existential: root-scoped but NOT a boundary wire
    expect(rd.wires[wz]!.scope).toBe(rd.root)
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
    const [rwn, ws] = t.rhs.boundary
    const rNat = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const rSuc = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    expect(argWire(rd, rNat, 0)).toBe(ws)
    expect(argWire(rd, rSuc, 1)).toBe(ws)
    // the guard is on the SUCCESSOR, not the predecessor: Succ's arg0 rides the
    // other boundary line, distinct from ws — the statement is nat(succ n), not
    // a degenerate nat(s) ∧ Succ(s,s).
    expect(argWire(rd, rSuc, 0)).toBe(rwn)
    expect(rwn).not.toBe(ws)
  })

  it('oneIsNat: the closed sentence ⟹ ∃z,s. Zero(z) ∧ Succ(z,s) ∧ nat(s); no boundary; guard on the successor', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'oneIsNat')!
    // a standalone fact: closed on both sides
    expect(t.lhs.boundary).toHaveLength(0)
    expect(t.rhs.boundary).toHaveLength(0)
    // lhs is the blank sheet
    expect(refKinds(t.lhs)).toEqual([])
    expect(refKinds(t.rhs)).toEqual(['nat/1', 'succ/2', 'zero/1'])
    const rd = t.rhs.diagram
    const rNat = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const rSuc = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    const rZero = Object.entries(rd.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'zero')![0]
    // the produced nat guards s = the successor output
    const ws = argWire(rd, rNat, 0)
    expect(argWire(rd, rSuc, 1)).toBe(ws)
    // nat(1) is genuinely nat(succ(zero)): the successor's predecessor rides the
    // SAME line as the Zero witness, distinct from the s-line. Without this the
    // "1" could be any Succ, not the successor of a certified zero.
    const wz = argWire(rd, rSuc, 0)
    expect(argWire(rd, rZero, 0)).toBe(wz)
    expect(wz).not.toBe(ws)
    // both z and s are genuine existentials: root-scoped, no boundary
    expect(rd.wires[ws]!.scope).toBe(rd.root)
    expect(rd.wires[wz]!.scope).toBe(rd.root)
  })

  it('smoke: oneIsNat inserts a certified nat(1) that then satisfies a plusComm citation', () => {
    const theory = buildFregeTheory()
    const oneIsNat = theory.theorems.find((x) => x.name === 'oneIsNat')!
    const plusComm = theory.theorems.find((x) => x.name === 'plusComm')!

    // The closed oneIsNat is a standalone fact: cite it (empty selection) at a
    // positive region and it PLANTS its own certified 1 as Zero(z) ∧ Succ(z,s)
    // ∧ nat(s) on fresh existential lines — no host premise needed.
    const d0 = new DiagramBuilder().build()
    const d = applyTheorem(d0, oneIsNat, {
      sel: mkSelection(d0, { region: d0.root, regions: [], nodes: [], wires: [] }), args: [],
    }, 'forward')
    const natS = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'nat')![0]
    const succS = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'succ')![0]
    const ws = argWire(d, natS, 0)                 // the certified 1 line
    expect(argWire(d, succS, 1)).toBe(ws)          // genuinely succ(zero)

    // build the surrounding arithmetic around the certified line: nat(b) and
    // Plus(s,b,sum) reading the certified 1 as its first argument.
    const natB = 'smoke_natB', plusN = 'smoke_plus', wb = 'smoke_wb', wsum = 'smoke_wsum'
    const d1 = mkDiagram({
      root: d.root,
      regions: d.regions,
      nodes: {
        ...d.nodes,
        [natB]: { kind: 'ref', region: d.root, defId: 'nat', arity: 1 },
        [plusN]: { kind: 'ref', region: d.root, defId: 'plus', arity: 3 },
      },
      wires: {
        ...d.wires,
        [ws]: { scope: d.wires[ws]!.scope, endpoints: [...d.wires[ws]!.endpoints, { node: plusN, port: { kind: 'arg', index: 0 } }] },
        [wb]: { scope: d.root, endpoints: [{ node: natB, port: { kind: 'arg', index: 0 } }, { node: plusN, port: { kind: 'arg', index: 1 } }] },
        [wsum]: { scope: d.root, endpoints: [{ node: plusN, port: { kind: 'arg', index: 2 } }] },
      },
    })

    // feed nat(1) ∧ nat(b) ∧ Plus(s,b,sum) into plusComm → Plus(b,s,sum)
    const d2 = applyTheorem(d1, plusComm, {
      sel: mkSelection(d1, { region: d1.root, regions: [], nodes: [natS, natB, plusN], wires: [] }), args: [ws, wb, wsum],
    }, 'forward')
    // the Plus now reads (b, s, sum): its first argument rides wb, the crossed 1
    const plusAfter = Object.entries(d2.nodes).find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    expect(argWire(d2, plusAfter, 0)).toBe(wb)
    expect(argWire(d2, plusAfter, 1)).toBe(ws)
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
    expect(boundaryForm(theory.relations['nat']!)).toBeTruthy()
    expect(boundaryForm(natRelation())).toBe(boundaryForm(theory.relations['nat']!))
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
