import { describe, it, expect } from 'vitest'
import { buildFregeTheory, natRelation } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'
import { parseTerm } from '../../src/kernel/term/parse'
import { termEq, type Term } from '../../src/kernel/term/term'
import type { Theorem } from '../../src/kernel/proof/theorem'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const pZero = parseTerm('ZERO', new Set(['ZERO']))

/** The sole root term node's term on a theorem side. */
function soleTerm(side: Theorem['lhs']): Term {
  const d = side.diagram
  const node = Object.values(d.nodes).find((n) => n.kind === 'term' && n.region === d.root)
  if (node === undefined || node.kind !== 'term') throw new Error('no root term node')
  return node.term
}

describe('the bundled Frege theory', () => {
  it('verifies end to end: nat resolves, conversion + induction theorems replay', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['plusAssoc', 'plusLeftUnit', 'plusRightUnit', 'succShiftS', 'plusComm'])
    expect(ctx.relations.has('nat')).toBe(true)
  })

  it('round-trips through the file format with re-verification', () => {
    const theory = buildFregeTheory()
    const text = JSON.stringify(theoryToJson(theory))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(5)
    expect(ctx.relations.has('nat')).toBe(true)
  })

  it('succShiftS: ℕ-guarded, boundary arity 3, rhs carries the applied SUCC-shift pair', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'succShiftS')!
    expect(t.lhs.boundary).toHaveLength(3)
    expect(t.rhs.boundary).toHaveLength(3)
    // the ℕ(m) guard is folded on BOTH sides (one ref each)
    const lhsRefs = Object.values(t.lhs.diagram.nodes).filter((n) => n.kind === 'ref')
    const rhsRefs = Object.values(t.rhs.diagram.nodes).filter((n) => n.kind === 'ref')
    expect(lhsRefs).toHaveLength(1)
    expect(rhsRefs).toHaveLength(1)
    expect(lhsRefs[0]).toMatchObject({ kind: 'ref', defId: 'nat', arity: 1 })
    // the rhs materializes the exact applied pair PLUS m (SUCC n) —o— SUCC (PLUS m n)
    const rd = t.rhs.diagram
    const has = (term: Term): boolean =>
      Object.values(rd.nodes).some((n) => n.kind === 'term' && n.region === rd.root && termEq(n.term, term))
    expect(has(p('PLUS s0 (SUCC s1)'))).toBe(true)
    expect(has(p('SUCC (PLUS s0 s1)'))).toBe(true)
    // the pair asserts an EQUALITY, not mere coexistence: the two nodes share
    // one output wire, and their m/n args ride the wm/wn boundary lines (s0=wm,
    // s1=wn on both). Without this the two `has` checks pass a statement that
    // merely says both terms exist on unrelated lines.
    const node = (term: Term): string =>
      Object.entries(rd.nodes).find(([, n]) => n.kind === 'term' && n.region === rd.root && termEq(n.term, term))![0]
    const outOf = (id: string): string =>
      Object.entries(rd.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === id && ep.port.kind === 'output'))![0]
    const argOf = (id: string, name: string): string =>
      Object.entries(rd.wires).find(([, w]) =>
        w.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === name))![0]
    const [wm, wn] = t.rhs.boundary
    const nP = node(p('PLUS s0 (SUCC s1)'))
    const nS = node(p('SUCC (PLUS s0 s1)'))
    expect(outOf(nP)).toBe(outOf(nS))
    expect(argOf(nP, 's0')).toBe(wm)
    expect(argOf(nP, 's1')).toBe(wn)
    expect(argOf(nS, 's0')).toBe(wm)
    expect(argOf(nS, 's1')).toBe(wn)
  })

  it('the bundled ℕ is inCutNat: the zero-evidence is inside the guard, not root-witnessable', () => {
    // Non-vacuity lock. In the vacuous root-scoped encoding, ℕ(x)=∃w0¬∃R[…] and
    // any non-zero witnesses w0, making ℕ true of everything. inCutNat scopes the
    // base line INSIDE the guard bubble, so no top-level zero witness leaks: the
    // ZERO node lives strictly inside the guard structure AND its output line's
    // scope is not the body root.
    const nat = buildFregeTheory().relations['nat']!
    const d = nat.diagram
    const zeroEntry = Object.entries(d.nodes).find(
      ([, n]) => n.kind === 'term' && termEq(n.term, pZero),
    )
    expect(zeroEntry).toBeDefined()
    const [zeroId, zeroNode] = zeroEntry!
    // (a) the zero-evidence node is not a child of the body root
    expect(zeroNode.region).not.toBe(d.root)
    // (b) the zero-evidence output line's scope is NOT the body root
    const w0 = Object.entries(d.wires).find(
      ([, w]) => w.endpoints.some((ep) => ep.node === zeroId && ep.port.kind === 'output'),
    )
    expect(w0).toBeDefined()
    expect(w0![1].scope).not.toBe(d.root)
    // (c) semantic non-vacuity: the ONLY root-scoped wire is the boundary x-line.
    // No evidence wire (zero witness or the successor/closure structure) leaks to
    // the body root, so ∃w0 and all of R live strictly inside the guard cut — the
    // reading ¬∃R∃w0[…], not a surface ∃w0 witnessable by any non-zero.
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

  it('plusAssoc rewrites (a+b)+c into a+(b+c) with a 4-line boundary', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'plusAssoc')!
    expect(termEq(soleTerm(t.lhs), p('PLUS (PLUS s0 s1) s2'))).toBe(true)
    expect(termEq(soleTerm(t.rhs), p('PLUS s0 (PLUS s1 s2)'))).toBe(true)
    expect(t.lhs.boundary).toHaveLength(4) // output + s0,s1,s2
    expect(t.rhs.boundary).toHaveLength(4)
  })

  it('plusLeftUnit rewrites 0+n into n; plusRightUnit rewrites n+0 into n', () => {
    const theory = buildFregeTheory()
    const left = theory.theorems.find((x) => x.name === 'plusLeftUnit')!
    expect(termEq(soleTerm(left.lhs), p('PLUS ZERO s0'))).toBe(true)
    expect(termEq(soleTerm(left.rhs), p('s0'))).toBe(true)
    expect(left.lhs.boundary).toHaveLength(2)
    const right = theory.theorems.find((x) => x.name === 'plusRightUnit')!
    expect(termEq(soleTerm(right.lhs), p('PLUS s0 ZERO'))).toBe(true)
    expect(termEq(soleTerm(right.rhs), p('s0'))).toBe(true)
    expect(right.rhs.boundary).toHaveLength(2)
  })

  it('plusComm: two folded ℕ guards; rhs is exactly the commutation pair', () => {
    const t = buildFregeTheory().theorems.find((x) => x.name === 'plusComm')!
    expect(t.lhs.boundary).toHaveLength(2)
    expect(t.rhs.boundary).toHaveLength(2)
    // ℕ(a) ∧ ℕ(b) folded on both sides
    expect(Object.values(t.lhs.diagram.nodes).filter((n) => n.kind === 'ref')).toHaveLength(2)
    expect(Object.values(t.rhs.diagram.nodes).filter((n) => n.kind === 'ref')).toHaveLength(2)
    // the lhs is the two folded guards and NOTHING else (no root term nodes): the
    // hypothesis is exactly ℕ(a) ∧ ℕ(b), not a strengthened premise.
    expect(Object.values(t.lhs.diagram.nodes).filter((n) => n.kind === 'term')).toHaveLength(0)
    // rhs audit: exactly two PLUS-pair term nodes at root, sharing one output
    const rd = t.rhs.diagram
    const pairs = Object.entries(rd.nodes).filter(
      ([, n]) => n.kind === 'term' && n.region === rd.root && termEq(n.term, p('PLUS s0 s1')),
    )
    expect(pairs).toHaveLength(2)
    // no OTHER term nodes at the root (only the two PLUS nodes)
    const rootTerms = Object.values(rd.nodes).filter((n) => n.kind === 'term' && n.region === rd.root)
    expect(rootTerms).toHaveLength(2)
    const outWire = (id: string): string =>
      Object.entries(rd.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === id && ep.port.kind === 'output'))![0]
    expect(outWire(pairs[0]![0])).toBe(outWire(pairs[1]![0]))
    // the pair is CROSSED: one node reads PLUS a b, the other PLUS b a. Without
    // this the assertions above pass a trivial reflexive PLUS a b —o— PLUS a b,
    // certifying reflexivity as commutativity. Pin the arg wiring against the
    // [wa, wb] boundary: the two nodes' (s0-wire, s1-wire) signatures must be
    // exactly {(wa, wb), (wb, wa)}.
    const [wa, wb] = t.rhs.boundary
    const wireOfPort = (id: string, name: string): string =>
      Object.entries(rd.wires).find(([, w]) =>
        w.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === name),
      )![0]
    const sig = (id: string): string => `${wireOfPort(id, 's0')},${wireOfPort(id, 's1')}`
    expect(new Set([sig(pairs[0]![0]), sig(pairs[1]![0])])).toEqual(new Set([`${wa},${wb}`, `${wb},${wa}`]))
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
