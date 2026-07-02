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
  it('verifies end to end: nat resolves, conversion theorems + succShiftS replay', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['plusAssoc', 'plusLeftUnit', 'plusRightUnit', 'succShiftS'])
    expect(ctx.relations.has('nat')).toBe(true)
  })

  it('round-trips through the file format with re-verification', () => {
    const theory = buildFregeTheory()
    const text = JSON.stringify(theoryToJson(theory))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(4)
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

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
