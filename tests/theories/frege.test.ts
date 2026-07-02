import { describe, it, expect } from 'vitest'
import { buildFregeTheory, natRelation } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'
import { parseTerm } from '../../src/kernel/term/parse'
import { termEq } from '../../src/kernel/term/term'

const pZero = parseTerm('ZERO', new Set(['ZERO']))

describe('the bundled Frege theory', () => {
  it('verifies end to end: the nat relation resolves, no theorems bundled', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual([])
    expect(ctx.relations.has('nat')).toBe(true)
  })

  it('round-trips through the file format with re-verification', () => {
    const theory = buildFregeTheory()
    const text = JSON.stringify(theoryToJson(theory))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(0)
    expect(ctx.relations.has('nat')).toBe(true)
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
    // the standalone builder and the bundled relation agree
    expect(boundaryFingerprint(natRelation())).toBe(boundaryFingerprint(theory.relations['nat']!))
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
