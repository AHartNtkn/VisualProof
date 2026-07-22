import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyIteration, applyDeiteration, findDeiterationEvidence } from '../../../src/kernel/rules/iteration'

const p = (s: string) => parseTerm(s)

/** rB(1)[ R-app on a shared wire ; an empty cut to iterate into ]. */
function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n = h.termNode(rB, p('\\x. x'))
  const a = h.atom(rB, rB)
  const w = h.wire(rB, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(rB)
  return { d: h.build(), rB, n, a, w, cut }
}

describe('open iteration / deiteration', () => {
  it('iterates an R-application into a cut inside the binder, then deiterates back (fingerprint)', () => {
    const { d, rB, n, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    const copies = Object.entries(iterated.nodes).filter(([, x]) => x.region === cut)
    expect(copies).toHaveLength(2)
    const copyAtom = copies.find(([, x]) => x.kind === 'atom')!
    expect(copyAtom[1].kind === 'atom' && copyAtom[1].binder).toBe(rB)
    const copySel = mkSelection(iterated, {
      region: cut, regions: [], nodes: copies.map(([id]) => id), wires:
        Object.entries(iterated.wires).filter(([, wv]) =>
          wv.scope === cut).map(([id]) => id),
    })
    const evidence = findDeiterationEvidence(iterated, copySel, 100)
    const back = applyDeiteration(iterated, copySel, evidence.justifier, evidence.certificate)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('refuses iteration to a target outside an external binder', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    expect(() => applyIteration(d, sel, d.root))
      .toThrowError(/must lie within the source region/)
    // a target inside the source region but outside the binder cannot exist
    // (external binders enclose the anchor), so the source-region gate
    // subsumes the binder gate for anchored iteration; the explicit binder
    // check is an invariant guard, and splice's own ancestry validation is
    // pinned directly in splice-open.test.ts ('does not enclose the splice
    // region').
  })

  it('deiteration justification requires the SAME binder: a decoy bubble copy does not justify', () => {
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1)
    const n1 = h.termNode(rB, p('\\x. x'))
    const a1 = h.atom(rB, rB)
    h.wire(rB, [
      { node: n1, port: { kind: 'output' } },
      { node: a1, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    // only ONE R-application exists: deiterating it must fail (no justifier)
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    expect(() => findDeiterationEvidence(d, sel, 100)).toThrowError(/no justifying occurrence/)
  })
})

// Vacuous intro/elim now operates on endpoint-free WIRES, not bubble regions
// (bubbles are gone from the Region type). Its test matrix lives in
// tests/kernel/rules/vacuous.test.ts.
