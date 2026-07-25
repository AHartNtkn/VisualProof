import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyIteration, applyDeiteration, findDeiterationEvidence } from '../../../src/kernel/rules/iteration'

const p = (s: string) => parseTerm(s)

/** A relational atom applied to a term on a shared wire, inside an outer cut
 * (the source region), plus an inner empty cut to iterate into. The atom's head
 * sits on its own relational wire scoped in the outer cut. */
function host() {
  const h = new DiagramBuilder()
  const outer = h.cut(h.root)
  const n = h.termNode(outer, p('\\x. x'))
  const a = h.atom(outer, relSig([IOTA]))
  const w = h.wire(outer, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(outer)
  return { d: h.build(), outer, n, a, w, cut }
}

describe('open iteration / deiteration', () => {
  it('iterates a relational application into a cut, then deiterates back (fingerprint)', () => {
    const { d, outer, n, a, cut } = host()
    const sel = mkSelection(d, { region: outer, regions: [], nodes: [n, a], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    const copies = Object.entries(iterated.nodes).filter(([, x]) => x.region === cut)
    expect(copies).toHaveLength(2)
    const copyAtom = copies.find(([, x]) => x.kind === 'atom')!
    expect(copyAtom[1].kind).toBe('atom')
    const copySel = mkSelection(iterated, {
      region: cut, regions: [], nodes: copies.map(([id]) => id), wires:
        Object.entries(iterated.wires).filter(([, wv]) =>
          wv.scope === cut).map(([id]) => id),
    })
    const evidence = findDeiterationEvidence(iterated, copySel, 100)
    const back = applyDeiteration(iterated, copySel, evidence.justifier, evidence.certificate)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('refuses iteration to a target that does not lie within the source region', () => {
    const { d, outer, n, a } = host()
    const sel = mkSelection(d, { region: outer, regions: [], nodes: [n, a], wires: [] })
    // the root encloses the source cut, so it is not within it
    expect(() => applyIteration(d, sel, d.root))
      .toThrowError(/must lie within the source region/)
  })

  it('deiteration justification requires a matching occurrence: a lone application does not justify', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const a1 = h.atom(h.root, relSig([IOTA]))
    h.wire(h.root, [
      { node: n1, port: { kind: 'output' } },
      { node: a1, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    // only ONE R-application exists: deiterating it must fail (no justifier)
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n1, a1], wires: [] })
    expect(() => findDeiterationEvidence(d, sel, 100)).toThrowError(/no justifying occurrence/)
  })
})
