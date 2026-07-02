import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'

const p = (s: string) => parseTerm(s)

/** Host: rB(1) holding TWO structurally identical R-applications on separate wires, plus a decoy bubble. */
function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n1 = h.termNode(rB, p('\\x. x'))
  const a1 = h.atom(rB, rB)
  h.wire(rB, [
    { node: n1, port: { kind: 'output' } },
    { node: a1, port: { kind: 'arg', index: 0 } },
  ])
  const n2 = h.termNode(rB, p('\\x. x'))
  const a2 = h.atom(rB, rB)
  h.wire(rB, [
    { node: n2, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const decoy = h.bubble(h.root, 1)
  const n3 = h.termNode(decoy, p('\\x. x'))
  const a3 = h.atom(decoy, decoy)
  h.wire(decoy, [
    { node: n3, port: { kind: 'output' } },
    { node: a3, port: { kind: 'arg', index: 0 } },
  ])
  return { d: h.build(), rB, n1, a1, n2, a2, decoy, a3 }
}

describe('findOccurrences with openBinders', () => {
  it('finds copies bound to the SAME host bubble only', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, rB]])
    const { matches, undecided } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders })
    expect(undecided).toEqual([])
    // both R-applications inside rB match; the decoy bubble's does NOT
    expect(matches).toHaveLength(2)
    for (const m of matches) {
      expect(m.region).toBe(rB)
    }
  })

  it('binder identity is exact: mapping the stub to the decoy finds only the decoy copy', () => {
    const { d, rB, n1, a1, decoy } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, decoy]])
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders })
    expect(matches).toHaveLength(1)
    expect(matches[0]!.region).toBe(decoy)
  })

  it('open patterns without their openBinders map match stub bubbles structurally (closed reading)', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    // no openBinders: the stub is an ordinary arity-1 bubble pattern — the host
    // has no bubble containing exactly one node-pair, so no matches
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50 })
    expect(matches).toHaveLength(0)
  })

  it('rejects malformed openBinders loudly', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const stub = ex.binderStubs[0]!
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([['ghost', rB]]) }))
      .toThrowError(/open binder 'ghost' is not a pattern region/)
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[stub, 'ghost']]) }))
      .toThrowError(/open binder target 'ghost' does not exist/)
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[ex.pattern.diagram.root, rB]]) }))
      .toThrowError(/is not a bubble/)
    // wrong arity: a host bubble of a different arity than the stub
    const h2 = new DiagramBuilder()
    const wide = h2.bubble(h2.root, 2)
    void wide
    const d2 = h2.build()
    expect(() => findOccurrences(d2, ex.pattern, { fuel: 50, openBinders: new Map([[stub, wide]]) }))
      .toThrowError(/open binder arity mismatch/)
  })

  it('binder identity holds across a cut: R(x) under a cut never matches the S copy', () => {
    const h = new DiagramBuilder()
    // decoy: ∃S. S(x)
    const rD = h.bubble(h.root, 1)
    const nD = h.termNode(rD, p('\\x. x'))
    const aD = h.atom(rD, rD)
    h.wire(rD, [
      { node: nD, port: { kind: 'output' } },
      { node: aD, port: { kind: 'arg', index: 0 } },
    ])
    // ∃R. ¬R(x): the R-application sits under a cut
    const rB = h.bubble(h.root, 1)
    const cut = h.cut(rB)
    const nR = h.termNode(cut, p('\\x. x'))
    const aR = h.atom(cut, rB)
    h.wire(cut, [
      { node: nR, port: { kind: 'output' } },
      { node: aR, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [nR, aR], wires: [] })
    const ex = extractSubgraph(d, sel)
    const stub = ex.binderStubs[0]!
    // bound to rB: only the original under the cut — the S copy must NOT match
    const withRB = findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[stub, rB]]) })
    expect(withRB.matches).toHaveLength(1)
    expect(withRB.matches[0]!.region).toBe(cut)
    // bound to rD: only the S copy
    const withRD = findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[stub, rD]]) })
    expect(withRD.matches).toHaveLength(1)
    expect(withRD.matches[0]!.region).toBe(rD)
  })

  it('nested open binders enforce both identities; flipping one target to a decoy kills the match', () => {
    const h = new DiagramBuilder()
    const rB1 = h.bubble(h.root, 1)
    const rB2 = h.bubble(rB1, 1)
    const rB3 = h.bubble(rB2, 1) // decoy that ALSO encloses the content
    const c = h.cut(rB3)
    const a1 = h.atom(c, rB1)
    const a2 = h.atom(c, rB2)
    h.wire(rB1, [{ node: a1, port: { kind: 'arg', index: 0 } }])
    h.wire(rB2, [{ node: a2, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    const sel = mkSelection(d, { region: c, regions: [], nodes: [a1, a2], wires: [] })
    const ex = extractSubgraph(d, sel)
    const [s1, s2] = [ex.binderStubs[0]!, ex.binderStubs[1]!]
    const good = findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[s1, rB1], [s2, rB2]]) })
    expect(good.matches).toHaveLength(1)
    expect(good.matches[0]!.region).toBe(c)
    // same arity, still encloses c: only binder IDENTITY can reject it
    const bad = findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[s1, rB1], [s2, rB3]]) })
    expect(bad.matches).toHaveLength(0)
  })

  it('never matches at a candidate outside the open binder, even when the binder bubble itself is matchable content', () => {
    // pattern: root -> stub(1) -> pb(1) [ atom bound to STUB ]
    const b = new DiagramBuilder()
    const stub = b.bubble(b.root, 1)
    const pb = b.bubble(stub, 1)
    b.atom(pb, stub)
    const pattern = mkDiagramWithBoundary(b.build(), [])
    // host: root [ rB(1) [ atom bound to rB ] ]
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1)
    h.atom(rB, rB)
    const d = h.build()
    // without the candidate enclosure skip, R = root would map pb -> rB and
    // the atom's binder-identity check would PASS (the host atom IS bound to
    // rB) — a forged occurrence placing the free relation variable rB at a
    // region where rB is not in scope
    const { matches } = findOccurrences(d, pattern, { fuel: 50, openBinders: new Map([[stub, rB]]) })
    expect(matches).toHaveLength(0)
  })

  it('rejects ENDPOINTFUL wires scoped at a non-innermost stub loudly', () => {
    // hand-built open pattern: root -> s1(1) -> s2(1) -> atom bound to s1,
    // with the atom's arg wire scoped at s1 (the non-innermost stub)
    const b = new DiagramBuilder()
    const s1 = b.bubble(b.root, 1)
    const s2 = b.bubble(s1, 1)
    const a = b.atom(s2, s1)
    b.wire(s1, [{ node: a, port: { kind: 'arg', index: 0 } }])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    const rB1 = h.bubble(h.root, 1)
    const rB2 = h.bubble(rB1, 1)
    const ha = h.atom(rB2, rB1)
    h.wire(rB1, [{ node: ha, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    expect(() =>
      findOccurrences(d, pattern, { fuel: 50, openBinders: new Map([[s1, rB1], [s2, rB2]]) }),
    ).toThrowError(/above the binder-stub chain are not matchable/)
  })

  it('bare wires scoped at the innermost stub get root (subset) semantics like the closed case', () => {
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1)
    const a = h.atom(rB, rB)
    h.wire(rB, [{ node: a, port: { kind: 'arg', index: 0 } }])
    const bw1 = h.wire(rB, [])
    h.wire(rB, []) // second bare wire: host has MORE than the pattern selects
    const d = h.build()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [bw1] })
    const ex = extractSubgraph(d, sel)
    // the pattern bare wire is scoped at the innermost stub (contentParent);
    // the stub layer is location-transparent, so the open reading must use
    // the same subset semantics the closed root does
    const { matches } = findOccurrences(d, ex.pattern, {
      fuel: 50,
      openBinders: new Map([[ex.binderStubs[0]!, rB]]),
    })
    expect(matches).toHaveLength(1)
  })

  it('candidates outside an open binder are skipped (atoms cannot escape their quantifier)', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, rB]])
    // restrict the search to the ROOT, which is outside rB: no matches
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders, inRegion: d.root })
    expect(matches).toHaveLength(0)
  })
})
