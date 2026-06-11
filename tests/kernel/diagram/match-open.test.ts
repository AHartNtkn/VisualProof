import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

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
