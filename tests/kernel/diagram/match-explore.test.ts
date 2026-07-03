import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences, __benchCounter } from '../../../src/kernel/diagram/subgraph/match'
import type { Endpoint } from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)

function choose(m: number, k: number): number {
  let r = 1
  for (let i = 0; i < k; i++) r = (r * (m - i)) / (i + 1)
  return Math.round(r)
}

describe('exploration matcher — benchmark (visited-state growth)', () => {
  // N identical `\x. x` nodes whose outputs all lie on ONE N-endpoint equality
  // wire; pattern identical (empty boundary). Exactly one occurrence (the whole
  // thing); the N! interchangeable bijections collapse to it. The old
  // backtracking matcher visited 325 / 9.86M / (infeasible) at N=5/10/20; the
  // exploration matcher is linear.
  function shared(N: number) {
    const b = new DiagramBuilder()
    const eps: Endpoint[] = []
    for (let i = 0; i < N; i++) {
      const n = b.termNode(b.root, p('\\x. x'))
      eps.push({ node: n, port: { kind: 'output' } })
    }
    b.wire(b.root, eps)
    return b.build()
  }
  function sharedPattern(N: number) {
    const b = new DiagramBuilder()
    const eps: Endpoint[] = []
    for (let i = 0; i < N; i++) {
      const n = b.termNode(b.root, p('\\x. x'))
      eps.push({ node: n, port: { kind: 'output' } })
    }
    b.wire(b.root, eps)
    return mkDiagramWithBoundary(b.build(), [])
  }

  it('visits O(N) states — pinned at N = 5, 10, 20 (old matcher was factorial)', () => {
    const expected: Record<number, number> = { 5: 5, 10: 10, 20: 20 }
    for (const N of [5, 10, 20]) {
      __benchCounter.n = 0
      const r = findOccurrences(shared(N), sharedPattern(N), { fuel: 100 })
      expect(r.matches, `N=${N} occurrence count`).toHaveLength(1)
      expect(__benchCounter.n, `N=${N} visited states`).toBe(expected[N])
    }
  })
})

describe('exploration matcher — symmetry collapse is COMPLETE (not over-pruned)', () => {
  // k independent identical pattern nodes into M independent identical host
  // nodes: every k-subset is a distinct occurrence, so exactly C(M,k) matches.
  // Under-reporting here would mean the increasing-order break lost occurrences;
  // over-reporting would mean footprint dedup failed.
  function identityNodes(count: number) {
    const b = new DiagramBuilder()
    for (let i = 0; i < count; i++) b.termNode(b.root, p('\\x. x'))
    return b.build()
  }
  function identityPattern(count: number) {
    const b = new DiagramBuilder()
    for (let i = 0; i < count; i++) b.termNode(b.root, p('\\x. x'))
    return mkDiagramWithBoundary(b.build(), [])
  }

  for (const [k, M] of [[1, 3], [2, 4], [3, 5], [3, 3], [2, 5], [4, 6]] as const) {
    it(`k=${k} identical pattern nodes into M=${M} identical host nodes → C(${M},${k})=${choose(M, k)} occurrences`, () => {
      const r = findOccurrences(identityNodes(M), identityPattern(k), { fuel: 50, inRegion: 'r0' })
      expect(r.matches).toHaveLength(choose(M, k))
    })
  }

  it('symmetric child regions collapse but distinct ones do not (twin identical cuts)', () => {
    // pattern: two identical cuts each holding `\x. x`
    const pb = new DiagramBuilder()
    for (let i = 0; i < 2; i++) { const c = pb.cut(pb.root); pb.termNode(c, p('\\x. x')) }
    const pattern = mkDiagramWithBoundary(pb.build(), [])
    // host: three identical such cuts → C(3,2)=3 distinct pairs
    const hb = new DiagramBuilder()
    for (let i = 0; i < 3; i++) { const c = hb.cut(hb.root); hb.termNode(c, p('\\x. x')) }
    const r = findOccurrences(hb.build(), pattern, { fuel: 50, inRegion: 'r0' })
    expect(r.matches).toHaveLength(choose(3, 2))
  })

  it('distinct wirings to a hub are NOT collapsed (both occurrences found)', () => {
    // pattern: one `y` node with its v:y as boundary
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y'))
    const stub = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(pb.build(), [stub])
    // host: two `y` nodes on distinct wires to distinct hubs → two occurrences
    const hb = new DiagramBuilder()
    const a = hb.termNode(hb.root, p('y'))
    const c = hb.termNode(hb.root, p('y'))
    const h1 = hb.termNode(hb.root, p('\\x. x'))
    const h2 = hb.termNode(hb.root, p('\\x. \\y. x'))
    const w1 = hb.wire(hb.root, [{ node: a, port: { kind: 'freeVar', name: 'y' } }, { node: h1, port: { kind: 'output' } }])
    const w2 = hb.wire(hb.root, [{ node: c, port: { kind: 'freeVar', name: 'y' } }, { node: h2, port: { kind: 'output' } }])
    const r = findOccurrences(hb.build(), pattern, { fuel: 50, inRegion: 'r0' })
    expect(r.matches).toHaveLength(2)
    expect(new Set(r.matches.map((m) => m.attachments[0]))).toEqual(new Set([w1, w2]))
  })
})

describe('exploration matcher — attachment seed', () => {
  it('seeded results equal unseeded results filtered by attachment', () => {
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y'))
    const stub = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(pb.build(), [stub])
    const hb = new DiagramBuilder()
    const a = hb.termNode(hb.root, p('y'))
    const c = hb.termNode(hb.root, p('y'))
    const h1 = hb.termNode(hb.root, p('\\x. x'))
    const h2 = hb.termNode(hb.root, p('\\x. \\y. x'))
    const w1 = hb.wire(hb.root, [{ node: a, port: { kind: 'freeVar', name: 'y' } }, { node: h1, port: { kind: 'output' } }])
    hb.wire(hb.root, [{ node: c, port: { kind: 'freeVar', name: 'y' } }, { node: h2, port: { kind: 'output' } }])
    const host = hb.build()
    const unseeded = findOccurrences(host, pattern, { fuel: 50, inRegion: 'r0' })
    const seeded = findOccurrences(host, pattern, { fuel: 50, inRegion: 'r0', attachments: [w1] })
    const filtered = unseeded.matches.filter((m) => m.attachments.length === 1 && m.attachments[0] === w1)
    expect(seeded.matches.map((m) => m.attachments)).toEqual(filtered.map((m) => m.attachments))
    expect(seeded.matches).toHaveLength(1)
    expect(seeded.matches[0]!.attachments).toEqual([w1])
  })
})

describe('exploration matcher — exact vs betaEta mode', () => {
  it('a redex host node matches in betaEta but NOT in exact', () => {
    // pattern node `y`; host node `(\x. x) y` (beta-equal but not structurally equal)
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y'))
    const stub = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(pb.build(), [stub])
    const hb = new DiagramBuilder()
    const target = hb.termNode(hb.root, p('(\\x. x) y'))
    const other = hb.termNode(hb.root, p('\\x. x'))
    hb.wire(hb.root, [
      { node: target, port: { kind: 'freeVar', name: 'y' } },
      { node: other, port: { kind: 'output' } },
    ])
    const host = hb.build()
    expect(findOccurrences(host, pattern, { fuel: 100, mode: 'betaEta' }).matches).toHaveLength(1)
    expect(findOccurrences(host, pattern, { fuel: 100, mode: 'exact' }).matches).toHaveLength(0)
  })

  it('exact mode is name-blind and produces no undecided even on non-normalizing terms', () => {
    const omega = '(\\x. x x) (\\x. x x)'
    const pb = new DiagramBuilder()
    pb.termNode(pb.root, p(omega))
    const pattern = mkDiagramWithBoundary(pb.build(), [])
    const hb = new DiagramBuilder()
    hb.termNode(hb.root, p(omega))
    const r = findOccurrences(hb.build(), pattern, { fuel: 5, mode: 'exact', inRegion: 'r0' })
    expect(r.undecided).toHaveLength(0)
    expect(r.matches).toHaveLength(1)
  })
})
