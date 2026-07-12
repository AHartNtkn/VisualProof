import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences, __benchCounter } from '../../../src/kernel/diagram/subgraph/match'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import { termShapeKey, positionalPortKey } from '../../../src/kernel/diagram/canonical/shape'

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

describe('exploration matcher — explicit exploration fuel', () => {
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

  it('returns explicit exhaustion before exact backtracking completes', () => {
    const result = findOccurrences(identityNodes(4), identityPattern(2), {
      fuel: 50,
      explorationFuel: 1,
      mode: 'exact',
      inRegion: 'r0',
    })

    expect(result.status).toBe('exhausted')
    expect(result.matches.length).toBeLessThan(choose(4, 2))
    expect(result.undecided).toEqual([])
    expect(result.explorationSteps).toBe(1)
  })

  it('returns every exact match when exploration fuel is sufficient', () => {
    const result = findOccurrences(identityNodes(4), identityPattern(2), {
      fuel: 1,
      explorationFuel: 100,
      mode: 'exact',
      inRegion: 'r0',
    })

    expect(result.status).toBe('complete')
    expect(result.matches).toHaveLength(choose(4, 2))
    expect(result.undecided).toEqual([])
    expect(result.explorationSteps).toBeGreaterThan(1)
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

// ---------------------------------------------------------------------------
// STANDING brute-force footprint-equality oracle (team-lead ruling): an
// independent full-enumeration reference matcher — every injective region/node
// assignment, verified directly, footprints collected. It shares NONE of the
// matcher's search strategy, so agreement is a genuine completeness check on
// the symmetry break + per-subset fallback. Scoped to CLOSED patterns (empty
// boundary), term nodes + cut regions, matched at the root — enough to exercise
// symmetric node/region runs, which is exactly where the break could drop
// occurrences. It is a regression guard, not a gate.
// ---------------------------------------------------------------------------

function mulberry32(seed: number): () => number {
  let a = seed >>> 0
  return () => {
    a |= 0; a = (a + 0x6d2b79f5) | 0
    let t = Math.imul(a ^ (a >>> 15), 1 | a)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const closedTermPool = ['\\x. x', '\\x. \\y. x', '\\x. \\y. y']

/** Random closed diagram: term nodes (small pool) across the root and up to two cuts, some shared output wires. */
function randomClosed(rng: () => number): Diagram {
  const b = new DiagramBuilder()
  const regions: RegionId[] = [b.root]
  const nCuts = Math.floor(rng() * 3) // 0..2
  for (let i = 0; i < nCuts; i++) regions.push(b.cut(regions[Math.floor(rng() * regions.length)]!))
  const outs: Endpoint[] = []
  const nNodes = 1 + Math.floor(rng() * 3) // 1..3
  for (let i = 0; i < nNodes; i++) {
    const region = regions[Math.floor(rng() * regions.length)]!
    const n = b.termNode(region, p(closedTermPool[Math.floor(rng() * closedTermPool.length)]!))
    outs.push({ node: n, port: { kind: 'output' } })
  }
  if (outs.length >= 2 && rng() < 0.5) {
    const k = 2 + Math.floor(rng() * (outs.length - 1))
    b.wire(b.root, outs.slice(0, k)) // one shared root-scoped wire
  }
  return b.build()
}

function epKey(d: Diagram, ep: Endpoint): string {
  const n = d.nodes[ep.node]!
  if (n.kind === 'term') return positionalPortKey(n.term, ep.port)
  if (ep.port.kind === 'arg') return `a${ep.port.index}`
  throw new Error('unexpected port')
}

function nodeContent(d: Diagram, id: NodeId): string {
  const n = d.nodes[id]!
  return n.kind === 'term' ? `t:${termShapeKey(n.term)}` : n.kind === 'ref' ? `r:${n.defId}:${n.arity}` : 'atom'
}
function regionContent(d: Diagram, id: RegionId): string {
  const r = d.regions[id]!
  return r.kind === 'bubble' ? `b/${r.arity}` : r.kind
}

/** All injective maps sources→targets respecting `ok(s,t)`, as an array of Maps. */
function injections<S extends string, T extends string>(
  sources: readonly S[], targets: readonly T[], ok: (s: S, t: T, m: Map<S, T>) => boolean,
): Map<S, T>[] {
  const out: Map<S, T>[] = []
  const used = new Set<T>()
  const cur = new Map<S, T>()
  const rec = (i: number): void => {
    if (i === sources.length) { out.push(new Map(cur)); return }
    const s = sources[i]!
    for (const t of targets) {
      if (used.has(t) || !ok(s, t, cur)) continue
      used.add(t); cur.set(s, t)
      rec(i + 1)
      used.delete(t); cur.delete(s)
    }
  }
  rec(0)
  return out
}

/** Footprint set of all occurrences of a closed pattern at host region R, by full enumeration. */
function bruteFootprints(host: Diagram, pd: Diagram, R: RegionId): Set<string> {
  const results = new Set<string>()
  const pRegionsNonRoot = Object.keys(pd.regions).filter((r) => r !== pd.root)
  const hRegionsNonRoot = Object.keys(host.regions).filter((r) => r !== host.root)
  const pNodes = Object.keys(pd.nodes)
  const hNodes = Object.keys(host.nodes)
  const childrenOf = (d: Diagram, id: RegionId) =>
    Object.keys(d.regions).filter((r) => { const x = d.regions[r]!; return x.kind !== 'sheet' && x.parent === id })
  const nodesIn = (d: Diagram, id: RegionId) => Object.keys(d.nodes).filter((n) => d.nodes[n]!.region === id)
  const endpointfulScoped = (d: Diagram, id: RegionId) =>
    Object.keys(d.wires).filter((w) => d.wires[w]!.scope === id && d.wires[w]!.endpoints.length > 0).length

  const regionMaps = injections(pRegionsNonRoot, hRegionsNonRoot, (pr, hr) => regionContent(pd, pr) === regionContent(host, hr))
  for (const rm0 of regionMaps) {
    const rm = new Map(rm0); rm.set(pd.root, R)
    const img = (pr: RegionId) => rm.get(pr)!
    // parent structure + exact-below (non-root) / subset (root)
    let ok = true
    for (const pr of Object.keys(pd.regions)) {
      const hr = img(pr)
      const pr0 = pd.regions[pr]!
      if (pr0.kind !== 'sheet') {
        const hrReg = host.regions[hr]!
        if (hrReg.kind === 'sheet') { ok = false; break }
        if (img(pr0.parent) !== hrReg.parent) { ok = false; break }
      }
      if (pr !== pd.root) {
        if (childrenOf(host, hr).length !== childrenOf(pd, pr).length) { ok = false; break }
        if (nodesIn(host, hr).length !== nodesIn(pd, pr).length) { ok = false; break }
        if (endpointfulScoped(host, hr) !== endpointfulScoped(pd, pr)) { ok = false; break }
      }
    }
    if (!ok) continue
    const nodeMaps = injections(pNodes, hNodes, (pn, hn, m) => {
      if (nodeContent(pd, pn) !== nodeContent(host, hn)) return false
      if (img(pd.nodes[pn]!.region) !== host.nodes[hn]!.region) return false
      void m
      return true
    })
    for (const nm of nodeMaps) {
      // verify wires
      const wireMap = new Map<WireId, WireId>()
      const usedWires = new Set<WireId>()
      let wok = true
      for (const [pw, w] of Object.entries(pd.wires)) {
        if (w.endpoints.length === 0) continue
        const imgs = w.endpoints.map((ep) => `${nm.get(ep.node)!} ${epKey(pd, ep)}`).sort()
        const scope = img(w.scope)
        let found: WireId | undefined
        for (const [hw, hwire] of Object.entries(host.wires)) {
          if (usedWires.has(hw) || hwire.scope !== scope) continue
          if (hwire.endpoints.length !== w.endpoints.length) continue
          const hs = hwire.endpoints.map((ep) => `${ep.node} ${epKey(host, ep)}`).sort()
          if (hs.length === imgs.length && hs.every((v, i) => v === imgs[i])) { found = hw; break }
        }
        if (found === undefined) { wok = false; break }
        usedWires.add(found); wireMap.set(pw, found)
      }
      if (!wok) continue
      const fp = JSON.stringify([
        [...rm.values()].sort(),
        [...nm.values()].sort(),
        [...wireMap.values()].sort(),
        [],
      ])
      results.add(fp)
    }
  }
  return results
}

function matcherFootprints(host: Diagram, pd: Diagram, R: RegionId): Set<string> {
  const r = findOccurrences(host, _dwbEmpty(pd), { fuel: 100, mode: 'exact', inRegion: R })
  const out = new Set<string>()
  for (const m of r.matches) {
    out.add(JSON.stringify([
      [...m.regionMap.values()].sort(),
      [...m.nodeMap.values()].sort(),
      [...m.wireMap.values()].sort(),
      [...m.attachments],
    ]))
  }
  return out
}
function _dwbEmpty(d: Diagram) {
  return { diagram: d, boundary: [] as readonly WireId[] }
}

describe('exploration matcher — brute-force footprint-equality oracle (standing regression guard)', () => {
  it('matches an independent full-enumeration reference across random closed diagrams', () => {
    const rng = mulberry32(0x1234ABCD)
    let sawMatch = false
    let sawEmpty = false
    let sawMulti = false
    for (let i = 0; i < 200; i++) {
      const host = randomClosed(rng)
      const pattern = randomClosed(rng)
      const brute = bruteFootprints(host, pattern, host.root)
      const mine = matcherFootprints(host, pattern, host.root)
      expect([...mine].sort(), `case ${i}: matcher vs brute-force footprints differ`).toEqual([...brute].sort())
      if (mine.size > 0) sawMatch = true
      if (mine.size === 0) sawEmpty = true
      if (mine.size > 1) sawMulti = true
    }
    // the corpus exercises matches, non-matches, and multi-occurrence cases
    expect(sawMatch && sawEmpty && sawMulti).toBe(true)
  })
})
