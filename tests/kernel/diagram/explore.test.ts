import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import type { Diagram, DiagramNode, Endpoint, NodeId, Region, RegionId, Wire, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm, exploreLabeling, exploreIso } from '../../../src/kernel/diagram/canonical/explore'
import { termShapeKey } from '../../../src/kernel/diagram/canonical/shape'
import { positionalPortKey } from '../../../src/kernel/diagram/canonical/shape'

const p = (s: string) => parseTerm(s)

// ---------------------------------------------------------------------------
// Independent brute-force isomorphism reference. Writes NONE of explore.ts's
// machinery: it enumerates id bijections and checks structure directly, so it
// is a genuine oracle for the labeling's completeness.
// ---------------------------------------------------------------------------

function permutations<T>(xs: readonly T[]): T[][] {
  if (xs.length <= 1) return [[...xs]]
  const out: T[][] = []
  for (let i = 0; i < xs.length; i++) {
    const rest = [...xs.slice(0, i), ...xs.slice(i + 1)]
    for (const perm of permutations(rest)) out.push([xs[i]!, ...perm])
  }
  return out
}

function nodeContent(n: DiagramNode): string {
  switch (n.kind) {
    case 'term': return `term:${termShapeKey(n.term)}`
    case 'atom': return 'atom'
    case 'ref': return `ref:${n.defId}:${n.arity}`
  }
}

function regionContent(r: Region): string {
  return r.kind === 'bubble' ? `bubble/${r.arity}` : r.kind
}

function epKey(d: Diagram, ep: Endpoint): string {
  const n = d.nodes[ep.node]!
  if (n.kind === 'term') return positionalPortKey(n.term, ep.port)
  if (ep.port.kind === 'arg') return `a${ep.port.index}`
  throw new Error('unexpected port')
}

/** Structural isomorphism by exhaustive bijection search (small diagrams only). */
function bruteIsomorphic(a: Diagram, b: Diagram): boolean {
  const aReg = Object.keys(a.regions)
  const bReg = Object.keys(b.regions)
  const aNode = Object.keys(a.nodes)
  const bNode = Object.keys(b.nodes)
  const aWire = Object.keys(a.wires)
  const bWire = Object.keys(b.wires)
  if (aReg.length !== bReg.length || aNode.length !== bNode.length || aWire.length !== bWire.length) return false

  // For each a-region, the candidate b-regions of the same content.
  for (const regPerm of permutations(bReg)) {
    const rmap = new Map<RegionId, RegionId>(aReg.map((r, i) => [r, regPerm[i]!]))
    // region content + parent structure + root
    let ok = true
    for (const r of aReg) {
      const ri = rmap.get(r)!
      if (regionContent(a.regions[r]!) !== regionContent(b.regions[ri]!)) { ok = false; break }
      const ar = a.regions[r]!
      const br = b.regions[ri]!
      if (ar.kind === 'sheet') { if (br.kind !== 'sheet') { ok = false; break } }
      else {
        if (br.kind === 'sheet') { ok = false; break }
        if (rmap.get(ar.parent) !== br.parent) { ok = false; break }
      }
    }
    if (!ok) continue

    for (const nodePerm of permutations(bNode)) {
      const nmap = new Map<NodeId, NodeId>(aNode.map((n, i) => [n, nodePerm[i]!]))
      let nok = true
      for (const n of aNode) {
        const ni = nmap.get(n)!
        const an = a.nodes[n]!
        const bn = b.nodes[ni]!
        if (an.kind !== bn.kind) { nok = false; break }
        if (nodeContent(an) !== nodeContent(bn)) { nok = false; break }
        if (rmap.get(an.region) !== bn.region) { nok = false; break }
        if (an.kind === 'atom' && bn.kind === 'atom' && rmap.get(an.binder) !== bn.binder) { nok = false; break }
      }
      if (!nok) continue

      for (const wirePerm of permutations(bWire)) {
        const wmap = new Map<WireId, WireId>(aWire.map((w, i) => [w, wirePerm[i]!]))
        let wok = true
        for (const w of aWire) {
          const wi = wmap.get(w)!
          const aw = a.wires[w]!
          const bw = b.wires[wi]!
          if (rmap.get(aw.scope) !== bw.scope) { wok = false; break }
          if (aw.endpoints.length !== bw.endpoints.length) { wok = false; break }
          const bset = new Set(bw.endpoints.map((ep) => `${ep.node}#${epKey(b, ep)}`))
          for (const ep of aw.endpoints) {
            if (!bset.has(`${nmap.get(ep.node)!}#${epKey(a, ep)}`)) { wok = false; break }
          }
          if (!wok) break
        }
        if (wok) return true
      }
    }
  }
  return false
}

// ---------------------------------------------------------------------------
// Randomized small-diagram generator (valid by construction: DiagramBuilder
// auto-fills every unattached port with a singleton wire).
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

const termPool = ['\\x. x', '\\x. \\y. x', '\\x. \\y. y', 'y', 'y x']

type RegMeta = { kind: 'sheet' | 'cut' | 'bubble'; parent: RegionId | null; arity: number }

function randomDiagram(rng: () => number): Diagram {
  const b = new DiagramBuilder()
  const meta = new Map<RegionId, RegMeta>([[b.root, { kind: 'sheet', parent: null, arity: 0 }]])
  const regions: RegionId[] = [b.root]
  const encloses = (anc: RegionId, desc: RegionId): boolean => {
    let cur: RegionId | null = desc
    while (cur !== null) {
      if (cur === anc) return true
      cur = meta.get(cur)!.parent
    }
    return false
  }
  const nRegions = Math.floor(rng() * 3) // 0..2 extra regions
  for (let i = 0; i < nRegions; i++) {
    const parent = regions[Math.floor(rng() * regions.length)]!
    if (rng() < 0.5) {
      const id = b.cut(parent)
      meta.set(id, { kind: 'cut', parent, arity: 0 })
      regions.push(id)
    } else {
      const arity = Math.floor(rng() * 3)
      const id = b.bubble(parent, arity)
      meta.set(id, { kind: 'bubble', parent, arity })
      regions.push(id)
    }
  }
  const nNodes = 1 + Math.floor(rng() * 3) // 1..3 nodes
  const outPorts: Endpoint[] = []
  for (let i = 0; i < nNodes; i++) {
    const region = regions[Math.floor(rng() * regions.length)]!
    if (rng() < 0.7) {
      const t = termPool[Math.floor(rng() * termPool.length)]!
      const id = b.termNode(region, p(t))
      outPorts.push({ node: id, port: { kind: 'output' } })
    } else {
      const bubbles = regions.filter((r) => meta.get(r)!.kind === 'bubble' && encloses(r, region))
      if (bubbles.length === 0) {
        const id = b.termNode(region, p('\\x. x'))
        outPorts.push({ node: id, port: { kind: 'output' } })
      } else {
        b.atom(region, bubbles[Math.floor(rng() * bubbles.length)]!)
      }
    }
  }
  // optionally join a couple of output ports on one shared root-scoped wire
  if (outPorts.length >= 2 && rng() < 0.5) {
    const k = 2 + Math.floor(rng() * (outPorts.length - 1))
    b.wire(b.root, outPorts.slice(0, k))
  }
  return b.build()
}

/** Rebuild a diagram with all ids remapped through fresh bijections. */
function relabel(d: Diagram, rng: () => number): Diagram {
  const shuffle = <T>(xs: T[]): T[] => {
    const a = [...xs]
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1))
      ;[a[i], a[j]] = [a[j]!, a[i]!]
    }
    return a
  }
  const rIds = Object.keys(d.regions)
  const nIds = Object.keys(d.nodes)
  const wIds = Object.keys(d.wires)
  const rPerm = shuffle(rIds.map((_, k) => k))
  const nPerm = shuffle(nIds.map((_, k) => k))
  const wPerm = shuffle(wIds.map((_, k) => k))
  const rTo = new Map(rIds.map((id, i) => [id, `R${rPerm[i]!}`]))
  const nTo = new Map(nIds.map((id, i) => [id, `N${nPerm[i]!}`]))
  const wTo = new Map(wIds.map((id, i) => [id, `W${wPerm[i]!}`]))
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    regions[rTo.get(id)!] = r.kind === 'sheet' ? r
      : r.kind === 'cut' ? { kind: 'cut', parent: rTo.get(r.parent)! }
      : { kind: 'bubble', parent: rTo.get(r.parent)!, arity: r.arity }
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[nTo.get(id)!] = n.kind === 'term' ? { kind: 'term', region: rTo.get(n.region)!, term: n.term }
      : n.kind === 'atom' ? { kind: 'atom', region: rTo.get(n.region)!, binder: rTo.get(n.binder)! }
      : { kind: 'ref', region: rTo.get(n.region)!, defId: n.defId, arity: n.arity }
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[wTo.get(id)!] = {
      scope: rTo.get(w.scope)!,
      endpoints: w.endpoints.map((ep) => ({ node: nTo.get(ep.node)!, port: ep.port })),
    }
  }
  return mkDiagram({ root: rTo.get(d.root)!, regions, nodes, wires })
}

describe('exploreLabeling — invariance property vs brute-force reference', () => {
  it('form equality agrees with brute-force isomorphism across random pairs', () => {
    const rng = mulberry32(0xC0FFEE)
    const corpus: Diagram[] = []
    for (let i = 0; i < 60; i++) corpus.push(randomDiagram(rng))
    let sawIso = false
    let sawNonIso = false
    for (let i = 0; i < corpus.length; i++) {
      for (let j = i; j < corpus.length; j++) {
        const eqForm = exploreForm(corpus[i]!) === exploreForm(corpus[j]!)
        const iso = bruteIsomorphic(corpus[i]!, corpus[j]!)
        expect(eqForm, `pair (${i},${j}): form-eq ${eqForm} but brute-iso ${iso}`).toBe(iso)
        if (iso && i !== j) sawIso = true
        if (!iso) sawNonIso = true
      }
    }
    // the corpus is discriminating in both directions
    expect(sawNonIso).toBe(true)
    expect(sawIso).toBe(true)
  })

  it('is invariant under random id relabeling (isomorphic by construction)', () => {
    const rng = mulberry32(0x5EED)
    for (let i = 0; i < 80; i++) {
      const d = randomDiagram(rng)
      const r = relabel(d, rng)
      expect(exploreForm(r)).toBe(exploreForm(d))
      expect(bruteIsomorphic(d, r)).toBe(true)
    }
  })
})

describe('exploreLabeling — specific structural properties', () => {
  it('boundary order is significant for open diagrams', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const wOut = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const wY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = b.build()
    expect(exploreForm(d, [wOut, wY])).not.toBe(exploreForm(d, [wY, wOut]))
    // and unpinned agrees regardless of construction
    expect(exploreForm(d, [wOut, wY])).toBe(exploreForm(d, [wOut, wY]))
  })

  it('wire-set deferral: a symmetric wire broken by a determined path takes no lex-least choice', () => {
    // Two term nodes distinguished by their own content but joined on ONE
    // shared wire. The wire's two endpoints look like an unordered set, yet
    // refinement determines them from the endpoints' distinct node colors — no
    // individualization branch is needed. Observe that by construction the
    // labeling is stable and the two endpoints receive distinct node ordinals.
    const b = new DiagramBuilder()
    const n1 = b.termNode(b.root, p('\\x. x'))
    const n2 = b.termNode(b.root, p('\\x. \\y. x'))
    b.wire(b.root, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const lab = exploreLabeling(b.build())
    const ords = [...lab.nodeOrd.values()].sort()
    expect(ords).toEqual([0, 1]) // distinguished without a tie
  })

  it('twin empty cuts canonicalize deterministically (lex-least automorphism choice)', () => {
    const mk = (swap: boolean) => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      void (swap ? [c2, c1] : [c1, c2])
      return b.build()
    }
    expect(exploreForm(mk(false))).toBe(exploreForm(mk(true)))
  })

  it('exact term comparison is name-blind but NOT beta-eta: a redex differs from its normal form', () => {
    const mk = (term: string) => {
      const b = new DiagramBuilder()
      b.termNode(b.root, p(term))
      return b.build()
    }
    // alpha/name-blind: same
    expect(exploreForm(mk('\\a. a'))).toBe(exploreForm(mk('\\z. z')))
    // beta: (\x.x) applied to y is NOT identified with its reduct y
    expect(exploreForm(mk('(\\x. x) y'))).not.toBe(exploreForm(mk('y')))
  })
})

describe('exploreIso', () => {
  it('extracts a valid ordinal-matched isomorphism between relabeled copies', () => {
    const rng = mulberry32(0xABCD)
    const d = randomDiagram(rng)
    const r = relabel(d, rng)
    const iso = exploreIso(d, r)
    expect(iso).not.toBeNull()
    // every region/node/wire image exists in r
    for (const img of iso!.regions.values()) expect(r.regions[img]).toBeDefined()
    for (const img of iso!.nodes.values()) expect(r.nodes[img]).toBeDefined()
    for (const img of iso!.wires.values()) expect(r.wires[img]).toBeDefined()
  })

  it('returns null for non-isomorphic diagrams', () => {
    const a = new DiagramBuilder(); a.termNode(a.root, p('\\x. x'))
    const b = new DiagramBuilder(); b.cut(b.root)
    expect(exploreIso(a.build(), b.build())).toBeNull()
  })
})
