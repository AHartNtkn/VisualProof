import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import type {
  Diagram, DiagramNode, DiagramNodeInput, Endpoint, NodeId, Region, RegionId, Wire, WireId,
} from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { RelSig } from '../../../src/kernel/diagram/sig'
import { TERM, relSig, sigEquals, sigKey } from '../../../src/kernel/diagram/sig'
import { exploreForm, exploreLabeling, exploreIso, boundaryForm } from '../../../src/kernel/diagram/canonical/explore'
import { termShapeKey, positionalPortKey } from '../../../src/kernel/diagram/canonical/shape'

const p = (s: string) => parseTerm(s)

// ---------------------------------------------------------------------------
// Independent brute-force isomorphism reference for the SIGNATURE-INDEXED model.
// It writes NONE of explore.ts's individualization/refinement machinery: it
// enumerates id bijections and checks structure directly. Leaf payloads are
// compared by the shared canonical helpers (term shape via `termShapeKey`; a
// body's content sub-diagram by its boundary-anchored fingerprint `boundaryForm`)
// exactly as an isomorphism would identify them — the top-level region/node/wire
// correspondence is what the brute force independently searches.
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

/** Region-, name-, and id-independent intrinsic content of a node. */
function nodeContent(n: DiagramNode): string {
  switch (n.kind) {
    case 'term': return `term:${termShapeKey(n.term, n.freePorts)}`
    case 'atom': return `atom:${sigKey(n.sig)}`
    case 'ref': return `ref:${n.defId}:${sigKey(n.sig)}`
    case 'body': return `body:${sigKey(n.sig)}:${boundaryForm(n.content)}`
  }
}

/** Region kind — `sheet` | `cut` (no bubbles in the sig-indexed model). */
function regionContent(r: Region): string {
  return r.kind
}

/** Positional (name-blind) key of an endpoint's port, per node kind. */
function epKey(d: Diagram, ep: Endpoint): string {
  const n = d.nodes[ep.node]!
  switch (n.kind) {
    case 'term':
      return positionalPortKey(n.term, ep.port, n.freePorts)
    case 'atom':
      if (ep.port.kind === 'head') return 'hd'
      if (ep.port.kind === 'arg') return `a${ep.port.index}`
      throw new Error(`atom endpoint has unexpected port '${ep.port.kind}'`)
    case 'ref':
      if (ep.port.kind === 'arg') return `a${ep.port.index}`
      throw new Error(`ref endpoint has unexpected port '${ep.port.kind}'`)
    case 'body':
      if (ep.port.kind === 'output') return 'out'
      if (ep.port.kind === 'freeVar') return ep.port.name
      throw new Error(`body endpoint has unexpected port '${ep.port.kind}'`)
  }
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

  for (const regPerm of permutations(bReg)) {
    const rmap = new Map<RegionId, RegionId>(aReg.map((r, i) => [r, regPerm[i]!]))
    // region content + parent structure
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
        if (nodeContent(an) !== nodeContent(bn)) { nok = false; break } // carries sigKey for atom/ref/body
        if (rmap.get(an.region) !== bn.region) { nok = false; break }
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
          if (!sigEquals(aw.sig, bw.sig)) { wok = false; break } // wire sort is intrinsic content
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
// auto-fills every unattached port with a singleton wire of the right sort —
// atom heads and args, ref args, term output/freeVars). Signature arities are
// capped at 1 to keep the brute-force reference tractable.
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
const sigPool: RelSig[] = [relSig([]), relSig([TERM])]
const defIdPool = ['Nat', 'Fin']

function randomDiagram(rng: () => number): Diagram {
  const b = new DiagramBuilder()
  const regions: RegionId[] = [b.root]
  const nRegions = Math.floor(rng() * 3) // 0..2 extra cuts
  for (let i = 0; i < nRegions; i++) {
    const parent = regions[Math.floor(rng() * regions.length)]!
    regions.push(b.cut(parent))
  }
  const nNodes = 1 + Math.floor(rng() * 3) // 1..3 nodes
  const outPorts: Endpoint[] = []
  for (let i = 0; i < nNodes; i++) {
    const region = regions[Math.floor(rng() * regions.length)]!
    const roll = rng()
    if (roll < 0.55) {
      const t = termPool[Math.floor(rng() * termPool.length)]!
      const id = b.termNode(region, p(t))
      outPorts.push({ node: id, port: { kind: 'output' } })
    } else if (roll < 0.8) {
      b.atom(region, sigPool[Math.floor(rng() * sigPool.length)]!)
    } else {
      b.ref(region, defIdPool[Math.floor(rng() * defIdPool.length)]!, sigPool[Math.floor(rng() * sigPool.length)]!)
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
    regions[rTo.get(id)!] = r.kind === 'sheet' ? r : { kind: 'cut', parent: rTo.get(r.parent)! }
  }
  const nodes: Record<NodeId, DiagramNodeInput> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[nTo.get(id)!] = n.kind === 'term'
      ? { kind: 'term', region: rTo.get(n.region)!, term: n.term, freePorts: n.freePorts }
      : n.kind === 'atom' ? { kind: 'atom', region: rTo.get(n.region)!, sig: n.sig }
      : n.kind === 'ref' ? { kind: 'ref', region: rTo.get(n.region)!, defId: n.defId, sig: n.sig }
      : { kind: 'body', region: rTo.get(n.region)!, sig: n.sig, content: n.content }
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[wTo.get(id)!] = {
      scope: rTo.get(w.scope)!,
      sig: w.sig,
      endpoints: w.endpoints.map((ep) => ({ node: nTo.get(ep.node)!, port: ep.port })),
    }
  }
  return mkDiagram({ root: rTo.get(d.root)!, regions, nodes, wires })
}

// ---------------------------------------------------------------------------
// Curated family exercising the sig-indexed distinctions the random generator
// under-samples: same-scope relational wire pairs (order permuted), atoms that
// differ only in sig, body nodes with equal-vs-differing content, and head-port
// wiring (a symmetric swap between two same-sig wires + shared-vs-separate heads).
// ---------------------------------------------------------------------------

/** Two same-scope relational (atom-head) wires inserted in either order. */
function relWirePair(swap: boolean): Diagram {
  const sigA = relSig([TERM]) // nA: head + a0
  const sigB = relSig([]) // nB: head only
  const nodes: Record<NodeId, DiagramNodeInput> = {
    nA: { kind: 'atom', region: 'r0', sig: sigA },
    nB: { kind: 'atom', region: 'r0', sig: sigB },
  }
  const hA: Wire = { scope: 'r0', sig: sigA, endpoints: [{ node: 'nA', port: { kind: 'head' } }] }
  const hB: Wire = { scope: 'r0', sig: sigB, endpoints: [{ node: 'nB', port: { kind: 'head' } }] }
  const aA0: Wire = { scope: 'r0', sig: TERM, endpoints: [{ node: 'nA', port: { kind: 'arg', index: 0 } }] }
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    nodes,
    wires: swap ? { hB, hA, aA0 } : { hA, hB, aA0 },
  })
}

/** One atom whose sig differs only in the SORT of its single argument. */
function atomOfArgSort(relArg: boolean): Diagram {
  const b = new DiagramBuilder()
  b.atom(b.root, relArg ? relSig([relSig([])]) : relSig([TERM]))
  return b.build()
}

/** One body node whose payload is the given closed content term. */
function bodyOfContent(contentTerm: string): Diagram {
  const cb = new DiagramBuilder()
  cb.termNode(cb.root, p(contentTerm))
  const content = mkDiagramWithBoundary(cb.build(), [])
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    nodes: { nb: { kind: 'body', region: 'r0', sig: relSig([]), content } },
    wires: { wo: { scope: 'r0', sig: relSig([]), endpoints: [{ node: 'nb', port: { kind: 'output' } }] } },
  })
}

/** Two arity-0 atom heads, each on its own same-sig wire; heads swapped or not. */
function headSwap(swap: boolean): Diagram {
  const sig = relSig([])
  const nodes: Record<NodeId, DiagramNodeInput> = {
    nA: { kind: 'atom', region: 'r0', sig },
    nB: { kind: 'atom', region: 'r0', sig },
  }
  const wires: Record<WireId, Wire> = {
    wP: { scope: 'r0', sig, endpoints: [{ node: swap ? 'nB' : 'nA', port: { kind: 'head' } }] },
    wQ: { scope: 'r0', sig, endpoints: [{ node: swap ? 'nA' : 'nB', port: { kind: 'head' } }] },
  }
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires })
}

/** Two arity-0 atoms: heads sharing ONE relation wire, vs on two separate ones. */
function headSharing(shared: boolean): Diagram {
  const sig = relSig([])
  const nodes: Record<NodeId, DiagramNodeInput> = {
    nA: { kind: 'atom', region: 'r0', sig },
    nB: { kind: 'atom', region: 'r0', sig },
  }
  const wires: Record<WireId, Wire> = shared
    ? {
        w: {
          scope: 'r0', sig,
          endpoints: [{ node: 'nA', port: { kind: 'head' } }, { node: 'nB', port: { kind: 'head' } }],
        },
      }
    : {
        wA: { scope: 'r0', sig, endpoints: [{ node: 'nA', port: { kind: 'head' } }] },
        wB: { scope: 'r0', sig, endpoints: [{ node: 'nB', port: { kind: 'head' } }] },
      }
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires })
}

function curatedCorpus(): Diagram[] {
  return [
    relWirePair(false), relWirePair(true), // isomorphic (wire insertion order permuted)
    atomOfArgSort(false), atomOfArgSort(true), // NON-iso: differ only in arg sort
    bodyOfContent('y'), bodyOfContent('z'), // iso: content equal up to free-port name
    bodyOfContent('\\x. x'), // NON-iso vs the above: different content shape
    headSwap(false), headSwap(true), // iso: symmetric head-port swap
    headSharing(true), headSharing(false), // NON-iso: shared vs separate head relations
  ]
}

describe('exploreLabeling — invariance property vs brute-force reference', () => {
  it('form equality agrees with brute-force isomorphism across random + curated pairs', () => {
    const rng = mulberry32(0xC0FFEE)
    const corpus: Diagram[] = curatedCorpus()
    for (let i = 0; i < 40; i++) corpus.push(randomDiagram(rng))
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

  it('the curated cases realize the intended iso / non-iso outcomes', () => {
    // same-scope relational wire pair: order-independent
    expect(exploreForm(relWirePair(false))).toBe(exploreForm(relWirePair(true)))
    expect(bruteIsomorphic(relWirePair(false), relWirePair(true))).toBe(true)
    // atoms differing only in the SORT of one argument: distinguished
    expect(exploreForm(atomOfArgSort(false))).not.toBe(exploreForm(atomOfArgSort(true)))
    expect(bruteIsomorphic(atomOfArgSort(false), atomOfArgSort(true))).toBe(false)
    // body content: equal up to name → same; different shape → different
    expect(exploreForm(bodyOfContent('y'))).toBe(exploreForm(bodyOfContent('z')))
    expect(bruteIsomorphic(bodyOfContent('y'), bodyOfContent('z'))).toBe(true)
    expect(exploreForm(bodyOfContent('y'))).not.toBe(exploreForm(bodyOfContent('\\x. x')))
    expect(bruteIsomorphic(bodyOfContent('y'), bodyOfContent('\\x. x'))).toBe(false)
    // head-port swap between two same-sig wires: an automorphism
    expect(exploreForm(headSwap(false))).toBe(exploreForm(headSwap(true)))
    expect(bruteIsomorphic(headSwap(false), headSwap(true))).toBe(true)
    // head incidence is significant: shared relation ≠ two separate relations
    expect(exploreForm(headSharing(true))).not.toBe(exploreForm(headSharing(false)))
    expect(bruteIsomorphic(headSharing(true), headSharing(false))).toBe(false)
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
