import type { NodeArc, NodeGeometry, NodeRadial } from './bend'
import { polar, type Vec2 } from './vec'

// ---- CONTINUOUS SHAPE MORPHING between two bent-grid anatomies.
// Port rails pair BY PORT NAME — the anchor is by construction the rail's
// outer endpoint (bend.ts: portAnchors[name] = polar(angle, r1)), so deriving
// each frame's anchors from the interpolated rails keeps every wire endpoint
// ON the drawn rail tip with zero error. Remaining radials and arcs pair
// greedily by geometric proximity (same kind preferred); the unpaired
// collapse to / grow from zero extent in place. Every frame draws ONE
// interpolated geometry — no crossfade, no swap.
const wrapPi = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))
const lerpN = (a: number, b: number, p: number): number => a + (b - a) * p
const lerpA = (a: number, b: number, p: number): number => a + wrapPi(b - a) * p

function greedyPairs<T>(as: readonly T[], bs: readonly T[], cost: (a: T, b: T) => number): { pairs: [T, T][]; loneA: T[]; loneB: T[] } {
  const cand: { i: number; j: number; c: number }[] = []
  as.forEach((a, i) => bs.forEach((b, j) => cand.push({ i, j, c: cost(a, b) })))
  cand.sort((x, y) => x.c - y.c)
  const usedA = new Set<number>(), usedB = new Set<number>()
  const pairs: [T, T][] = []
  for (const { i, j } of cand) {
    if (usedA.has(i) || usedB.has(j)) continue
    usedA.add(i)
    usedB.add(j)
    pairs.push([as[i]!, bs[j]!])
  }
  return { pairs, loneA: as.filter((_, i) => !usedA.has(i)), loneB: bs.filter((_, j) => !usedB.has(j)) }
}

export function mkGeomMorph(from: NodeGeometry, to: NodeGeometry): (p: number) => NodeGeometry {
  const railFor = (g: NodeGeometry, name: string): NodeRadial => {
    const a = g.portAnchors[name]!
    let best: NodeRadial | null = null
    let bd = Infinity
    for (const r of g.radials) {
      if (r.kind !== 'port') continue
      const tip = polar(r.angle, r.r1)
      const d = Math.hypot(tip.x - a.x, tip.y - a.y)
      if (d < bd) { bd = d; best = r }
    }
    if (best === null) throw new Error(`morph: no port rail for '${name}'`)
    return best
  }
  const names = [...new Set([...Object.keys(from.portAnchors), ...Object.keys(to.portAnchors)])]
  const ports = names.map((name) => ({
    name,
    from: name in from.portAnchors ? railFor(from, name) : null,
    to: name in to.portAnchors ? railFor(to, name) : null,
  }))
  const portRails = new Set<NodeRadial>()
  for (const pr of ports) {
    if (pr.from !== null) portRails.add(pr.from)
    if (pr.to !== null) portRails.add(pr.to)
  }
  const rcost = (a: NodeRadial, b: NodeRadial): number => {
    const ma = polar(a.angle, (a.r0 + a.r1) / 2), mb = polar(b.angle, (b.r0 + b.r1) / 2)
    return Math.hypot(ma.x - mb.x, ma.y - mb.y) + Math.abs((a.r1 - a.r0) - (b.r1 - b.r0)) * 0.5 + (a.kind === b.kind ? 0 : 3)
  }
  const rads = greedyPairs(from.radials.filter((r) => !portRails.has(r)), to.radials.filter((r) => !portRails.has(r)), rcost)
  const acost = (a: NodeArc, b: NodeArc): number => {
    const meanR = (a.r + b.r) / 2
    return Math.abs(a.r - b.r) + Math.abs(wrapPi((a.a0 + a.a1) / 2 - (b.a0 + b.a1) / 2)) * meanR
      + Math.abs((a.a1 - a.a0) - (b.a1 - b.a0)) * meanR * 0.5 + (a.kind === b.kind ? 0 : 2)
  }
  const arcs = greedyPairs(from.arcs, to.arcs, acost)

  return (p: number): NodeGeometry => {
    const outRadials: NodeRadial[] = []
    const portAnchors: Record<string, Vec2> = {}
    for (const pr of ports) {
      // paired rails lerp in polar; a dying port's rail retracts to its row
      // (the wire endpoint rides it inward); a born port's rail grows out
      const f = pr.from ?? { ...pr.to!, r1: pr.to!.r0 }
      const t = pr.to ?? { ...pr.from!, r1: pr.from!.r0 }
      const angle = lerpA(f.angle, t.angle, p)
      const r0 = lerpN(f.r0, t.r0, p), r1 = lerpN(f.r1, t.r1, p)
      outRadials.push({ angle, r0, r1, kind: 'port', hueRow: null })
      portAnchors[pr.name] = polar(angle, r1)
    }
    for (const [f, t] of rads.pairs) {
      const id = p < 0.5 ? f : t
      outRadials.push({ angle: lerpA(f.angle, t.angle, p), r0: lerpN(f.r0, t.r0, p), r1: lerpN(f.r1, t.r1, p), kind: id.kind, hueRow: id.hueRow })
    }
    for (const f of rads.loneA) {
      const m = (f.r0 + f.r1) / 2
      outRadials.push({ ...f, r0: lerpN(f.r0, m, p), r1: lerpN(f.r1, m, p) })
    }
    for (const t of rads.loneB) {
      const m = (t.r0 + t.r1) / 2
      outRadials.push({ ...t, r0: lerpN(m, t.r0, p), r1: lerpN(m, t.r1, p) })
    }
    const outArcs: NodeArc[] = []
    for (const [f, t] of arcs.pairs) {
      const m = lerpA((f.a0 + f.a1) / 2, (t.a0 + t.a1) / 2, p)
      const half = lerpN(f.a1 - f.a0, t.a1 - t.a0, p) / 2
      const id = p < 0.5 ? f : t
      outArcs.push({ r: lerpN(f.r, t.r, p), a0: m - half, a1: m + half, kind: id.kind, hueRow: id.hueRow })
    }
    for (const f of arcs.loneA) {
      const m = (f.a0 + f.a1) / 2
      outArcs.push({ ...f, a0: lerpN(f.a0, m, p), a1: lerpN(f.a1, m, p) })
    }
    for (const t of arcs.loneB) {
      const m = (t.a0 + t.a1) / 2
      outArcs.push({ ...t, a0: lerpN(m, t.a0, p), a1: lerpN(m, t.a1, p) })
    }
    // the exit: outputAnchor sits on angle 0 in both stages, so a straight
    // lerp IS the polar lerp; exit line/arc collapse when one side lacks them
    const outputAnchor = { x: lerpN(from.outputAnchor.x, to.outputAnchor.x, p), y: lerpN(from.outputAnchor.y, to.outputAnchor.y, p) }
    const exF = from.exitLine ?? ([from.outputAnchor, from.outputAnchor] as const)
    const exT = to.exitLine ?? ([to.outputAnchor, to.outputAnchor] as const)
    const exitLine: readonly [Vec2, Vec2] | null = from.exitLine === null && to.exitLine === null ? null : [
      { x: lerpN(exF[0].x, exT[0].x, p), y: lerpN(exF[0].y, exT[0].y, p) },
      { x: lerpN(exF[1].x, exT[1].x, p), y: lerpN(exF[1].y, exT[1].y, p) },
    ]
    const exitArc = from.exitArc === null && to.exitArc === null ? null : (() => {
      const f = from.exitArc ?? { r: to.exitArc!.r, a0: (to.exitArc!.a0 + to.exitArc!.a1) / 2, a1: (to.exitArc!.a0 + to.exitArc!.a1) / 2 }
      const t = to.exitArc ?? { r: from.exitArc!.r, a0: (from.exitArc!.a0 + from.exitArc!.a1) / 2, a1: (from.exitArc!.a0 + from.exitArc!.a1) / 2 }
      const m = lerpA((f.a0 + f.a1) / 2, (t.a0 + t.a1) / 2, p)
      const half = lerpN(f.a1 - f.a0, t.a1 - t.a0, p) / 2
      return { r: lerpN(f.r, t.r, p), a0: m - half, a1: m + half }
    })()
    return {
      outerRadius: lerpN(from.outerRadius, to.outerRadius, p),
      arcs: outArcs,
      radials: outRadials,
      outputAnchor,
      portAnchors,
      exitLine,
      exitArc,
    }
  }
}
