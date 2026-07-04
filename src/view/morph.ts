import { bendMaps, type NodeArc, type NodeGeometry, type NodeRadial } from './bend'
import type { Bar, Rail, Stem, TrompGrid } from './tromp'
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

// ---- GRID-SPACE MORPHING (connection-preserving). bendGrid is a pure image
// of integer grid coordinates through the frame maps theta(col)/radius(row),
// so INCIDENCE IS A SHARED COORDINATE: a stem touches its bar because
// stem.rowTop === bar.row. Linear interpolation preserves equalities that
// hold at both endpoints, so pairing elements in GRID space and lerping both
// their coordinates and the frame keeps every surviving junction connected
// at every p — no snapping pass. The unpaired follow the user's ruling
// ("shrink while still connected, disappear before disconnecting") via a
// three-phase clock: dying pieces retract INTO their host while the grid
// holds still (phase A), the paired skeleton morphs (phase B), born pieces
// grow OUT of their host on the settled target grid (phase C). Equal thirds:
// each phase is one visual beat of the step.
const A_END = 1 / 3
const B_END = 2 / 3

type BarPair = { from: Bar | null; to: Bar | null }
type StemPair = { from: Stem | null; to: Stem | null }
type RailPair = { from: Rail | null; to: Rail | null }

/** On-screen travel a pairing would cause — the principled matching cost:
    minimize how far each piece moves. Host-incoherent pairs (the stem's bar
    at one end is NOT the pair of its bar at the other) rank strictly below
    every coherent pair (lexicographic via an additive bound exceeding any
    possible travel): an incoherent pair detaches mid-morph, which is the
    exact defect this interpolator exists to remove. */
const INCOHERENT = 1e6

export function mkGridMorph(gF: TrompGrid, gT: TrompGrid): (p: number) => NodeGeometry {
  const mF = bendMaps(gF.cols, gF.rows, gF.railRows)
  const mT = bendMaps(gT.cols, gT.rows, gT.railRows)
  const meanR = (mF.pierceR + mT.pierceR) / 2

  // ---- rails pair BY NAME (port identity is semantic)
  const railNames = [...new Set([...gF.rails.map((r) => r.name), ...gT.rails.map((r) => r.name)])]
  const rails: RailPair[] = railNames.map((name) => ({
    from: gF.rails.find((r) => r.name === name) ?? null,
    to: gT.rails.find((r) => r.name === name) ?? null,
  }))

  // ---- bars: rail bars ride their rail's pairing; lam/app pair per kind by
  // least travel
  const railBarF = new Map(gF.rails.map((r) => [r.name, gF.bars.find((b) => b.kind === 'rail' && b.row === r.row)!]))
  const railBarT = new Map(gT.rails.map((r) => [r.name, gT.bars.find((b) => b.kind === 'rail' && b.row === r.row)!]))
  const barTravel = (a: Bar, b: Bar): number =>
    Math.abs(mF.radius(a.row) - mT.radius(b.row))
    + (Math.abs(mF.theta(a.colStart) - mT.theta(b.colStart)) + Math.abs(mF.theta(a.colEnd) - mT.theta(b.colEnd))) * meanR
  const bars: BarPair[] = []
  const barPairOf = new Map<Bar, Bar>()
  for (const name of railNames) {
    const f = railBarF.get(name) ?? null, t = railBarT.get(name) ?? null
    bars.push({ from: f, to: t })
    if (f !== null && t !== null) barPairOf.set(f, t)
  }
  for (const kind of ['lam', 'app'] as const) {
    const fs = gF.bars.filter((b) => b.kind === kind)
    const ts = gT.bars.filter((b) => b.kind === kind)
    const g = greedyPairs(fs, ts, barTravel)
    for (const [f, t] of g.pairs) { bars.push({ from: f, to: t }); barPairOf.set(f, t) }
    for (const f of g.loneA) bars.push({ from: f, to: null })
    for (const t of g.loneB) bars.push({ from: null, to: t })
  }

  // ---- stems: output pairs with output; port drops pair per NAME by least
  // travel; var stems pair by least travel, host-coherent pairs first
  const hostOf = (g: TrompGrid, s: Stem): Bar | null =>
    g.bars.find((b) => b.row === s.rowTop && b.colStart <= s.col && s.col <= b.colEnd) ?? null
  const stemTravel = (a: Stem, b: Stem): number =>
    Math.abs(mF.theta(a.col) - mT.theta(b.col)) * meanR
    + Math.abs(mF.radius(a.rowTop) - mT.radius(b.rowTop)) + Math.abs(mF.radius(a.rowBottom) - mT.radius(b.rowBottom))
  // host-coherent pairs first (lexicographic): a stem paired across
  // NON-paired host bars keeps living while its bar dies — detaching mid-B,
  // the exact defect this interpolator removes
  const stemCost = (a: Stem, b: Stem): number => {
    const hf = hostOf(gF, a), ht = hostOf(gT, b)
    const coherent = hf === null && ht === null ? true : hf !== null && ht !== null && barPairOf.get(hf) === ht
    return stemTravel(a, b) + (coherent ? 0 : INCOHERENT)
  }
  const stems: StemPair[] = []
  for (const name of railNames) {
    const fs = gF.stems.filter((s) => s.kind === 'port' && s.portName === name)
    const ts = gT.stems.filter((s) => s.kind === 'port' && s.portName === name)
    const g = greedyPairs(fs, ts, stemCost)
    for (const [f, t] of g.pairs) stems.push({ from: f, to: t })
    for (const f of g.loneA) stems.push({ from: f, to: null })
    for (const t of g.loneB) stems.push({ from: null, to: t })
  }
  for (const kind of ['var', 'output'] as const) {
    const fs = gF.stems.filter((s) => s.kind === kind)
    const ts = gT.stems.filter((s) => s.kind === kind)
    const g = greedyPairs(fs, ts, stemCost)
    for (const [f, t] of g.pairs) stems.push({ from: f, to: t })
    for (const f of g.loneA) stems.push({ from: f, to: null })
    for (const t of g.loneB) stems.push({ from: null, to: t })
  }

  // clamp a dying/born stem's col into its (possibly shrinking/growing) host
  // bar's span so a collapsing bar sweeps its stems up rather than leaving
  // them behind
  const shrunkSpan = (b: Bar, q: number, dying: boolean): { s: number; e: number } => {
    // a vanishing bar retracts toward an incident SURVIVING stem's column if
    // one exists (the junction that remains meaningful), else its midpoint
    const survivors = stems.filter((sp) => {
      const s = dying ? sp.from : sp.to
      const paired = dying ? sp.to !== null : sp.from !== null
      return s !== null && paired && (s.rowTop === b.row || s.rowBottom === b.row) && b.colStart <= s.col && s.col <= b.colEnd
    })
    const s0 = dying ? survivors[0]?.from : survivors[0]?.to
    const anchor = s0 !== undefined && s0 !== null ? s0.col : (b.colStart + b.colEnd) / 2
    return { s: lerpN(b.colStart, anchor, q), e: lerpN(b.colEnd, anchor, q) }
  }

  return (p: number): NodeGeometry => {
    // phase clocks: qA retracts the dying, qB moves the skeleton, qC grows
    const qA = Math.min(1, p / A_END)
    const qB = Math.max(0, Math.min(1, (p - A_END) / (B_END - A_END)))
    const qC = Math.max(0, (p - B_END) / (1 - B_END))
    const frame = bendMaps(
      lerpN(gF.cols, gT.cols, qB),
      lerpN(gF.rows, gT.rows, qB),
      lerpN(gF.railRows, gT.railRows, qB),
    )
    const { theta, radius, pierceR, a0 } = frame

    const outArcs: NodeArc[] = []
    const outRadials: NodeRadial[] = []
    const portAnchors: Record<string, Vec2> = {}
    const deadBarSpan = new Map<Bar, { s: number; e: number }>()

    for (const bp of bars) {
      if (bp.from !== null && bp.to !== null) {
        const row = lerpN(bp.from.row, bp.to.row, qB)
        const id = qB < 0.5 ? bp.from : bp.to
        outArcs.push({ r: radius(row), a0: theta(lerpN(bp.from.colStart, bp.to.colStart, qB)), a1: theta(lerpN(bp.from.colEnd, bp.to.colEnd, qB)), kind: id.kind, hueRow: id.row })
      } else if (bp.from !== null) {
        if (qA >= 1) continue
        const span = shrunkSpan(bp.from, qA, true)
        deadBarSpan.set(bp.from, span)
        outArcs.push({ r: radius(bp.from.row), a0: theta(span.s), a1: theta(span.e), kind: bp.from.kind, hueRow: bp.from.row })
      } else if (bp.to !== null) {
        if (qC <= 0) continue
        const span = shrunkSpan(bp.to, 1 - qC, false)
        deadBarSpan.set(bp.to, span)
        outArcs.push({ r: radius(bp.to.row), a0: theta(span.s), a1: theta(span.e), kind: bp.to.kind, hueRow: bp.to.row })
      }
    }

    const clampCol = (g: TrompGrid, s: Stem): number => {
      const host = hostOf(g, s)
      const span = host !== null ? deadBarSpan.get(host) : undefined
      return span === undefined ? s.col : Math.max(span.s, Math.min(span.e, s.col))
    }
    for (const sp of stems) {
      if (sp.from !== null && sp.to !== null) {
        const id = qB < 0.5 ? sp.from : sp.to
        outRadials.push({
          angle: theta(lerpN(sp.from.col, sp.to.col, qB)),
          r0: radius(lerpN(sp.from.rowTop, sp.to.rowTop, qB)),
          r1: radius(lerpN(sp.from.rowBottom, sp.to.rowBottom, qB)),
          kind: id.kind,
          hueRow: id.kind === 'var' ? id.rowTop : null,
        })
      } else if (sp.from !== null) {
        if (qA >= 1) continue
        const s = sp.from
        outRadials.push({ angle: theta(clampCol(gF, s)), r0: radius(s.rowTop), r1: radius(lerpN(s.rowBottom, s.rowTop, qA)), kind: s.kind, hueRow: s.kind === 'var' ? s.rowTop : null })
      } else if (sp.to !== null) {
        if (qC <= 0) continue
        const s = sp.to
        outRadials.push({ angle: theta(clampCol(gT, s)), r0: radius(s.rowTop), r1: radius(lerpN(s.rowTop, s.rowBottom, qC)), kind: s.kind, hueRow: s.kind === 'var' ? s.rowTop : null })
      }
    }

    for (const rp of rails) {
      if (rp.from !== null && rp.to !== null) {
        const angle = theta(lerpN(rp.from.stemCol, rp.to.stemCol, qB))
        const row = lerpN(rp.from.row, rp.to.row, qB)
        outRadials.push({ angle, r0: radius(row), r1: pierceR, kind: 'port', hueRow: null })
        portAnchors[rp.from.name] = polar(angle, pierceR)
      } else if (rp.from !== null) {
        // the pierce retracts to the rim with the rest of the dying port;
        // its anchor rides the tip so the wire dives into the rim with it
        const angle = theta(rp.from.stemCol)
        const rim = radius(rp.from.row)
        const tip = lerpN(pierceR, rim, qA)
        if (qA < 1) outRadials.push({ angle, r0: rim, r1: tip, kind: 'port', hueRow: null })
        portAnchors[rp.from.name] = polar(angle, tip)
      } else if (rp.to !== null) {
        const angle = theta(rp.to.stemCol)
        const rim = radius(rp.to.row)
        const tip = lerpN(rim, pierceR, qC)
        if (qC > 0) outRadials.push({ angle, r0: rim, r1: tip, kind: 'port', hueRow: null })
        portAnchors[rp.to.name] = polar(angle, tip)
      }
    }

    const outputCol = lerpN(gF.outputCol, gT.outputCol, qB)
    const outRows = lerpN(gF.rows, gT.rows, qB)
    const exitR = radius(outRows)
    const outputAnchor = polar(0, pierceR)
    return {
      outerRadius: pierceR + 0.5,
      arcs: outArcs,
      radials: outRadials,
      outputAnchor,
      portAnchors,
      exitArc: { r: exitR, a0, a1: theta(outputCol) },
      exitLine: [polar(a0, exitR), outputAnchor],
    }
  }
}
