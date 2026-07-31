import type { Vec2 } from '../vec'
import type { Bounds, Disc, HugArc } from './freespace'
import { FRAME_COST } from './freespace'

/**
 * THE DRAWN CURVE + ROD ENERGY (USER ruling 2026-07-24: "the minimal energy
 * curves should be gentle... the energy function for the curve shapes is
 * simply wrong — rethink it from first principles").
 *
 * First principles: a wire is a thin elastic rod (the standing physical-wire
 * law). Its shape energy is the classical functional
 *
 *     E[curve] = ∫ (α + β·κ(s)²) ds        (α = 1: unit tension)
 *
 * A total-turn charge is placement-invariant (a sharp corner and a wide arc
 * with the same net turn cost the same), so its minimizers are exactly
 * straight polylines with point corners — the observed defect. κ² breaks the
 * invariance: for a fixed net turn Δθ over arclength L the bending cost is
 * β·Δθ²/L, DECREASING in L, so turning spreads out and the minimizers are
 * gentle. The balance defines the characteristic bend radius r* = √(β/α);
 * bends flatter than r* are nearly free, tighter ones increasingly dear. β is
 * DERIVED, not tuned: r* = the node-disc scale (bends happen at the scale of
 * the objects they route around), so β = r*².
 *
 * The drawn curve of a routed edge is a DETERMINISTIC cubic Hermite spline
 * through the route's waypoints: clamped tangents where the edge meets a
 * fixed anchor (port rim → outward normal; frame slot → inward normal —
 * perpendicular meetings by energy, not construction), free (natural) ends at
 * junctions and dots. No curve state exists — edges stay incidences only;
 * the same construction is rendered and charged (drawn = charged, one law).
 */

/** Terminal boundary condition: fixed anchor point + the unit direction the
    curve LEAVES it (null = natural end at the raw endpoint). */
export type CurveBC = { readonly p: Vec2; readonly n: Vec2 } | null

const sub = (a: Vec2, b: Vec2): Vec2 => ({ x: a.x - b.x, y: a.y - b.y })
const len = (a: Vec2): number => Math.hypot(a.x, a.y)

const wrapA = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

/**
 * THE CURVE FAMILY (USER LAW, 2026-07-24): wires are drawn as HOBBY cubic
 * splines — the round-8 render-lab family ("good to integrate"), ported
 * faithfully from render-lab8/round9-spline (hobbyRho mock-curvature
 * velocity, cubic control arms |rho|·d/3). Spiral-curvature representations
 * (Euler spirals, clothoids, θ-polynomials) are BANNED — the plan-22
 * elastica legs were an approximation of this family that introduced
 * exactly that banned class. Arc-line-arc constant-curvature chains are
 * likewise rejected (mechanical drafting look). The cubics are sampled for
 * both painting and energy — what is drawn IS what is charged.
 */
function hobbyRho(t: number, f: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  return (2 + a * (Math.sin(t) - b * Math.sin(f)) * (Math.sin(f) - b * Math.sin(t)) * (Math.cos(t) - Math.cos(f))) /
    (1 + (1 - c) * Math.cos(t) + c * Math.cos(f))
}

export type Cubic = { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }

/** One Hobby segment: pa → pb with OUTWARD tangent angles at both ends
    (start: forward travel; end: forward + π, or the far rim's port normal). */
function hobbySeg(pa: Vec2, ta: number, pb: Vec2, tb: number): Cubic {
  const chord = Math.atan2(pb.y - pa.y, pb.x - pa.x)
  const d = Math.hypot(pb.x - pa.x, pb.y - pa.y)
  const th = wrapA(ta - chord), ph = wrapA(chord - (tb + Math.PI))
  const ra = (Math.abs(hobbyRho(th, ph)) * d) / 3
  const rb = (Math.abs(hobbyRho(ph, th)) * d) / 3
  return {
    a: pa,
    c1: { x: pa.x + Math.cos(ta) * ra, y: pa.y + Math.sin(ta) * ra },
    c2: { x: pb.x + Math.cos(tb) * rb, y: pb.y + Math.sin(tb) * rb },
    b: pb,
  }
}

/** Samples per cubic (the lab's SUB): painting and energy share them. */
const SUB = 7

export function sampleCubics(cubics: readonly Cubic[]): Vec2[] {
  const out: Vec2[] = []
  for (const c of cubics) {
    const from = out.length === 0 ? 0 : 1
    for (let k = from; k <= SUB; k++) {
      const t = k / SUB
      const u = 1 - t
      const p = {
        x: u * u * u * c.a.x + 3 * u * u * t * c.c1.x + 3 * u * t * t * c.c2.x + t * t * t * c.b.x,
        y: u * u * u * c.a.y + 3 * u * u * t * c.c1.y + 3 * u * t * t * c.c2.y + t * t * t * c.b.y,
      }
      const last = out[out.length - 1]
      if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
      out.push(p)
    }
  }
  return out
}

/** Max hug angle one Hobby piece may span. The interior anchors exist ONLY to
    keep the drawn curve on the route's side of the hugged disc — never to
    trace the arc — and one tangent-clamped piece cannot reach the disc's far
    side while its subtended angle is under π; π/2 takes that bound with a 2×
    margin. At π/2 a cubic with tangential ends deviates from the circular arc
    by ~3·10⁻⁴·r (the classical quarter-circle cubic bound), so every span
    choice in [π/3, π] draws visually identical curves — a derived bound, not
    a tuning knob (executable: the span-insensitivity test). */
const HUG_SPAN = Math.PI / 2

/** The anchors of one hugging arc: its ENTRY and EXIT tangency points plus
    interior points on a fixed HUG_SPAN angular grid from the entry, each
    carrying the circle's EXACT tangent direction there (in the direction of
    travel). Anchoring the tangency points pins the curve at contact (the
    free entry/exit blends happen OUTSIDE the hug, so they cannot sag into the
    disc), and the grid rule makes the construction CONTINUOUS in the sweep: a
    new grid anchor appears precisely when the sweep crosses a grid multiple —
    i.e. exactly AT the exit anchor, already on the curve — and then separates
    smoothly. Equal-fraction placement would instead relocate every anchor
    whenever the count steps (a visible pop). */
function hugAnchors(h: HugArc): { p: Vec2; t: number }[] {
  const dir = h.sweep >= 0 ? 1 : -1
  const at = (a: number): { p: Vec2; t: number } => ({
    p: { x: h.c.x + h.r * Math.cos(a), y: h.c.y + h.r * Math.sin(a) },
    t: a + (Math.PI / 2) * dir,
  })
  const out: { p: Vec2; t: number }[] = [at(h.from)]
  const n = Math.floor(Math.abs(h.sweep) / HUG_SPAN + 1e-9)
  for (let k = 1; k <= n; k++) out.push(at(h.from + dir * HUG_SPAN * k))
  out.push(at(h.from + h.sweep))
  return out
}

/**
 * The drawn curve of one edge: the Hobby cubic chain anchored on the route's
 * CONTACT STRUCTURE (spec 2026-07-31). Anchors are the two terminals plus the
 * hug anchors of each contact arc; straight runs contribute nothing. A spline
 * through the route's sampled polyline reproduces the router's tangent-line-
 * plus-circular-arc geodesic — the rejected drafting look — so the samples
 * never reach the drawing. Clamped ends (port rim → outward normal, frame
 * slot → inward normal) fix the end tangents and REPLACE the route's
 * endpoints (the escape point is the anchor displaced along the clamp normal
 * — the same boundary datum — so keeping both would interpolate one datum
 * twice); every interior anchor carries its exact geometric tangent, so no
 * tangent is ever estimated from neighboring points; natural ends (junctions,
 * dots) take the chord toward the adjacent anchor. Deterministic, closed
 * form, stateless; the same samples are rendered and charged.
 */
export function edgeCurvePts(
  u: CurveBC,
  v: CurveBC,
  start: Vec2,
  end: Vec2,
  hugs: readonly HugArc[],
  clampLayer = 0,
): Vec2[] {
  return sampleCubics(edgeCurveCubics(u, v, start, end, hugs, clampLayer))
}

/** The edge's Hobby cubic chain itself — the renderer draws THESE as true
    Bézier path segments (sampled polylines are for energy and hit-testing;
    drawing them as line segments is visibly faceted). */
export function edgeCurveCubics(
  u: CurveBC,
  v: CurveBC,
  start: Vec2,
  end: Vec2,
  hugs: readonly HugArc[],
  clampLayer = 0,
): Cubic[] {
  const a0: Vec2 = u !== null ? { ...u.p } : { ...start }
  const a1: Vec2 = v !== null ? { ...v.p } : { ...end }
  // Interior anchors, dropping any that coincide with a terminal anchor (a
  // grazing contact at an endpoint — the terminal's clamp wins), and any
  // within `clampLayer` (= r*, the rod bend radius — USER rod ruling
  // 2026-07-24) of a CLAMPED terminal: a rod cannot conform to contact detail
  // inside its own bend scale, and a wire leaving a port immediately hugs its
  // own node's inflated disc, putting a tangency anchor with a perpendicular
  // tangent right next to the clamp — one boundary datum interpolated twice
  // (measured: a 0.54-radius curl at the port of a forced U-turn).
  const inLayer = (bc: CurveBC, p: Vec2): boolean =>
    bc !== null && Math.hypot(p.x - bc.p.x, p.y - bc.p.y) < clampLayer
  const interior = hugs.flatMap(hugAnchors).filter(
    (a) =>
      Math.hypot(a.p.x - a0.x, a.p.y - a0.y) >= 1e-9 &&
      Math.hypot(a.p.x - a1.x, a.p.y - a1.y) >= 1e-9 &&
      !inLayer(u, a.p) && !inLayer(v, a.p),
  )
  const Q: { p: Vec2; t: number | null }[] = [{ p: a0, t: null }]
  for (const a of interior) {
    const last = Q[Q.length - 1]!
    if (Math.hypot(a.p.x - last.p.x, a.p.y - last.p.y) < 1e-9) continue
    Q.push({ p: a.p, t: a.t })
  }
  if (Math.hypot(a1.x - Q[Q.length - 1]!.p.x, a1.y - Q[Q.length - 1]!.p.y) >= 1e-9) Q.push({ p: a1, t: null })
  if (Q.length < 2) return []
  const m = Q.length - 1
  const chord = (i: number, j: number): number => Math.atan2(Q[j]!.p.y - Q[i]!.p.y, Q[j]!.p.x - Q[i]!.p.x)
  const uAng = u !== null ? Math.atan2(u.n.y, u.n.x) : chord(0, 1)
  const vAng = v !== null ? Math.atan2(v.n.y, v.n.x) : chord(m - 1, m) + Math.PI
  const cubics: Cubic[] = []
  for (let i = 0; i + 1 < Q.length; i++) {
    const ta = i === 0 ? uAng : Q[i]!.t!
    const tb = i + 1 === m ? vAng : Q[i + 1]!.t! + Math.PI
    cubics.push(hobbySeg(Q[i]!.p, ta, Q[i + 1]!.p, tb))
  }
  return cubics
}

/** The family chain through a full anchor sequence (terminal anchors included):
    clamped end tangents from the boundary conditions, chord (central
    difference) tangents at the free interior anchors — the family's own
    construction rule on its own control points. Shared by the solver's energy
    evaluations and the frozen-probe rebuild (same anchors ⇒ same curve). */
export function chainThroughAnchors(u: CurveBC, v: CurveBC, anchors: readonly Vec2[]): Cubic[] {
  const Q: Vec2[] = []
  for (const p of anchors) {
    const last = Q[Q.length - 1]
    if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
    Q.push(p)
  }
  if (Q.length < 2) return []
  const m = Q.length - 1
  const chord = (i: number, j: number): number => Math.atan2(Q[j]!.y - Q[i]!.y, Q[j]!.x - Q[i]!.x)
  const uAng = u !== null ? Math.atan2(u.n.y, u.n.x) : chord(0, 1)
  const vAng = v !== null ? Math.atan2(v.n.y, v.n.x) : chord(m - 1, m) + Math.PI
  const cubics: Cubic[] = []
  for (let i = 0; i + 1 < Q.length; i++) {
    const ta = i === 0 ? uAng : chord(Math.max(0, i - 1), Math.min(m, i + 1))
    const tb = i + 1 === m ? vAng : chord(Math.max(0, i), Math.min(m, i + 2)) + Math.PI
    cubics.push(hobbySeg(Q[i]!, ta, Q[i + 1]!, tb))
  }
  return cubics
}

/** Uniform-arclength resample of a polyline to exactly n points (endpoints
    kept). */
function resampleByArclength(pts: readonly Vec2[], n: number): Vec2[] {
  const cum: number[] = [0]
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1]!, b = pts[i]!
    cum.push(cum[i - 1]! + Math.hypot(b.x - a.x, b.y - a.y))
  }
  const L = cum[cum.length - 1]!
  const out: Vec2[] = []
  let seg = 1
  for (let k = 0; k < n; k++) {
    const s = (L * k) / (n - 1)
    while (seg < pts.length - 1 && cum[seg]! < s) seg++
    const a = pts[seg - 1]!, b = pts[seg]!
    const ds = cum[seg]! - cum[seg - 1]!
    const f = ds < 1e-12 ? 0 : (s - cum[seg - 1]!) / ds
    out.push({ x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f })
  }
  return out
}

/**
 * THE DRAWN CURVE (energy-drawn wires, USER-confirmed design 2026-07-31): the
 * minimizer of `curveEnergy` over family chains between the edge's boundary
 * data, found by a DETERMINISTIC fixed-budget coordinate descent on free
 * interior anchors. The route contributes only the SEED (and with it the
 * side of each obstacle); no route geometry is drawn or anchored — the
 * energy, which charges nearness, lifts the curve to its resting standoff on
 * its own.
 *
 * Anchor count: one interior anchor per π·r* of seed arclength (r* = √β, the
 * characteristic bend radius). Bends tighter than r* are energetically
 * prohibitive, so resting shapes carry no features below that scale and the
 * densification is a resolution floor, not a knob (halving the spacing draws
 * the same curves — executable insensitivity, energy-drawn.test.ts).
 *
 * Step schedule: R, R/2, R/4, R/8 (R = the clearance radius, the scale the
 * nearness term acts on), one deterministic sweep per step, best-of-4 axis
 * probe per anchor, strict decrease to accept. Same inputs ⇒ same curve; no
 * state anywhere.
 */
export function solveEdgeCurve(
  u: CurveBC,
  v: CurveBC,
  start: Vec2,
  end: Vec2,
  hugs: readonly HugArc[],
  ns: NearSpace,
  beta: number,
): { cubics: Cubic[]; pts: Vec2[]; anchors: Vec2[] } {
  const seed = edgeCurveCubics(u, v, start, end, hugs, Math.sqrt(beta))
  if (seed.length === 0) return { cubics: [], pts: [], anchors: [] }
  const seedPts = sampleCubics(seed)
  let L = 0
  for (let i = 1; i < seedPts.length; i++) L += Math.hypot(seedPts[i]!.x - seedPts[i - 1]!.x, seedPts[i]!.y - seedPts[i - 1]!.y)
  // anchor spacing = π × the energy's smallest feature scale: the bend radius
  // r* = √β when bending exists, else the nearness radius R (the only other
  // length scale the energy defines); with neither, the curve has no features
  // and needs no interior freedom
  const rstar = Math.sqrt(beta)
  const featureScale = rstar > 1e-9 ? rstar : ns.R
  const K = featureScale > 1e-9 ? Math.max(0, Math.ceil(L / (Math.PI * featureScale)) - 1) : 0
  const a0: Vec2 = u !== null ? { ...u.p } : { ...start }
  const a1: Vec2 = v !== null ? { ...v.p } : { ...end }
  if (K === 0) {
    const cubics = chainThroughAnchors(u, v, [a0, a1])
    return { cubics, pts: sampleCubics(cubics), anchors: [] }
  }
  const resampled = resampleByArclength(seedPts, K + 2)
  const anchors: Vec2[] = resampled.slice(1, K + 1)
  // Disc prefilter: the descent can move an anchor at most Σ(R/2ᵏ) < 2R off
  // its seed, and nearness reads a disc up to R past its boundary, so only
  // discs within 3R of the seed's bounding box can ever contribute — the rest
  // are exactly zero for every candidate this solve evaluates.
  let bx0 = Infinity, by0 = Infinity, bx1 = -Infinity, by1 = -Infinity
  for (const p of seedPts) {
    bx0 = Math.min(bx0, p.x); by0 = Math.min(by0, p.y)
    bx1 = Math.max(bx1, p.x); by1 = Math.max(by1, p.y)
  }
  const reach = 3 * ns.R
  // The frame charges only OUTSIDE the border, so a chain whose seed sits
  // `reach` inside every wall cannot be charged by any candidate this solve
  // evaluates — drop the bounds from the descent's evaluations entirely.
  const frameNear = ns.bounds !== null && !(
    bx0 >= ns.bounds.minX + reach && bx1 <= ns.bounds.maxX - reach &&
    by0 >= ns.bounds.minY + reach && by1 <= ns.bounds.maxY - reach
  )
  const near: NearSpace = {
    discs: ns.discs.filter((D) => {
      const dx = D.c.x - Math.max(bx0, Math.min(D.c.x, bx1))
      const dy = D.c.y - Math.max(by0, Math.min(D.c.y, by1))
      return Math.hypot(dx, dy) <= D.r + reach
    }),
    bounds: frameNear ? ns.bounds : null, R: ns.R, slope: ns.slope,
  }
  // Fixed-budget deterministic coordinate descent; when no filtered disc and
  // no frame wall is in reach the seed already minimizes (tension+bending is
  // what built it), so the budget is spent only where the nearness term acts.
  if (near.discs.length > 0 || frameNear) {
    // Incremental machinery: the chain is kept as per-cubic sample arrays with
    // per-span energies (span i = cubic i's segments + its interior bends +
    // the joint bend with cubic i−1), summing EXACTLY to curveEnergy of the
    // concatenated polyline. Moving anchor j rebuilds cubics [j−2, j+1] and
    // spans [j−2, j+2] only — the probe cost is O(1) in chain length.
    const A: Vec2[] = [a0, ...anchors, a1]
    const last = A.length - 1
    const chord = (i: number, j: number): number => Math.atan2(A[j]!.y - A[i]!.y, A[j]!.x - A[i]!.x)
    const buildCubic = (i: number): Cubic => {
      const ta = i === 0 ? (u !== null ? Math.atan2(u.n.y, u.n.x) : chord(0, 1)) : chord(i - 1, i + 1)
      const tb = i + 1 === last
        ? (v !== null ? Math.atan2(v.n.y, v.n.x) : chord(last - 1, last) + Math.PI)
        : chord(i, i + 2) + Math.PI
      return hobbySeg(A[i]!, ta, A[i + 1]!, tb)
    }
    const sampleOne = (c: Cubic): Vec2[] => {
      const out: Vec2[] = []
      for (let k = 0; k <= SUB; k++) {
        const t = k / SUB, w = 1 - t
        out.push({
          x: w * w * w * c.a.x + 3 * w * w * t * c.c1.x + 3 * w * t * t * c.c2.x + t * t * t * c.b.x,
          y: w * w * w * c.a.y + 3 * w * w * t * c.c1.y + 3 * w * t * t * c.c2.y + t * t * t * c.b.y,
        })
      }
      return out
    }
    const segE = (a: Vec2, b: Vec2): number => {
      const L = Math.hypot(b.x - a.x, b.y - a.y)
      if (L < 1e-12) return 0
      let s = L
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2
      for (const D of near.discs) {
        const g = Math.hypot(mx - D.c.x, my - D.c.y) - D.r
        if (g < near.R) { const t = near.R - g; s += (L * near.slope * t * t) / near.R }
      }
      if (near.bounds !== null) {
        const N = 8
        let out = 0
        for (let k = 0; k <= N; k++) {
          const t = k / N
          const x = a.x + (b.x - a.x) * t, y = a.y + (b.y - a.y) * t
          if (x < near.bounds.minX || x > near.bounds.maxX || y < near.bounds.minY || y > near.bounds.maxY) out++
        }
        s += FRAME_COST * L * (out / (N + 1))
      }
      return s
    }
    const bendE = (p0: Vec2, p1: Vec2, p2: Vec2): number => {
      const ax = p1.x - p0.x, ay = p1.y - p0.y
      const bx2 = p2.x - p1.x, by2 = p2.y - p1.y
      const la = Math.hypot(ax, ay), lb = Math.hypot(bx2, by2)
      if (la < 1e-12 || lb < 1e-12) return 0
      const dot = Math.max(-1, Math.min(1, (ax * bx2 + ay * by2) / (la * lb)))
      const dth = Math.acos(dot)
      return (beta * dth * dth) / ((la + lb) / 2)
    }
    const spanEnergy = (prev: readonly Vec2[] | null, cur: readonly Vec2[]): number => {
      let s = 0
      for (let k = 0; k + 1 < cur.length; k++) s += segE(cur[k]!, cur[k + 1]!)
      for (let k = 1; k + 1 < cur.length; k++) s += bendE(cur[k - 1]!, cur[k]!, cur[k + 1]!)
      if (prev !== null) s += bendE(prev[prev.length - 2]!, cur[0]!, cur[1]!)
      return s
    }
    const nC = last // cubic count
    const cubPts: Vec2[][] = []
    for (let i = 0; i < nC; i++) cubPts.push(sampleOne(buildCubic(i)))
    const spans: number[] = []
    for (let i = 0; i < nC; i++) spans.push(spanEnergy(i > 0 ? cubPts[i - 1]! : null, cubPts[i]!))
    for (const h of [ns.R, ns.R / 2, ns.R / 4, ns.R / 8]) {
      for (let j = 1; j <= K; j++) {
        const lo = Math.max(0, j - 2), hi = Math.min(nC - 1, j + 1)
        const shi = Math.min(nC - 1, hi + 1)
        let oldPart = 0
        for (let i2 = lo; i2 <= shi; i2++) oldPart += spans[i2]!
        const p = A[j]!
        let bestD = -1e-12
        let bestP: Vec2 | null = null
        let bestPts: Vec2[][] | null = null
        let bestSpans: number[] | null = null
        for (const [dx, dy] of [[h, 0], [-h, 0], [0, h], [0, -h]] as const) {
          A[j] = { x: p.x + dx, y: p.y + dy }
          const trialPts: Vec2[][] = []
          for (let i2 = lo; i2 <= hi; i2++) trialPts.push(sampleOne(buildCubic(i2)))
          const at = (i2: number): Vec2[] => (i2 >= lo && i2 <= hi ? trialPts[i2 - lo]! : cubPts[i2]!)
          const trialSpans: number[] = []
          let newPart = 0
          for (let i2 = lo; i2 <= shi; i2++) {
            const sE = spanEnergy(i2 > 0 ? at(i2 - 1) : null, at(i2))
            trialSpans.push(sE)
            newPart += sE
          }
          const d = newPart - oldPart
          if (d < bestD) { bestD = d; bestP = A[j]!; bestPts = trialPts; bestSpans = trialSpans }
        }
        if (bestP !== null) {
          A[j] = bestP
          for (let i2 = lo; i2 <= hi; i2++) cubPts[i2] = bestPts![i2 - lo]!
          for (let i2 = lo; i2 <= shi; i2++) spans[i2] = bestSpans![i2 - lo]!
        } else {
          A[j] = p
        }
      }
    }
    for (let j = 1; j <= K; j++) anchors[j - 1] = A[j]!
  }
  const cubics = chainThroughAnchors(u, v, [a0, ...anchors, a1])
  return { cubics, pts: sampleCubics(cubics), anchors }
}

/**
 * THE NEARNESS SPACE (energy-drawn wires, USER-confirmed design 2026-07-31):
 * the DRAWN geometry a wire's curve is charged for being close to — node
 * discs and foreign cut circles at their drawn radii (no routing clearance
 * folded in), plus the frame box. `R`/`slope` are the ONE clearance law: the
 * same falloff wires pay against each other (WIREP.sepR/sepSlope), applied
 * uniformly to being near anything. There is no separate "inside" charge —
 * inside is the deep end of near, on the same quadratic.
 */
export type NearSpace = {
  readonly discs: readonly Disc[]
  readonly bounds: Bounds | null
  readonly R: number
  readonly slope: number
}

/** Nearness cost density (per unit of curve length) at a point. */
export function nearnessAt(p: Vec2, ns: NearSpace): number {
  let v = 0
  for (const D of ns.discs) {
    const g = Math.hypot(p.x - D.c.x, p.y - D.c.y) - D.r
    if (g < ns.R) {
      const t = ns.R - g
      v += (ns.slope * t * t) / ns.R
    }
  }
  return v
}

/** Nearness cost of one segment against ONE disc (midpoint quadrature × length
    — the same rule `curveEnergy` integrates with, so incremental patches are
    exact against it). */
export function segNearness(a: Vec2, b: Vec2, D: Disc, R: number, slope: number): number {
  const L = Math.hypot(b.x - a.x, b.y - a.y)
  if (L < 1e-12) return 0
  const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2
  const g = Math.hypot(mx - D.c.x, my - D.c.y) - D.r
  if (g >= R) return 0
  const t = R - g
  return (L * slope * t * t) / R
}

/**
 * THE curve energy: tension (length) + out-of-frame surcharge + nearness
 * (midpoint quadrature per segment) + β·Σ Δθᵢ²/Δs̄ᵢ (the discrete ∫κ²ds).
 * A point corner concentrates Δθ over vanishing Δs̄ and diverges — corners
 * cannot survive at a minimum. This is what the renderer draws, the gates
 * gate, and the layout score integrates: drawn = charged, one law.
 */
export function curveEnergy(pts: readonly Vec2[], ns: NearSpace, beta: number): number {
  let E = 0
  for (let i = 0; i + 1 < pts.length; i++) {
    const a = pts[i]!, b = pts[i + 1]!
    const L = Math.hypot(b.x - a.x, b.y - a.y)
    if (L < 1e-12) continue
    E += L
    const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2
    for (const D of ns.discs) {
      const g = Math.hypot(mx - D.c.x, my - D.c.y) - D.r
      if (g < ns.R) {
        const t = ns.R - g
        E += (L * ns.slope * t * t) / ns.R
      }
    }
    if (ns.bounds !== null) {
      const N = 8
      let out = 0
      for (let k = 0; k <= N; k++) {
        const t = k / N
        const x = a.x + (b.x - a.x) * t, y = a.y + (b.y - a.y) * t
        if (x < ns.bounds.minX || x > ns.bounds.maxX || y < ns.bounds.minY || y > ns.bounds.maxY) out++
      }
      E += FRAME_COST * L * (out / (N + 1))
    }
  }
  for (let i = 1; i + 1 < pts.length; i++) {
    const a = sub(pts[i]!, pts[i - 1]!)
    const b = sub(pts[i + 1]!, pts[i]!)
    const la = len(a), lb = len(b)
    if (la < 1e-12 || lb < 1e-12) continue
    const dot = Math.max(-1, Math.min(1, (a.x * b.x + a.y * b.y) / (la * lb)))
    const dth = Math.acos(dot)
    E += (beta * dth * dth) / ((la + lb) / 2)
  }
  return E
}
