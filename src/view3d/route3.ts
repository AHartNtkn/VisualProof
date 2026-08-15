import type { WireId } from '../kernel/diagram/diagram'
import {
  add3, anyPerp, cross3, dist3, dot3, len3, norm3, scale3, segClosest, segPointDist, segSegClosest, segSegDist, sub3, v3, type Vec3,
} from './vec3'

export type Capsule = { a: Vec3; b: Vec3; r: number }
export type EdgeIn = { p: Vec3; q: Vec3; tp: Vec3 | null; tq: Vec3 | null }
/** `exempt`: this net's OWN anchors and junctions — the only points/edges
    allowed to hug the tree or a sibling wire within an exemption ball.
    Exemption is never shared across nets: a later wire must clear an
    earlier wire's anchors just like any other obstacle. */
export type NetIn = { id: WireId; edges: EdgeIn[]; exempt: Vec3[] }

const MAX_ROUNDS = 60
const SMOOTH = 0.4

const capDir = (c: Capsule): Vec3 => {
  const d = sub3(c.b, c.a)
  const l = len3(d)
  return l < 1e-12 ? v3(0, 0, 1) : scale3(d, 1 / l)
}

const isExempt = (p: Vec3, exempt: readonly Vec3[], delta: number): boolean =>
  exempt.some((e) => dist3(p, e) < 2.5 * delta)

function penetrations(p: Vec3, obstacles: readonly Capsule[], delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const c of obstacles) if (segPointDist(p, c.a, c.b) < c.r + delta * (1 - 1e-9)) out.push(c)
  return out
}

/** Capsules whose clearance is violated by the EDGE [a,b], not just its
    endpoint samples — catches an interior dip toward an obstacle that both
    endpoints individually clear. This is what makes clearance symmetric:
    a later wire's edge is checked against an earlier wire's edges, not just
    against the earlier wire's sample points.

    Exemption is evaluated per capsule at the edge's OWN closest-approach
    point to THAT capsule, not at the edge's two discrete sample endpoints:
    a wire is allowed to hug the tree near its own anchor, and the curve
    approaching that anchor can dip closer to some nearby obstacle than
    either of its neighboring samples individually — sample density, not
    the underlying geometry, is what put the endpoints where they are.
    A rule that only inspects the two endpoints (e.g. "exempt when both
    are") is exactly wrong at the transition: the sample just outside the
    exemption ball can pair with one just inside to form an edge whose
    true closest approach still sits inside the ball, yet the rule would
    flag it as a real violation with no exempt endpoint able to explain it
    away. Testing the actual closest point is what makes exemption
    well-defined regardless of sampling density. */
function edgeHits(a: Vec3, b: Vec3, obstacles: readonly Capsule[], exempt: readonly Vec3[], delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const c of obstacles) {
    if (segSegDist(a, b, c.a, c.b) >= c.r + delta * (1 - 1e-9)) continue
    const [onEdge] = segSegClosest(a, b, c.a, c.b)
    if (isExempt(onEdge, exempt, delta)) continue
    out.push(c)
  }
  return out
}

/** Deterministic escape: march along ±axis in delta/2 steps until clear. */
function escape(p: Vec3, axis: Vec3, obstacles: readonly Capsule[], delta: number): Vec3 {
  for (let j = 1; j <= 400; j++) {
    for (const sign of [1, -1]) {
      const cand = add3(p, scale3(axis, sign * j * (delta / 2)))
      if (penetrations(cand, obstacles, delta).length === 0) return cand
    }
  }
  throw new Error('route3: no escape direction cleared the obstacle set')
}

function pushOut(p: Vec3, hits: Capsule[], obstacles: readonly Capsule[], delta: number): Vec3 {
  if (hits.length === 1) {
    const c = hits[0]!
    const closest = segClosest(p, c.a, c.b)
    const radial = sub3(p, closest)
    const dir = len3(radial) < 1e-9 ? anyPerp(capDir(c)) : norm3(radial)
    const cand = add3(closest, scale3(dir, c.r + delta * (1 + 1e-3)))
    return penetrations(cand, obstacles, delta).length === 0 ? cand : escape(p, dir, obstacles, delta)
  }
  const ax = cross3(capDir(hits[0]!), capDir(hits[1]!))
  const axis = len3(ax) < 1e-6 ? anyPerp(capDir(hits[0]!)) : norm3(ax)
  return escape(p, axis, obstacles, delta)
}

/** Push a point out of the obstacle set to ≥ delta clearance. */
export function clearPoint(p: Vec3, obstacles: Capsule[], exempt: Vec3[], delta: number): Vec3 {
  if (isExempt(p, exempt, delta)) return p
  const hits = penetrations(p, obstacles, delta)
  return hits.length === 0 ? p : pushOut(p, hits, obstacles, delta)
}

/** Whether points a and b sit on opposite sides of capsule c's axis — a
    STRADDLING edge, the one case a per-point radial push can never resolve:
    both ends would retreat along the very line the edge itself lies on, so
    the segment between them keeps crossing the axis no matter how far they
    move. (An end sitting exactly on the axis has no radial direction at
    all, which is the same problem.) */
function straddles(a: Vec3, b: Vec3, c: Capsule): boolean {
  const ra = sub3(a, segClosest(a, c.a, c.b))
  const rb = sub3(b, segClosest(b, c.a, c.b))
  if (len3(ra) < 1e-9 || len3(rb) < 1e-9) return true
  return dot3(ra, rb) < 0
}

/** Jointly escape an edge's two endpoints transverse to the plane the edge
    and capsule `c`'s axis share (`cross3` of the two directions) — the only
    direction guaranteed to break a coplanar/threading crossing, since it
    moves the edge off that shared plane entirely rather than further along
    a line that already lies in it. Marches both endpoints additively in
    lockstep (`delta/2` steps, mirroring `escape`) from their CURRENT
    positions — not from a shared anchor — so nearby samples needing the
    same escape stay separated along the curve instead of collapsing onto
    one point. Accepted once the EDGE clears `c` by direct segment-vs-segment
    distance (the actual invariant, not assumed from point clearance), and
    each moved endpoint is independently point-clear of the full obstacle
    list. Only targets `c` — other simultaneous hits on this edge are left
    for later rounds/edges, matching how the point-based scan converges
    incrementally rather than solving every constraint in one shot. */
function escapeEdgeAcross(
  a: Vec3, b: Vec3, moveA: boolean, moveB: boolean, c: Capsule, obstacles: readonly Capsule[], delta: number,
): [Vec3, Vec3] {
  const rawEdge = sub3(b, a)
  const edgeDir = len3(rawEdge) < 1e-12 ? null : norm3(rawEdge)
  const cross = edgeDir === null ? v3(0, 0, 0) : cross3(capDir(c), edgeDir)
  const dir = len3(cross) > 1e-6 ? norm3(cross) : anyPerp(capDir(c))
  const target = c.r + delta * (1 + 1e-3)
  for (let j = 1; j <= 400; j++) {
    for (const sign of [1, -1]) {
      const na = moveA ? add3(a, scale3(dir, sign * j * (delta / 2))) : a
      const nb = moveB ? add3(b, scale3(dir, sign * j * (delta / 2))) : b
      if (segSegDist(na, nb, c.a, c.b) >= target
        && (!moveA || penetrations(na, obstacles, delta).length === 0)
        && (!moveB || penetrations(nb, obstacles, delta).length === 0)) return [na, nb]
    }
  }
  throw new Error('route3: no transverse escape cleared the edge')
}

/** Two points at the SAME radius from a straight axis but at different
    azimuths always have a connecting chord that dips inside that radius (a
    chord of a circle sits inside the circle) — so once both endpoints of a
    non-straddling edge are individually pinned to the minimum
    point-clearance radius, the edge itself can still be short of target.
    Scaling both points' radial offset from capsule `c`'s axis by the same
    factor k ≥ 1 fixes this (unlike translation): it increases each end's
    radius while preserving azimuth, monotonically opening the chord, so
    the minimal k is found by bisection (a numeric root-find, not a tuned
    constant). Returns null — never a silently-unresolved position — when
    an endpoint sits exactly on the axis (no radial direction to scale) or
    the bisection's doubling search cannot reach clearance within a
    generous bound; the caller falls back to `escapeEdgeAcross`. Only
    targets `c`, mirroring `escapeEdgeAcross`'s incremental scope. */
function tryScaleEdgeAcross(
  a: Vec3, b: Vec3, moveA: boolean, moveB: boolean, c: Capsule, delta: number,
): [Vec3, Vec3] | null {
  const closestA = segClosest(a, c.a, c.b)
  const closestB = segClosest(b, c.a, c.b)
  const radA = sub3(a, closestA)
  const radB = sub3(b, closestB)
  if (len3(radA) < 1e-9 || len3(radB) < 1e-9) return null
  const at = (k: number): [Vec3, Vec3] => [
    moveA ? add3(closestA, scale3(radA, k)) : a,
    moveB ? add3(closestB, scale3(radB, k)) : b,
  ]
  const target = c.r + delta * (1 + 1e-3)
  const clear = (k: number): boolean => {
    const [pa, pb] = at(k)
    return segSegDist(pa, pb, c.a, c.b) >= target
  }
  let hi = 4
  while (!clear(hi)) {
    if (hi > 1e6) return null
    hi *= 2
  }
  let lo = 1
  for (let it = 0; it < 60; it++) {
    const mid = (lo + hi) / 2
    if (!clear(mid)) lo = mid
    else hi = mid
  }
  return at(hi)
}

/** Resolve a penetrating edge against its single WORST-violating hit
    capsule (smallest current segment-vs-segment distance): scaling
    (`tryScaleEdgeAcross`) when the edge doesn't straddle that capsule's
    axis and the scale converges; transverse escape (`escapeEdgeAcross`)
    otherwise. Any OTHER simultaneous hits on this edge are left for
    subsequent rounds — the round loop is what converges the full obstacle
    set, one worst-offender resolution at a time, the same incremental
    shape as the original point-based scan. */
function resolveEdge(
  a: Vec3, b: Vec3, moveA: boolean, moveB: boolean, hits: readonly Capsule[],
  obstacles: readonly Capsule[], delta: number,
): [Vec3, Vec3] {
  let worst = hits[0]!
  let worstD = segSegDist(a, b, worst.a, worst.b)
  for (const c of hits) {
    const d = segSegDist(a, b, c.a, c.b)
    if (d < worstD) { worstD = d; worst = c }
  }
  if (!straddles(a, b, worst)) {
    const scaled = tryScaleEdgeAcross(a, b, moveA, moveB, worst, delta)
    if (scaled !== null) return scaled
  }
  return escapeEdgeAcross(a, b, moveA, moveB, worst, obstacles, delta)
}

function hermiteSeed(e: EdgeIn, delta: number): Vec3[] {
  const chord = sub3(e.q, e.p)
  const l = len3(chord)
  const dir = l < 1e-12 ? v3(0, 0, 1) : scale3(chord, 1 / l)
  const m0 = scale3(e.tp ?? dir, l)
  const m1 = scale3(e.tq ?? dir, l)
  const n = Math.min(240, Math.max(8, Math.ceil(l / (delta / 2))))
  const pts: Vec3[] = []
  for (let i = 0; i <= n; i++) {
    const t = i / n
    const h00 = 2 * t ** 3 - 3 * t ** 2 + 1
    const h10 = t ** 3 - 2 * t ** 2 + t
    const h01 = -2 * t ** 3 + 3 * t ** 2
    const h11 = t ** 3 - t ** 2
    pts.push(add3(
      add3(scale3(e.p, h00), scale3(m0, h10)),
      add3(scale3(e.q, h01), scale3(m1, h11)),
    ))
  }
  return pts
}

function repair(seed: Vec3[], obstacles: readonly Capsule[], exempt: readonly Vec3[], delta: number, label: string): Vec3[] {
  const pts = seed.map((p) => v3(p.x, p.y, p.z))
  for (let round = 0; round < MAX_ROUNDS; round++) {
    let dirty = false
    // Jacobi update: every edge in this round is tested and pushed against
    // the SAME pre-round snapshot, then all pushes are applied together.
    // Mutating `pts` mid-scan would let an already-pushed neighbor corrupt
    // the next edge's direction (its escape can flip out-of-plane on one
    // side and not the other), which stalls convergence — a shared sample
    // is claimed by the first penetrating edge that touches it, and every
    // claim in the round reads the identical starting geometry.
    const snapshot = pts.map((p) => v3(p.x, p.y, p.z))
    const updates = new Map<number, Vec3>()
    for (let i = 0; i < snapshot.length - 1; i++) {
      const a = snapshot[i]!, b = snapshot[i + 1]!
      const hits = edgeHits(a, b, obstacles, exempt, delta)
      if (hits.length === 0) continue
      dirty = true
      // A fixed terminal (index 0 / n) or an exempt sample never moves. A
      // sample already claimed by an earlier edge THIS round is different:
      // it WILL move, just via that other edge's own computation — solving
      // this edge as if it were permanently pinned there is wrong (it can
      // manufacture an impossible constraint, or waste motion on the other
      // end for a position that is about to change). Defer to next round,
      // once the claim has actually been applied, instead.
      const permFixed = (idx: number): boolean => idx === 0 || idx === snapshot.length - 1 || isExempt(snapshot[idx]!, exempt, delta)
      const permFixedA = permFixed(i), permFixedB = permFixed(i + 1)
      if (permFixedA && permFixedB) continue // truly unroutable here; the round cap throws if it never resolves elsewhere
      if (updates.has(i) && !permFixedA) continue
      if (updates.has(i + 1) && !permFixedB) continue
      const moveA = !permFixedA, moveB = !permFixedB
      const [na, nb] = resolveEdge(a, b, moveA, moveB, hits, obstacles, delta)
      if (moveA) updates.set(i, na)
      if (moveB) updates.set(i + 1, nb)
    }
    if (!dirty) return pts // the scan above just verified every edge clear
    for (const [idx, np] of updates) pts[idx] = np
    for (let i = 2; i < pts.length - 2; i++) {
      const mid = scale3(add3(pts[i - 1]!, pts[i + 1]!), 0.5)
      const cand = add3(pts[i]!, scale3(sub3(mid, pts[i]!), SMOOTH))
      // Guarded smoothing: accept the smoothed position only if it stays
      // clear (or sits in an anchor-exemption ball). Smoothing must never
      // undo the clearance the pushes achieved, or push/smooth cycles
      // forever without a clean scan.
      if (isExempt(cand, exempt, delta) || penetrations(cand, obstacles, delta).length === 0) pts[i] = cand
    }
  }
  throw new Error(`route3: clearance not achieved for ${label} after ${MAX_ROUNDS} rounds`)
}

const chainOf = (pts: Vec3[]): Capsule[] => pts.slice(1).map((b, i) => ({ a: pts[i]!, b, r: 0 }))

export function routeAll(nets: NetIn[], tree: Capsule[], delta: number): Map<WireId, Vec3[][]> {
  const obstacles: Capsule[] = [...tree]
  const out = new Map<WireId, Vec3[][]>()
  for (const net of nets) {
    const curves: Vec3[][] = []
    const ownCaps: Capsule[] = []
    net.edges.forEach((edge, i) => {
      const pts = repair(hermiteSeed(edge, delta), [...obstacles, ...ownCaps], net.exempt, delta, `${net.id}[${i}]`)
      curves.push(pts)
      ownCaps.push(...chainOf(pts))
    })
    out.set(net.id, curves)
    obstacles.push(...ownCaps)
  }
  return out
}
