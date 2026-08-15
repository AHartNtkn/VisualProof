import type { WireId } from '../kernel/diagram/diagram'
import {
  add3, anyPerp, cross3, dist3, dot3, len3, norm3, scale3, segClosest, segPointDist, segSegClosest, segSegDist, sub3, v3, type Vec3,
} from './vec3'

/** `g` names the obstacle GROUP a capsule belongs to (a region line, one
    ring with its spokes, one wire's strands…). Exemption licenses whole
    groups: a ball at an anchor licenses every group that passes through the
    meeting zone — a wire coexists with its own ring, not just with the two
    chords nearest its anchor. */
export type Capsule = { a: Vec3; b: Vec3; r: number; g: string }
export type EdgeIn = { p: Vec3; q: Vec3; tp: Vec3 | null; tq: Vec3 | null }
/** One wire's network to route: `anchors` are its terminal points (with a
    departure tangent or null each), `junctions` its branch vertices —
    positioned by the caller in free space, then CLEARED here against the
    live obstacle set (tree plus every already-routed wire) so nothing
    foreign ever sits inside a junction's meeting zone. `edges` reference
    vertices: index < anchors.length → anchor, else junctions[i-anchors.length]. */
export type NetIn = {
  id: WireId
  anchors: Vec3[]
  tangents: (Vec3 | null)[]
  junctions: Vec3[]
  edges: (readonly [number, number])[]
}

const MAX_ROUNDS = 60
const SMOOTH = 0.4

const capDir = (c: Capsule): Vec3 => {
  const d = sub3(c.b, c.a)
  const l = len3(d)
  return l < 1e-12 ? v3(0, 0, 1) : scale3(d, 1 / l)
}

function penetrations(p: Vec3, obstacles: readonly Capsule[], delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const c of obstacles) if (segPointDist(p, c.a, c.b) < c.r + delta * (1 - 1e-9)) out.push(c)
  return out
}

/** One exemption ball: a meeting point (anchor or junction) plus the set of
    obstacle groups that pass through its meeting zone (within δ) — the
    geometry the wire legitimately touches there. */
export type Ball = { e: Vec3; groups: ReadonlySet<string> }
/** A net's license: its own group (its strands always meet themselves at
    shared vertices) plus its exemption balls. */
export type License = { own: string; balls: readonly Ball[] }

export function groupsNear(e: Vec3, obstacles: readonly Capsule[], delta: number): Set<string> {
  const out = new Set<string>()
  for (const c of obstacles) if (segPointDist(e, c.a, c.b) < c.r + delta) out.add(c.g)
  return out
}

/** Whether a sub-δ approach to capsule `c` at position `at` is licensed:
    `at` lies inside some ball whose licensed groups include `c`'s group
    (or `c` belongs to the net's own strands, which meet it at every shared
    vertex). Licensing is per GROUP, never per capsule — a wire's anchor
    licenses its whole ring, not just the chords nearest the anchor (the
    farther chords of the SAME ring sit at knife-edge distances and would
    otherwise be unroutable strangers) — and foreign geometry that merely
    passes near the ball stays a stranger the curve must clear. */
const licensedHit = (at: Vec3, c: Capsule, lic: License, delta: number): boolean =>
  lic.balls.some((b) => {
    const d = dist3(at, b.e)
    // Own strands meet themselves across the wide ball (edges of one wire
    // share vertices and diverge slowly). Foreign-but-meeting groups are
    // touched only AT the meeting point — a TIGHT ball — so a wire may
    // touch its line or ring at the anchor but never run along it (USER
    // law: a wire is never parallel-and-overlapping with a branch).
    return c.g === lic.own ? d < 2.5 * delta : d < delta && b.groups.has(c.g)
  })

/** An acceptable resting place for a movable sample: every capsule it
    penetrates is licensed at that position. Exemption licenses CLOSENESS —
    it never pins a sample; a sample inside a ball whose edge still has a
    real (unlicensed) violation must remain free to move, or that violation
    can become permanently unclearable. */
const pointOk = (p: Vec3, obstacles: readonly Capsule[], lic: License, delta: number): boolean =>
  penetrations(p, obstacles, delta).every((c) => licensedHit(p, c, lic, delta))

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
function edgeHits(a: Vec3, b: Vec3, obstacles: readonly Capsule[], lic: License, delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const c of obstacles) {
    if (segSegDist(a, b, c.a, c.b) >= c.r + delta * (1 - 1e-9)) continue
    const [onEdge] = segSegClosest(a, b, c.a, c.b)
    if (licensedHit(onEdge, c, lic, delta)) continue
    out.push(c)
  }
  return out
}

/** The 26 unit directions of a 3×3×3 stencil — a fixed, deterministic
    direction set for local escape searches. */
const ESCAPE_DIRS: readonly Vec3[] = (() => {
  const dirs: Vec3[] = []
  for (const x of [-1, 0, 1]) for (const y of [-1, 0, 1]) for (const z of [-1, 0, 1]) {
    if (x === 0 && y === 0 && z === 0) continue
    dirs.push(norm3(v3(x, y, z)))
  }
  return dirs
})()

/** Deterministic LOCAL-FIRST escape: scan candidates on expanding shells
    (radius j·δ/2 over the fixed direction stencil) and take the first
    acceptable position — the nearest usable spot. A 1-D march along a
    single axis is wrong here: in a crowded zone its first clear point can
    be tens of units away, flinging junctions and samples into space
    (measured: a standoff junction thrown ~100 units, exploding its leaf
    edge). */
function escapeNear(p: Vec3, obstacles: readonly Capsule[], lic: License, delta: number): Vec3 {
  for (let j = 1; j <= 400; j++) {
    for (const dir of ESCAPE_DIRS) {
      const cand = add3(p, scale3(dir, j * (delta / 2)))
      if (pointOk(cand, obstacles, lic, delta)) return cand
    }
  }
  throw new Error('route3: no escape position cleared the obstacle set')
}

function pushOut(p: Vec3, hits: Capsule[], obstacles: readonly Capsule[], lic: License, delta: number): Vec3 {
  if (hits.length === 1) {
    const c = hits[0]!
    const closest = segClosest(p, c.a, c.b)
    const radial = sub3(p, closest)
    const dir = len3(radial) < 1e-9 ? anyPerp(capDir(c)) : norm3(radial)
    const cand = add3(closest, scale3(dir, c.r + delta * (1 + 1e-3)))
    if (pointOk(cand, obstacles, lic, delta)) return cand
  }
  return escapeNear(p, obstacles, lic, delta)
}

/** Push a point out of the obstacle set until every remaining penetration
    is licensed (usually: none). `exempt` points license the groups passing
    through their meeting zones, as in routing. */
export function clearPoint(p: Vec3, obstacles: Capsule[], exempt: Vec3[], delta: number): Vec3 {
  const lic: License = { own: '', balls: exempt.map((e) => ({ e, groups: groupsNear(e, obstacles, delta) })) }
  if (pointOk(p, obstacles, lic, delta)) return p
  return pushOut(p, penetrations(p, obstacles, delta), obstacles, lic, delta)
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

/** March both movable endpoints in lockstep along ±dir (`delta/2` steps,
    mirroring `escape`) from their CURRENT positions — not from a shared
    anchor — so nearby samples needing the same escape stay separated along
    the curve instead of collapsing onto one point. Returns the first
    position `accept` blesses, or null when 400 steps never satisfy it. */
function marchEdge(
  a: Vec3, b: Vec3, moveA: boolean, moveB: boolean, dir: Vec3, delta: number,
  accept: (na: Vec3, nb: Vec3) => boolean,
): [Vec3, Vec3] | null {
  for (let j = 1; j <= 400; j++) {
    for (const sign of [1, -1]) {
      const na = moveA ? add3(a, scale3(dir, sign * j * (delta / 2))) : a
      const nb = moveB ? add3(b, scale3(dir, sign * j * (delta / 2))) : b
      if (accept(na, nb)) return [na, nb]
    }
  }
  return null
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
    generous bound; the caller falls back to its transverse marches. Only
    targets `c`; the caller verifies the pose against the full set. */
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
/** Resolve a penetrating edge. The PRIMARY goal is a pose where the edge is
    fully clear (no edgeHits at all, movable endpoints acceptable): radial
    scaling first when the worst capsule allows it, then transverse marches
    along the escape direction of EVERY hit in turn — resolving only the
    single worst capsule ping-pongs forever when clearing one obstacle
    re-violates another (measured: a two-state limit cycle under 3
    simultaneous hits). Only when no direction reaches a fully clear pose
    does it fall back to single-worst-capsule progress, leaving the rest for
    later rounds; the round cap stays the loud backstop. */
function resolveEdge(
  a: Vec3, b: Vec3, moveA: boolean, moveB: boolean, hits: readonly Capsule[],
  obstacles: readonly Capsule[], lic: License, delta: number,
): [Vec3, Vec3] {
  let worst = hits[0]!
  let worstD = segSegDist(a, b, worst.a, worst.b)
  for (const c of hits) {
    const d = segSegDist(a, b, c.a, c.b)
    if (d < worstD) { worstD = d; worst = c }
  }
  const endsOk = (na: Vec3, nb: Vec3): boolean =>
    (!moveA || pointOk(na, obstacles, lic, delta)) && (!moveB || pointOk(nb, obstacles, lic, delta))
  const fullyClear = (na: Vec3, nb: Vec3): boolean =>
    edgeHits(na, nb, obstacles, lic, delta).length === 0 && endsOk(na, nb)

  if (!straddles(a, b, worst)) {
    const scaled = tryScaleEdgeAcross(a, b, moveA, moveB, worst, delta)
    if (scaled !== null && fullyClear(scaled[0], scaled[1])) return scaled
  }
  // Transverse escape directions: cross of each hit's axis with the edge —
  // the direction that breaks a coplanar/threading crossing with THAT
  // capsule by leaving their shared plane — then a deterministic
  // perpendicular of the worst axis as the degenerate-case fallback.
  const rawEdge = sub3(b, a)
  const edgeDir = len3(rawEdge) < 1e-12 ? null : norm3(rawEdge)
  const dirs: Vec3[] = []
  for (const c of [worst, ...hits.filter((h) => h !== worst)]) {
    const cr = edgeDir === null ? v3(0, 0, 0) : cross3(capDir(c), edgeDir)
    if (len3(cr) > 1e-6) dirs.push(norm3(cr))
  }
  dirs.push(anyPerp(capDir(worst)))
  for (const dir of dirs) {
    const clear = marchEdge(a, b, moveA, moveB, dir, delta, fullyClear)
    if (clear !== null) return clear
  }
  // The fallback accepts at EXACTLY the scan's violation threshold — an
  // inflated target creates a dead band: an obstacle can legally rest just
  // past the violation threshold from a FIXED endpoint (measured: 0.30004
  // vs a 0.3003 target), making any edge from that endpoint permanently
  // unable to reach the inflated target even though the scan would already
  // call it clear.
  const target = worst.r + delta * (1 - 1e-9)
  for (const dir of dirs) {
    const progress = marchEdge(a, b, moveA, moveB, dir, delta, (na, nb) =>
      segSegDist(na, nb, worst.a, worst.b) >= target && endsOk(na, nb))
    if (progress !== null) return progress
  }
  throw new Error(`route3: no transverse escape cleared the edge a=${JSON.stringify(a)} b=${JSON.stringify(b)} moveA=${moveA} moveB=${moveB} worst=${JSON.stringify(worst)} dWorst=${worstD.toFixed(4)} distA=${segPointDist(a, worst.a, worst.b).toFixed(4)} distB=${segPointDist(b, worst.a, worst.b).toFixed(4)} hits=${hits.length}`)
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

function repair(seed: Vec3[], obstacles: readonly Capsule[], lic: License, delta: number, label: string): Vec3[] {
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
      const hits = edgeHits(a, b, obstacles, lic, delta)
      if (hits.length === 0) continue
      dirty = true
      // Only the true terminals (index 0 / n) are pinned — exemption
      // licenses closeness, it never pins (a ball-side sample pinned next
      // to a real violation makes that violation permanently unclearable).
      // A sample already claimed by an earlier edge THIS round is
      // different: it WILL move, just via that other edge's own
      // computation — solving this edge as if it were permanently pinned
      // there is wrong (it can manufacture an impossible constraint, or
      // waste motion on the other end for a position that is about to
      // change). Defer to next round, once the claim has been applied.
      const permFixed = (idx: number): boolean => idx === 0 || idx === snapshot.length - 1
      const permFixedA = permFixed(i), permFixedB = permFixed(i + 1)
      if (permFixedA && permFixedB) continue // truly unroutable here; the round cap throws if it never resolves elsewhere
      if (updates.has(i) && !permFixedA) continue
      if (updates.has(i + 1) && !permFixedB) continue
      const moveA = !permFixedA, moveB = !permFixedB
      const [na, nb] = resolveEdge(a, b, moveA, moveB, hits, obstacles, lic, delta)
      if (moveA) updates.set(i, na)
      if (moveB) updates.set(i + 1, nb)
    }
    if (!dirty) return beautify(pts, obstacles, lic, delta) // the scan above just verified every edge clear
    for (const [idx, np] of updates) pts[idx] = np
    for (let i = 2; i < pts.length - 2; i++) {
      const mid = scale3(add3(pts[i - 1]!, pts[i + 1]!), 0.5)
      const cand = add3(pts[i]!, scale3(sub3(mid, pts[i]!), SMOOTH))
      // Guarded smoothing must guard the SAME invariant the scan enforces —
      // EDGE clearance, not point clearance. A point-clear position can
      // still drag its two edges back under the clearance target, undoing
      // each round's resolution by exactly the amount it achieved (measured:
      // a 0.01-per-round limit cycle at the target boundary). Accept the
      // smoothed position only if both edges it participates in stay clear
      // of every capsule outside the exemption balls.
      if (edgeHits(pts[i - 1]!, cand, obstacles, lic, delta).length === 0
        && edgeHits(cand, pts[i + 1]!, obstacles, lic, delta).length === 0) pts[i] = cand
    }
  }
  throw new Error(`route3: clearance not achieved for ${label} after ${MAX_ROUNDS} rounds`)
}

/** Subdivide a waypoint path to ~delta/2 sample spacing (points on a
    straight leg inherit its clearance). */
function densifyWaypoints(way: readonly Vec3[], delta: number): Vec3[] {
  const out: Vec3[] = [way[0]!]
  for (let k = 1; k < way.length; k++) {
    const a = way[k - 1]!, b = way[k]!
    const pieces = Math.max(1, Math.ceil(dist3(a, b) / (delta / 2)))
    for (let t = 1; t <= pieces; t++) out.push(lerpPt(a, b, t / pieces))
  }
  return out
}

/** Shortest-detour seed: resolve a blocked chord by recursively inserting a
    via point beside the WORST blocking capsule, trying both perpendicular
    sides (and both transverse directions) ordered by resulting path length.
    The side of an obstacle is thereby chosen by LENGTH, never by an escape
    step's accident — a wire no longer wraps a branch it could pass beside
    (the measured 1.3π spiral) or keeps a detour class it was flung into
    (the measured 9.5-unit jut); the repair loop only verifies and fixes
    residual interactions afterwards. Deterministic: fixed candidate order,
    fixed call budget; null on exhaustion (caller falls back to the chord). */
function viaSeed(
  p: Vec3, q: Vec3, obstacles: readonly Capsule[], lic: License, delta: number,
  budget: { calls: number }, depth: number,
): Vec3[] | null {
  if (budget.calls-- <= 0 || depth <= 0) return null
  const hits = edgeHits(p, q, obstacles, lic, delta)
  if (hits.length === 0) return [p, q]
  let worst = hits[0]!
  let worstD = segSegDist(p, q, worst.a, worst.b)
  for (const c of hits) {
    const d = segSegDist(p, q, c.a, c.b)
    if (d < worstD) { worstD = d; worst = c }
  }
  const [onEdge, onCap] = segSegClosest(p, q, worst.a, worst.b)
  const axis = capDir(worst)
  const radialRaw = sub3(onEdge, onCap)
  const radialPerp = sub3(radialRaw, scale3(axis, dot3(radialRaw, axis)))
  const r1 = len3(radialPerp) > 1e-9 ? norm3(radialPerp) : anyPerp(axis)
  const r2 = norm3(cross3(axis, r1))
  const standoff = worst.r + 2 * delta
  const vias = [r1, scale3(r1, -1), r2, scale3(r2, -1)]
    .map((dir) => add3(onCap, scale3(dir, standoff)))
    .filter((via) => pointOk(via, obstacles, lic, delta))
    .sort((a, b) => dist3(p, a) + dist3(a, q) - (dist3(p, b) + dist3(b, q)))
  for (const via of vias) {
    const left = viaSeed(p, via, obstacles, lic, delta, budget, depth - 1)
    if (left === null) continue
    const right = viaSeed(via, q, obstacles, lic, delta, budget, depth - 1)
    if (right === null) continue
    return [...left, ...right.slice(1)]
  }
  return null
}

/** Repair output is CLEAR but carries its history — every push, march, and
    scale survives as spikes, zigzags, and obstacle-hugging wander. The
    drawn curve should instead read as the design's "distortion applied to
    a straight line": beautify pulls the path TAUT (replace subpaths with
    verified-clear chords), re-densifies, then ROUNDS corners with
    clearance-verified smoothing to a fixpoint. Every accepted move is
    verified against the same edge invariant the repair scan enforces, so
    beautification can never spend the clearance the repair earned. The
    first and last samples' segments are left untouched to preserve the
    anchors' departure tangents. */
function beautify(pts: Vec3[], obstacles: readonly Capsule[], lic: License, delta: number): Vec3[] {
  if (pts.length < 4) return pts
  // 1) Taut: from each kept vertex, probe the farthest reachable sample by
  //    halving (log probes; a missed longer shortcut is cosmetic, never a
  //    correctness issue) and jump to it when the chord is verified clear.
  const last = pts.length - 1
  const taut: Vec3[] = [pts[0]!, pts[1]!]
  let i = 1
  while (i < last - 1) {
    let j = last - 1
    while (j > i + 1 && edgeHits(pts[i]!, pts[j]!, obstacles, lic, delta).length !== 0) {
      j = i + Math.floor((j - i) / 2)
    }
    taut.push(pts[j]!)
    i = j
  }
  taut.push(pts[last]!)
  // 2) Densify: subdivide each chord to ~delta/2 spacing (points on a clear
  //    chord stay clear), giving the rounding pass room to bend.
  const dense = densifyWaypoints(taut, delta)
  // 3) Round: guarded smoothing to a movement fixpoint. Purely cosmetic —
  //    each accepted move is edge-verified, so stopping at the round cap
  //    leaves a fully valid (just less smooth) curve; no throw needed.
  for (let round = 0; round < 200; round++) {
    let moved = 0
    for (let k = 2; k < dense.length - 2; k++) {
      const mid = scale3(add3(dense[k - 1]!, dense[k + 1]!), 0.5)
      const cand = add3(dense[k]!, scale3(sub3(mid, dense[k]!), SMOOTH))
      if (edgeHits(dense[k - 1]!, cand, obstacles, lic, delta).length === 0
        && edgeHits(cand, dense[k + 1]!, obstacles, lic, delta).length === 0) {
        moved = Math.max(moved, dist3(cand, dense[k]!))
        dense[k] = cand
      }
    }
    if (moved < 1e-3 * delta) break
  }
  return dense
}

const lerpPt = (a: Vec3, b: Vec3, t: number): Vec3 =>
  v3(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t, a.z + (b.z - a.z) * t)

const chainOf = (pts: Vec3[], g: string): Capsule[] => pts.slice(1).map((b, i) => ({ a: pts[i]!, b, r: 0, g }))

export function routeAll(nets: NetIn[], tree: Capsule[], delta: number): Map<WireId, Vec3[][]> {
  const obstacles: Capsule[] = [...tree]
  // Every wire's anchors are obstacles from the START: without this, an
  // early wire may legally park within δ of a LATER wire's anchor, making
  // that wire's first edge permanently unresolvable (its fixed endpoint
  // alone sits sub-δ from the stranger). Each anchor capsule carries its
  // owner's group, so the owner itself keeps free access.
  for (const net of nets) for (const a of net.anchors) obstacles.push({ a, b: a, r: 0, g: `w:${net.id}` })
  const out = new Map<WireId, Vec3[][]>()
  for (const net of nets) {
    // Junctions clear against the LIVE obstacle set — the tree plus every
    // wire routed so far — licensed only near this net's own anchors, so a
    // junction's meeting zone ends ≥ δ from all foreign geometry and group
    // licensing cleanly separates "meets here" from "merely nearby".
    const own = `w:${net.id}`
    const junctions = net.junctions.map((j) => clearPoint(j, obstacles, net.anchors, delta))
    const ballPts = [...net.anchors, ...junctions]
    const lic: License = {
      own,
      balls: ballPts.map((e) => ({ e, groups: groupsNear(e, obstacles, delta) })),
    }
    const posOf = (v: number): Vec3 =>
      v < net.anchors.length ? net.anchors[v]! : junctions[v - net.anchors.length]!
    const tanOf = (v: number): Vec3 | null =>
      v < net.anchors.length ? net.tangents[v]! : null
    const curves: Vec3[][] = []
    const ownCaps: Capsule[] = []
    net.edges.forEach(([u, w], i) => {
      const edge: EdgeIn = { p: posOf(u), q: posOf(w), tp: tanOf(u), tq: tanOf(w) }
      const live = [...obstacles, ...ownCaps]
      // Tangent-free edges (junction-to-junction spans) seed on the
      // shortest-detour via path so their homotopy class is length-chosen;
      // tangent-carrying edges (the short anchor stubs) keep the Hermite
      // seed that honors their departure direction.
      const seed = edge.tp === null && edge.tq === null
        ? densifyWaypoints(viaSeed(edge.p, edge.q, live, lic, delta, { calls: 200 }, 10) ?? [edge.p, edge.q], delta)
        : hermiteSeed(edge, delta)
      const pts = repair(seed, live, lic, delta, `${net.id}[${i}]`)
      curves.push(pts)
      ownCaps.push(...chainOf(pts, own))
    })
    out.set(net.id, curves)
    obstacles.push(...ownCaps)
  }
  return out
}
