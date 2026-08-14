import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, RegionCircle, StoredFrame, WireSpaces, WireView } from './engine'
import { DISC_R, mkEngine, subtreeCarriers, worldBindAnchor, wireTerminalPoints, wireTerminalBCs, drawnObstacles, routeBounds, wireRouteSpaces, frameSlots, FRAME_MARGIN, isBodyObstacle } from './engine'
import { mkFreeSpace, route } from './route/freespace'
import type { Disc as RouteDisc, Bounds, FreeSpace } from './route/freespace'
import { advanceNetwork, netEval, solveTarget, FD_PROBE } from './route/network'
import type { WireNet } from './route/network'
import type { CurveBC, NearSpace } from './route/curve'
import { chainThroughAnchors, curveEnergy, sampleCubics, segNearness, solveEdgeCurve } from './route/curve'
import { layoutScore } from './optimize'
import { mkScoreState, applyMove } from './score-delta'
import type { ScoreState } from './score-delta'
import type { LayoutBest } from './optimize'
// The presentation approach and the drag share ONE semantic frontier, so the
// two modules reference each other. The import cycle is inert: neither module
// evaluates anything of the other's at load time (both are definitions only,
// every cross-reference happens inside a call).
import { commitBodyPositions, projectDragToSemanticFrontier } from './constraints'

/** Live-build marker for serving-path verification (2026-07-23). */
export const PHYSICS_REV = 'hobby-anneal@2026-07-25'
console.info('[physics] rev', PHYSICS_REV)

/** LIVE-TUNABLE wire ENERGY parameters (plan 22, promoted from the accepted
    round-10 demo's `P`). The leg's own tension/bend live in ELASTICA (the
    solver reads them); these are the terms beyond the leg — node clearance,
    wire↔wire separation, junction spread, ∃-tip standoff — plus the trust
    region. Wire↔node collision has NO semantic meaning (USER): through-disc
    travel is a soft surcharge in the routed metric, never a ban. */
export const WIREP = {
  /** wire↔wire separation slope (transverse crossings cheap, co-running dear) */
  sepSlope: 1.4,
  /** wire↔wire separation radius */
  sepR: 5,
  /** POSITION locality budget (continuity law): the max per-tick POSITION motion
      of any DOF — both the synchronous descent's position step (operatorStep) and
      the live layout's approach toward a searched best (approachStep). Rotation is
      NOT bound by this: the descent turns a node up to π per tick (USER
      2026-07-25), since global positional reconfiguration is the search layer's
      job but a node's orientation is a purely local DOF. */
  travelCap: 0.55,
}

/**
 * STRICT TOTAL-ENERGY DESCENT relaxation for the render engine (plan 23, the
 * USER's ruling "the system does not change if it doesn't lower energy"). ONE
 * energy over ALL state — the wires (`wireEnergy`) plus the content (`sibling
 * spacing + scope-ring, `contentEnergy`) — and ONE mover: a strictly E-gated
 * per-DOF coordinate step (the `descentDofs` sweep + the global-rotation DOF). No velocity,
 * no force accumulator, no per-tick projection, no zero-mode quotient — so a
 * limit cycle is impossible by theorem and total E is monotone non-increasing at
 * rest. Regions are true minimal enclosing circles recomputed as bodies move, so
 * containment is derived; the uncapped sibling barrier keeps sibling circles
 * disjoint. `settleStep` advances one tick (live app use); `settle` runs a budget
 * then applies the discrete-event legality projection.
 */

/** Natural (scale-1) region padding beyond the minimal enclosing circle. */
export const REGION_PAD = 5
/** Minimum gap enforced between sibling discs/regions by overlap projection. */
export const SIB_GAP = 5 // structural fallback; live value is PACE.sibGap

// Relaxation coefficients. Not correctness heuristics: any positive values give
// a valid equilibrium of the same constraint system; they tune visual pacing.
// LIVE-TUNABLE (the feel levers — ui-lab/tune.html); defaults are what the
// pinned batteries were derived against.
export const PACE = {
  /** body integrator timestep */
  dt: 0.06,
  /** body damping (higher = syrupier) */
  damp: 4,
  /** content soft-force scale (sibling anchoring strength derives from it) */
  softScale: 18,
  /** content barrier stiffness */
  rep: 900,
  /** sibling gap (spacing between discs/regions) */
  sibGap: 5,
  /** rotation responsiveness divisor (higher = slower turning) */
  rotDrag: 1,
}
/** The soft-force bound: every SOFT pull (sibling attraction, leg-spring
    tension) saturates at this one magnitude — the old linear cohesion
    evaluated at one leg rest-length (0.65·PACE.softScale), no new scale. An unbounded
    soft force can outpull every bounded one and drive a permanent conveyor:
    a leg spring stretched across a region ring (its geometric length must
    exceed the rest length) would otherwise drag body + enclosing circle +
    junction across the sheet forever — minimal enclosing circles exert no
    inward wall, so only the sibling attraction anchors content, and it can
    hold precisely because nothing soft can exceed it. */
const SOFT_MAX = (): number => 0.65 * PACE.softScale
/** The rest INTERVAL for sibling gaps: no force at all between REST_LO() and
    REST_HI(). The interval's width (3·PACE.sibGap) is the noise budget — derived
    circle geometry breathes well under one unit at rest, so content parked
    mid-zone is never re-excited from either edge. */
const REST_LO = (sc: number): number => 2 * PACE.sibGap * sc
const REST_HI = (sc: number): number => 4 * PACE.sibGap * sc
/** Per-call sweep budget for the construction-time legality projection. */
const PROJECTION_PASSES = 60

type Disc = { readonly c: Vec2; readonly r: number; readonly mid?: string; readonly sub?: RegionId }

/** Exact enclosing circle of two discs (the bigger one if it contains the other). */
function mec2(a: Disc, b: Disc): { center: Vec2; radius: number } | null {
  const dx = b.c.x - a.c.x, dy = b.c.y - a.c.y
  const d = Math.hypot(dx, dy)
  if (d + b.r <= a.r) return { center: { x: a.c.x, y: a.c.y }, radius: a.r }
  if (d + a.r <= b.r) return { center: { x: b.c.x, y: b.c.y }, radius: b.r }
  const R = (d + a.r + b.r) / 2
  const t = (R - a.r) / d
  return { center: { x: a.c.x + dx * t, y: a.c.y + dy * t }, radius: R }
}

/** Exact circle enclosing three discs and tangent to all (Apollonius):
    |c − cᵢ| = R − rᵢ. Subtracting pairs gives two equations linear in
    (cx, cy, R); solving them expresses c = p + R·q, and substituting back
    yields a quadratic in R. Returns null on degeneracy (caller falls back). */
function mec3(a: Disc, b: Disc, cD: Disc): { center: Vec2; radius: number } | null {
  const rows = [
    [2 * (b.c.x - a.c.x), 2 * (b.c.y - a.c.y), -2 * (b.r - a.r),
      b.c.x ** 2 - a.c.x ** 2 + b.c.y ** 2 - a.c.y ** 2 - (b.r ** 2 - a.r ** 2)],
    [2 * (cD.c.x - a.c.x), 2 * (cD.c.y - a.c.y), -2 * (cD.r - a.r),
      cD.c.x ** 2 - a.c.x ** 2 + cD.c.y ** 2 - a.c.y ** 2 - (cD.r ** 2 - a.r ** 2)],
  ] as const
  // solve [m00 m01; m10 m11]·c = rhs − R·(k0; k1)  →  c = p + R·q
  const det = rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0]
  if (Math.abs(det) < 1e-12) return null
  const px = (rows[0][3] * rows[1][1] - rows[0][1] * rows[1][3]) / det
  const py = (rows[0][0] * rows[1][3] - rows[0][3] * rows[1][0]) / det
  const qx = (-rows[0][2] * rows[1][1] + rows[0][1] * rows[1][2]) / det
  const qy = (-rows[0][0] * rows[1][2] + rows[0][2] * rows[1][0]) / det
  // |p + R·q − c_a|² = (R − r_a)²
  const ex = px - a.c.x, ey = py - a.c.y
  const A = qx * qx + qy * qy - 1
  const B = 2 * (ex * qx + ey * qy) + 2 * a.r
  const C = ex * ex + ey * ey - a.r * a.r
  let R: number | null = null
  if (Math.abs(A) < 1e-12) {
    if (Math.abs(B) < 1e-12) return null
    R = -C / B
  } else {
    const disc = B * B - 4 * A * C
    if (disc < 0) return null
    const s = Math.sqrt(disc)
    for (const cand of [(-B - s) / (2 * A), (-B + s) / (2 * A)]) {
      if (cand >= Math.max(a.r, b.r, cD.r) - 1e-9 && (R === null || cand < R)) R = cand
    }
  }
  if (R === null || !Number.isFinite(R)) return null
  return { center: { x: px + R * qx, y: py + R * qy }, radius: R }
}

/** Exact-terminating minimal enclosing circle of discs: a coarse subgradient
    descent locates the support region, then the 1/2/3 farthest discs are
    solved in closed form and verified against every disc. Exactness matters
    dynamically, not just geometrically: a capped iterative solve leaves
    unit-scale wobble on LARGE regions (its final steps still move several
    units), and that wobble re-excites gap-resting content every tick — the
    drawing shimmers forever. Falls back to the coarse result if refinement
    degenerates. */
function minimalEnclosingCircle(discs: readonly Disc[]): { center: Vec2; radius: number; support: Disc[] } {
  const center = { x: 0, y: 0 }
  for (const m of discs) { center.x += m.c.x; center.y += m.c.y }
  center.x /= discs.length
  center.y /= discs.length
  for (let it = 0; it < 80; it++) {
    let worst = discs[0]!, worstV = -Infinity
    for (const m of discs) {
      const vv = Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r
      if (vv > worstV) { worstV = vv; worst = m }
    }
    const dx = worst.c.x - center.x, dy = worst.c.y - center.y
    const dd = Math.hypot(dx, dy)
    if (dd < 0.02) break
    const step = Math.min(dd, worstV * 0.6 / (it + 2))
    center.x += (dx / dd) * step
    center.y += (dy / dd) * step
  }
  let radius = 0
  for (const m of discs) radius = Math.max(radius, Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r)
  const coarse = { center, radius }
  // support refinement: the three discs deepest against the coarse circle
  const byDepth = [...discs].sort((m, n) =>
    (Math.hypot(n.c.x - center.x, n.c.y - center.y) + n.r) - (Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r))
  const encloses = (g: { center: Vec2; radius: number }): boolean =>
    discs.every((m) => Math.hypot(m.c.x - g.center.x, m.c.y - g.center.y) + m.r <= g.radius + 1e-6)
  const cands: ({ center: Vec2; radius: number } | null)[] = [
    { center: { x: byDepth[0]!.c.x, y: byDepth[0]!.c.y }, radius: byDepth[0]!.r },
  ]
  if (byDepth.length >= 2) cands.push(mec2(byDepth[0]!, byDepth[1]!))
  if (byDepth.length >= 3) {
    cands.push(mec2(byDepth[0]!, byDepth[2]!), mec2(byDepth[1]!, byDepth[2]!), mec3(byDepth[0]!, byDepth[1]!, byDepth[2]!))
  }
  let best = coarse
  for (const g of cands) {
    if (g !== null && g.radius < best.radius && encloses(g)) best = g
  }
  // support = the discs on the rim of the final circle: the only content
  // whose position the circle actually depends on
  const support = discs.filter((m) => Math.hypot(m.c.x - best.center.x, m.c.y - best.center.y) + m.r >= best.radius - 1e-4)
  return { ...best, support: support.length > 0 ? support : [...discs] }
}

/** The ONE definition of a region's circle: the minimal enclosing circle of its
    direct member discs and its child circles (each inflated by the nesting pad),
    padded and floored at the empty-region radius. Region circles are DERIVED,
    never stored state, so the derivation is parameterized by where the content
    IS — the live body positions (`recomputeRegions`) or a candidate pose set
    (`regionCirclesAt`) — and by the child circles derived under that same
    lookup. */
function deriveRegionCircle(
  e: Engine,
  rid: RegionId,
  posOf: (mid: string) => Vec2,
  circleOf: (child: RegionId) => RegionCircle,
): RegionCircle {
  const discs: Disc[] = []
  for (const mid of e.membersOf.get(rid)!) discs.push({ c: posOf(mid), r: e.bodies.get(mid)!.discR * e.scale, mid })
  for (const c of e.childrenOf.get(rid)!) {
    const g = circleOf(c)
    discs.push({ c: g.center, r: g.radius + REGION_PAD * 0.8 * e.scale, sub: c })
  }
  // only a contentless sheet reaches here (empty leaf regions carry an anchor body)
  if (discs.length === 0) return { center: { x: 0, y: 0 }, radius: 10 * e.scale, support: [] }
  const mec = minimalEnclosingCircle(discs)
  return {
    center: mec.center,
    radius: Math.max(mec.radius + REGION_PAD * e.scale, 10 * e.scale),
    support: mec.support.map((m) => (m.mid !== undefined ? { mid: m.mid } : { sub: m.sub! })),
  }
}

/** The region circles a candidate pose set WOULD produce, derived bottom-up
    without touching live state. */
function regionCirclesAt(e: Engine, posOf: (mid: string) => Vec2): Map<RegionId, RegionCircle> {
  const out = new Map<RegionId, RegionCircle>()
  const visit = (rid: RegionId): void => {
    for (const c of e.childrenOf.get(rid)!) visit(c)
    out.set(rid, deriveRegionCircle(e, rid, posOf, (c) => out.get(c)!))
  }
  visit(e.d.root)
  return out
}

export function recomputeRegions(e: Engine, dirty: ReadonlySet<RegionId> | null = null): void {
  const order: RegionId[] = []
  const visit = (rid: RegionId): void => { for (const c of e.childrenOf.get(rid)!) visit(c); order.push(rid) }
  visit(e.d.root)
  // a circle depends on its descendants only, so a dirty region invalidates
  // itself and its ancestors; everything else keeps its converged circle
  let affected: Set<RegionId> | null = null
  if (dirty !== null) {
    affected = new Set()
    const parentOf = new Map<RegionId, RegionId>()
    for (const [pid, kids] of e.childrenOf) for (const c of kids) parentOf.set(c, pid)
    for (const rid of dirty) {
      let cur: RegionId | undefined = rid
      while (cur !== undefined && !affected.has(cur)) { affected.add(cur); cur = parentOf.get(cur) }
    }
  }
  for (const rid of order) {
    if (affected !== null && !affected.has(rid)) continue
    e.regions.set(rid, deriveRegionCircle(e, rid, (mid) => e.bodies.get(mid)!.pos, (c) => e.regions.get(c)!))
  }
}

/** Establish the fixed near-square proof frame from the current content extent
    (plan 24, USER RULING 2026-07-06). A DISCRETE-EVENT write at first SPAWN only
    (after the leading construction projection makes the seed legal); it no-ops once
    a frame exists, so the box is established ONCE for the diagram's LIFETIME and a
    rewrite (which carries the SAME frame via carryOver) never resizes it — content
    reflows inside the unchanged border. The box is centered on the content bounding
    box and
    sized to the LARGER content half-extent + margin (near-square: all four
    boundaries on equal footing, a wide proof gets a bigger square, never a
    letterbox), tighter than the old enclosing-CIRCLE-derived box. Excludes the
    root sheet circle (which encloses everything — using it would re-inflate the
    box to the circle's corners, the "way too spaced out" the reset rejected) and
    the boundary exit terminals (`e:`, which ride ON the frame). Reads live region
    circles, so the caller must recomputeRegions first (settle / settleStep /
    seedProject do). */
/** Bounding box of an engine's CONTENT (node/junction discs + region circles,
    excluding the root sheet and boundary exit terminals) — the extent the frame is
    sized to. Null if there is no content. Reads live region circles (recompute
    first). */
function contentBBox(e: Engine): { minX: number; minY: number; maxX: number; maxY: number } | null {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
  const grow = (x: number, y: number, r: number): void => {
    if (x - r < minX) minX = x - r
    if (y - r < minY) minY = y - r
    if (x + r > maxX) maxX = x + r
    if (y + r > maxY) maxY = y + r
  }
  for (const b of e.bodies.values()) {
    if (b.id.startsWith('e:')) continue
    grow(b.pos.x, b.pos.y, b.discR * e.scale)
  }
  for (const [rid, g] of e.regions) {
    if (rid === e.d.root) continue
    grow(g.center.x, g.center.y, g.radius)
  }
  return Number.isFinite(minX) ? { minX, minY, maxX, maxY } : null
}

export function establishFrame(e: Engine): void {
  // The border is established ONCE and NEVER resizes for the diagram's lifetime
  // (USER RULING 2026-07-06 — supersedes "recalculated at rewrite"): a rewrite
  // carries the SAME frame (carryOver), so an already-set frame is kept and content
  // reflows inside it. Only a fresh engine with no carried frame establishes one.
  if (e.frame !== null) return
  const bb = contentBBox(e)
  if (bb === null) { e.frame = { center: { x: 0, y: 0 }, half: 10 + FRAME_MARGIN }; return }
  const cx = (bb.minX + bb.maxX) / 2, cy = (bb.minY + bb.maxY) / 2
  const half = Math.max((bb.maxX - bb.minX) / 2, (bb.maxY - bb.minY) / 2) + FRAME_MARGIN
  e.frame = { center: { x: cx, y: cy }, half }
}

/** Establish the fixed border for a REPLAY from the PROOF-WIDE max content extent
    (USER RULING 2026-07-06, option (a)): a replay's "contents" are ALL its steps —
    known at spawn — so one absolute border sized to the largest step fits EVERY step
    and never varies. The extent of each step is measured on its construction-
    projected seed (mkEngine → recomputeRegions → resolveOverlaps), NOT a full settle:
    a whole-proof scan is then ~150 ms (measured, plusComm's 65 steps), and the
    projected extent SAFELY over-bounds the settled extent at the binding (largest)
    steps (settling COMPACTS them — measured plusComm step 42 proj 402.8 → settled
    340.5), while the only steps whose settled extent exceeds their projection are
    tiny ones far below the max. The border is centered on the largest step's content
    (so it sits centered, not the tiny first step). No-ops if a frame already exists
    (established once, then carried). */
export function establishProofFrame(e: Engine, steps: readonly { diagram: Diagram; boundary: readonly WireId[] }[]): void {
  if (e.frame !== null) return
  let bestHalf = -1, bestCx = 0, bestCy = 0
  for (const s of steps) {
    const se = mkEngine(s.diagram, s.boundary)
    recomputeRegions(se)
    resolveOverlaps(se)
    recomputeRegions(se)
    const bb = contentBBox(se)
    if (bb === null) continue
    const half = Math.max((bb.maxX - bb.minX) / 2, (bb.maxY - bb.minY) / 2)
    if (half > bestHalf) { bestHalf = half; bestCx = (bb.minX + bb.maxX) / 2; bestCy = (bb.minY + bb.maxY) / 2 }
  }
  e.frame = bestHalf < 0
    ? { center: { x: 0, y: 0 }, half: 10 + FRAME_MARGIN }
    : { center: { x: bestCx, y: bestCy }, half: bestHalf + FRAME_MARGIN }
}

/** The PROOF-WIDE boundary slot-shift (plan 24 legibility, USER 2026-07-07): the
    single cyclic wire→slot rotation that minimizes the TOTAL port→slot chord summed
    over EVERY step's construction-projected seed (the same all-steps scan the border
    is sized by). Boundary wire i is assigned slot (i + shift) mod n; only cyclic
    shifts are legal (they preserve the canonical cyclic order — no port ever slips
    past another), and logical port 0's origin marker follows its assigned slot.
    Chosen ONCE at enterReplay and carried
    across the proof, so slots never move or reorder mid-proof. Scale-invariant (a
    rotation of the assignment), so the natural seed suffices. 0 for < 2 boundary
    wires (nothing to align). */
export function establishProofSlotShift(frame: StoredFrame, steps: readonly { diagram: Diagram; boundary: readonly WireId[] }[]): number {
  const n = steps.length > 0 ? steps[0]!.boundary.length : 0
  if (n < 2) return 0
  const fb = { minX: frame.center.x - frame.half, maxX: frame.center.x + frame.half, minY: frame.center.y - frame.half, maxY: frame.center.y + frame.half, frameR: frame.half, center: frame.center }
  const slots = frameSlots(fb, n)
  // per-step boundary-port positions (index by boundary order); null = no bind
  const stepPorts: (Vec2 | null)[][] = []
  for (const s of steps) {
    const se = mkEngine(s.diagram, s.boundary)
    recomputeRegions(se); resolveOverlaps(se)
    stepPorts.push(se.boundary.map((wid) => {
      const w = se.wires.get(wid); const bd = w?.binds[0]
      return bd === undefined ? null : worldBindAnchor(se, se.bodies.get(bd.body)!, bd.key)
    }))
  }
  let bestShift = 0, bestTotal = Infinity
  for (let shift = 0; shift < n; shift++) {
    let total = 0
    for (const ports of stepPorts) {
      for (let i = 0; i < ports.length; i++) {
        const p = ports[i]; if (p === null || p === undefined) continue
        const slot = slots[(i + shift) % n]!
        total += Math.hypot(slot.point.x - p.x, slot.point.y - p.y)
      }
    }
    if (total < bestTotal) { bestTotal = total; bestShift = shift }
  }
  return bestShift
}

/** Clamp a body centre inside the fixed frame's HARD WALL (plan 24, USER RULING:
    the boundary is a HARD edge, not a soft tether). Projects the trial position so
    the whole disc stays within the near-square box — a settling trial or a drag
    target past the edge is pushed back, never accepted past it, and the frame
    never grows to chase it. Boundary exit terminals (`e:`) ride ON the frame and
    are exempt; no frame yet → no wall. */
function clampToFrame(e: Engine, b: Body, p: Vec2): Vec2 {
  const f = e.frame
  if (f === null) return p
  const lim = Math.max(f.half - b.discR * e.scale, 0)
  return {
    x: Math.max(f.center.x - lim, Math.min(f.center.x + lim, p.x)),
    y: Math.max(f.center.y - lim, Math.min(f.center.y + lim, p.y)),
  }
}

/** Pull every content body inside the fixed border, a one-time CONSTRUCTION-EVENT
    projection (plan 24): after a rewrite, carryOver + resolveOverlaps can seed the
    carried content spread PAST the (proof-wide-sized) border, and the seed would flash
    outside for one frame before settling pulls it in. Clamping the seed here removes
    that transient — the content starts inside the border and settles within it (the
    cut barrier + wall keep it there). No-op with no frame. */
export function clampContentToFrame(e: Engine): void {
  if (e.frame === null) return
  for (const b of e.bodies.values()) {
    b.pos = clampToFrame(e, b, b.pos)
  }
  recomputeRegions(e)
}

/** Target fraction of the fixed frame half-extent a step's content should fill
    (plan 24, USER RULING 2026-07-07 "content must be sized to the space available"):
    every step is uniformly scaled in either direction to this same band. Sparse
    content grows and dense content shrinks; the frame itself never participates in
    that sizing decision. Below 1 so content clears the border with a rim of air
    (never pressed against the wall). */
const CONTENT_FILL = 0.82

/** Size THIS step's content to fill the FIXED proof-wide border (plan 24, USER
    RULING 2026-07-07). The border NEVER resizes — the CONTENT does, per rewrite:
    every world-space length of the diagram (disc/anatomy radii, packing gaps, wire
    clearance, drawn geometry) is a uniform multiple `Engine.scale` of its natural
    (scale-1) value, chosen so this step's projected extent reaches CONTENT_FILL of
    the frame. A DISCRETE-EVENT recalc at seed time (allowed by the ruling — sizes
    recalculated after a rewrite), never during settling.

    Runs on a NORMALIZED engine: every body/hub already sits at its NATURAL position
    (carryOver un-scales the carried layout to scale 1), so the natural extent is
    read directly, the fill scale is solved, and the whole layout is scaled about the
    frame centre. Requires an established frame and a recomputeRegions first (seedProject
    does both). No-op with no frame, no content, or a degenerate/non-finite extent. */
export function applyContentScale(e: Engine): void {
  if (e.frame === null) return
  const bb = contentBBox(e) // natural extent (engine is normalized to scale 1 here)
  if (bb === null) return
  const half = Math.max((bb.maxX - bb.minX) / 2, (bb.maxY - bb.minY) / 2)
  if (half < 1e-6) return
  const s = (CONTENT_FILL * e.frame.half) / half
  if (!Number.isFinite(s) || s <= 0) return
  // scale ABOUT the content's own centroid and place that centroid at the frame
  // centre — a small step's natural content sits at its own centre (not the
  // proof-wide frame centre, which was fixed to the LARGEST step), so scaling
  // about the frame centre would fling it off to the wall. Centroid-scale +
  // recentre grows each step in place and centres it in the fixed border.
  const cx = (bb.minX + bb.maxX) / 2, cy = (bb.minY + bb.maxY) / 2
  const fc = e.frame.center
  const map = (p: Vec2): Vec2 => ({ x: fc.x + (p.x - cx) * s, y: fc.y + (p.y - cy) * s })
  for (const b of e.bodies.values()) b.pos = map(b.pos)
  for (const w of e.wires.values()) {
    w.net.junctions = w.net.junctions.map(map)
  }
  e.scale = s
  recomputeRegions(e)
}

/** THE construction-time seed projection for a SINGLE diagram — the one canonical
    pipeline the live app, every render harness, and every settle-based test must
    share (it was copy-pasted across ~10 sites; a change to the order silently left
    the copies validating a layout the app no longer produced). A discrete event,
    not a mover: seed the region circles, separate the dense mkEngine spiral onto
    the feasible set (so the budgeted descent starts LEGAL, not wedged in a
    dense-overlap trap — the plan-23 leading projection), fix the frame, then
    content-fill scale + clamp inside it. Lives here (not in the shell or mkEngine)
    because it calls ONLY relax.ts functions — no circular import. The REPLAY path
    is a variant (establishProofFrame + establishProofSlotShift over all steps);
    see seedProjectReplay. `noScale` skips the content scale for scale-invariant
    measurements (frame box / slots) that must read natural geometry. */
export function seedProject(e: Engine, noScale = false, carriedNets: ReadonlySet<WireId> | null = null): void {
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e)
  if (!noScale) { applyContentScale(e); clampContentToFrame(e) }
  seedWireJunctions(e, carriedNets)
}

/** Junction SPAWN positions are solved, never stale seeds (USER 2026-07-30:
    fresh wires' junctions spawned near the diagram centre — the mkEngine
    centroid of the SEED body layout — and spent the whole opening walking to
    their optimum; the same time can spawn them AT it). A discrete
    construction event like the rest of seedProject: every wire whose net was
    NOT carried from a previous engine gets its fixed-topology target solved
    from the CURRENT terminals. Carried nets keep their glide state untouched
    (re-deriving them would be argmin-tracking of state that must follow its
    basin). */
function seedWireJunctions(e: Engine, carriedNets: ReadonlySet<WireId> | null): void {
  const spaces = wireRouteSpaces(e)
  for (const [wid, w] of e.wires) {
    if (w.net.junctions.length === 0) continue
    if (carriedNets !== null && carriedNets.has(wid)) continue
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    solveTarget(w.net, terms, spaces.space(wid), 60)
  }
}

function shiftSubtree(e: Engine, rid: RegionId, dx: number, dy: number): void {
  // a rigid translation moves the region's circle exactly — keep the stored
  // geometry consistent mid-pass without a recompute
  const g = e.regions.get(rid)
  if (g !== undefined) e.regions.set(rid, { center: { x: g.center.x + dx, y: g.center.y + dy }, radius: g.radius, support: g.support })
  for (const mid of e.membersOf.get(rid)!) {
    const b = e.bodies.get(mid)!
    b.pos = { x: b.pos.x + dx, y: b.pos.y + dy }
  }
  for (const c of e.childrenOf.get(rid)!) shiftSubtree(e, c, dx, dy)
}


export function resolveOverlaps(e: Engine): boolean {
  // CONSTRUCTION-TIME legality projection (plan 23): a purely POSITIONAL
  // projection onto the feasible set (no circle intersects another). It is NOT a
  // per-tick mover — the strict-descent dynamics never calls it inside settleStep
  // (that would move state without lowering energy, the USER law it violated).
  // It runs only as a DISCRETE EVENT: `settle` calls it once after the tick
  // budget to guarantee the at-rest hard law even when an externally constructed
  // (post-rewrite) layout lands overlapping. Every violated sibling pair is
  // separated by a MASS-WEIGHTED positional split (the pair's mutual centroid
  // stays fixed — an equal split between unequal masses would displace the
  // centroid every contact and walk the drawing off the sheet), region geometry
  // is recomputed, and the sweep repeats until legal or the pass budget is spent.
  let any = false
  for (let pass = 0; pass < PROJECTION_PASSES; pass++) {
    let moved = false
    const dirty = new Set<RegionId>()
    for (const rid of e.regions.keys()) {
      const items: { sub: RegionId | null; id: string; r: number }[] = []
      for (const mid of e.membersOf.get(rid)!) {
        items.push({ sub: null, id: mid, r: e.bodies.get(mid)!.discR * e.scale })
      }
      for (const c of e.childrenOf.get(rid)!) {
        items.push({ sub: c, id: c, r: e.regions.get(c)!.radius })
      }
      const centerOf = (it: { sub: RegionId | null; id: string }): Vec2 =>
        it.sub === null ? e.bodies.get(it.id)!.pos : e.regions.get(it.sub)!.center
      for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
        const A = items[i]!, B = items[j]!
        const ca = centerOf(A), cb = centerOf(B)
        const dx = cb.x - ca.x, dy = cb.y - ca.y
        const dist = Math.hypot(dx, dy)
        const need = A.r + B.r + PACE.sibGap * e.scale
        if (dist >= need) continue

        // coincident centers have no separation direction; any fixed unit
        // vector breaks the symmetry deterministically
        const ux = dist < 1e-9 ? 1 : dx / dist, uy = dist < 1e-9 ? 0 : dy / dist
        const viol = need - dist
        const mA = A.sub === null ? 1 : subtreeCarriers(e, A.sub).length
        const mB = B.sub === null ? 1 : subtreeCarriers(e, B.sub).length
        const wA = mB / (mA + mB), wB = mA / (mA + mB)
        const shift = (it: typeof A, sx: number, sy: number): void => {
          if (it.sub === null) {
            const b = e.bodies.get(it.id)!
            b.pos = { x: b.pos.x + sx, y: b.pos.y + sy }
            dirty.add(b.region)
          } else {
            shiftSubtree(e, it.sub, sx, sy)
            dirty.add(it.sub)
          }
        }
        shift(A, -ux * viol * wA, -uy * viol * wA)
        shift(B, ux * viol * wB, uy * viol * wB)
        moved = true
      }
    }
    if (!moved) break
    any = true
    recomputeRegions(e, dirty)
  }
  return any
}

// ---- THE wire energy (routed-network model, USER ruling 2026-07-24): the
// soft routed cost + drawn turning + inter-wire separation, identical for the
// node solver, the router's gates, and the global layout score. Junction
// placement and wire topology live in the separate router (src/view/route/),
// which observes nodes and never moves them. ----

/** Number of samples along each segment for the separation quadrature. */
const SEP_N = 8

/** Wire-segment type: a drawn curve segment tagged with its owning wire. */
export type WireSeg = { readonly wid: string; readonly a: Vec2; readonly b: Vec2 }

/** The separation energy of ONE segment pair (bbox-rejected, then the SEP_N²
    sample quadrature) — the numeric kernel of `segSeparationE`. `R` =
    WIREP.sepR·scale. */
function segPairSepE(A: { a: Vec2; b: Vec2 }, B: { a: Vec2; b: Vec2 }, R: number): number {
  if (Math.min(A.a.x, A.b.x) - R > Math.max(B.a.x, B.b.x) || Math.min(B.a.x, B.b.x) - R > Math.max(A.a.x, A.b.x)) return 0
  if (Math.min(A.a.y, A.b.y) - R > Math.max(B.a.y, B.b.y) || Math.min(B.a.y, B.b.y) - R > Math.max(A.a.y, A.b.y)) return 0
  let E = 0
  for (let ki = 0; ki <= SEP_N; ki++) {
    const ta = ki / SEP_N
    const pa = { x: A.a.x + (A.b.x - A.a.x) * ta, y: A.a.y + (A.b.y - A.a.y) * ta }
    for (let kj = 0; kj <= SEP_N; kj++) {
      const tb = kj / SEP_N
      const pb = { x: B.a.x + (B.b.x - B.a.x) * tb, y: B.a.y + (B.b.y - B.a.y) * tb }
      const d = Math.hypot(pa.x - pb.x, pa.y - pb.y)
      if (d < R) E += (WIREP.sepSlope * (R - d) * (R - d)) / R / (SEP_N * SEP_N)
    }
  }
  return E
}

/** Inter-wire separation over straight segments (plan-22 constants):
    co-running pairs pay heavily, transverse crossings pay a little — the
    objective SEES crossings and pointless co-routing.

    EXACT SPATIAL HASH. Two segments contribute 0 unless within R (segPairSepE
    bbox-rejects beyond R), so only pairs whose bboxes are ≤ R apart matter. On a
    uniform grid at cell size R, such a pair's bbox cells are the SAME or ADJACENT
    (a gap < R = one cell), so scanning the 3×3 neighborhood of each segment's
    bbox cells enumerates EXACTLY the contributing superset — no near pair is
    missed, and every far pair (which the all-pairs loop would only bbox-reject to
    0) is skipped. Summed over the near pairs in (i,j) order, this is the SAME sum
    as the all-pairs loop: the nonzero terms are identical and in the same order,
    and the far pairs it drops each added exactly 0. */
/** Pack a grid cell (cx,cy) into one integer key; the +2^25 offset keeps
    negatives non-negative and the 2^26 stride keeps the product a safe integer
    for any scene. */
const SEP_CELL_OFF = 33554432, SEP_CELL_STRIDE = 67108864
const sepCellKey = (cx: number, cy: number): number => (cx + SEP_CELL_OFF) * SEP_CELL_STRIDE + (cy + SEP_CELL_OFF)
type Seg2 = { readonly a: Vec2; readonly b: Vec2 }
/** The [cx0,cx1,cy0,cy1] grid-cell span of a segment's bbox at inverse cell size `inv`. */
const segCellSpan = (s: Seg2, inv: number): [number, number, number, number] => [
  Math.floor(Math.min(s.a.x, s.b.x) * inv), Math.floor(Math.max(s.a.x, s.b.x) * inv),
  Math.floor(Math.min(s.a.y, s.b.y) * inv), Math.floor(Math.max(s.a.y, s.b.y) * inv),
]

/** A drawn-curve sample step is a small fraction of the layout, so its bbox spans
    only a handful of grid cells. A segment whose bbox spans MORE than this many
    cells has a non-physical (huge or non-finite) endpoint — a transient a
    basin-hopping perturbation can produce before the relaxation pulls it back. Such
    a segment is NOT bucketed (bucketing it would allocate cells proportional to its
    area, exhausting the Map); its exact separation is charged via the all-pairs
    fallback instead, keeping the grid's total cell count O(segments). */
const GRID_MAX_CELLS = 1024

/** A uniform spatial hash of segments at cell size R: each ordinary segment's
    indices bucketed into every cell its bbox overlaps (two segments interact only
    within R = one cell, so the 3×3 neighborhood of a segment's cells is the exact
    near-pair superset). Degenerate huge/non-finite segments go to `large` and are
    handled by all-pairs (see GRID_MAX_CELLS). */
type SepGrid = { readonly grid: Map<number, number[]>; readonly large: number[] }
function buildSepGrid(segs: readonly Seg2[], R: number): SepGrid {
  const inv = 1 / R
  const grid = new Map<number, number[]>()
  const large: number[] = []
  for (let i = 0; i < segs.length; i++) {
    const [cx0, cx1, cy0, cy1] = segCellSpan(segs[i]!, inv)
    const cells = (cx1 - cx0 + 1) * (cy1 - cy0 + 1)
    if (!(cells >= 1 && cells <= GRID_MAX_CELLS)) { large.push(i); continue } // huge or non-finite
    for (let cx = cx0; cx <= cx1; cx++) for (let cy = cy0; cy <= cy1; cy++) {
      const b = grid.get(sepCellKey(cx, cy))
      if (b !== undefined) b.push(i); else grid.set(sepCellKey(cx, cy), [i])
    }
  }
  return { grid, large }
}

/** Enumerate every cross-wire near pair (i<j) EXACTLY ONCE, in (i,j) order, over a
    prebuilt grid: candidates come from the 3×3 neighborhood of each segment's cells
    (a pair sharing several cells is emitted several times; the sort+dedup collapses
    it). The (i,j) order makes the summation match the all-pairs loop bit-for-bit —
    the far pairs it never visits each contributed exactly 0. */
function eachNearPair(segs: readonly WireSeg[], sg: SepGrid, R: number, cb: (i: number, j: number) => void): void {
  const n = segs.length, inv = 1 / R
  const isLarge = new Uint8Array(n)
  for (const li of sg.large) isLarge[li] = 1
  const cand: number[] = []
  // ordinary × ordinary: grid neighborhood (a large segment's cell span is huge, so
  // it is never QUERIED here — it is enumerated below).
  for (let i = 0; i < n; i++) {
    if (isLarge[i] === 1) continue
    const A = segs[i]!
    const [cx0, cx1, cy0, cy1] = segCellSpan(A, inv)
    for (let cx = cx0 - 1; cx <= cx1 + 1; cx++) for (let cy = cy0 - 1; cy <= cy1 + 1; cy++) {
      const b = sg.grid.get(sepCellKey(cx, cy))
      if (b === undefined) continue
      for (const j of b) if (j > i && segs[j]!.wid !== A.wid) cand.push(i * n + j)
    }
  }
  // every pair with a large endpoint: all-pairs (large segments are rare — a
  // degenerate transient). large–large counted once (skip j<li when both large).
  for (const li of sg.large) {
    const w = segs[li]!.wid
    for (let j = 0; j < n; j++) {
      if (j === li || (isLarge[j] === 1 && j < li) || segs[j]!.wid === w) continue
      cand.push(Math.min(li, j) * n + Math.max(li, j))
    }
  }
  cand.sort((a, b) => a - b)
  let prev = -1
  for (const pk of cand) {
    if (pk === prev) continue
    prev = pk
    cb(Math.floor(pk / n), pk % n)
  }
}

/** The separation energy BETWEEN two wires' segment sets (no same-wire skip —
    the caller guarantees distinct wires). The incremental delta (score-delta)
    re-evaluates exactly the wire pairs a move touches; this is their exact
    cross contribution. Grid-free all-pairs is exact: segPairSepE is zero
    beyond the separation radius, so the grid total and this sum agree. */
export function segSeparationBetween(segsA: readonly { a: Vec2; b: Vec2 }[], segsB: readonly { a: Vec2; b: Vec2 }[], sc: number): number {
  const R = WIREP.sepR * sc
  let E = 0
  for (const A of segsA) for (const B of segsB) E += segPairSepE(A, B, R)
  return E
}

export function segSeparationE(segs: readonly WireSeg[], sc: number): number {
  const R = WIREP.sepR * sc
  if (segs.length < 2 || !(R > 0)) return 0
  let E = 0
  eachNearPair(segs, buildSepGrid(segs, R), R, (i, j) => { E += segPairSepE(segs[i]!, segs[j]!, R) })
  return E
}

/** THE wire energy: the ROD energy (tension + bending, USER ruling
    2026-07-24 — see route/curve.ts) of every drawn curve, plus the soft
    obstacle/frame surcharges along the samples and the routed inter-wire
    separation. There is exactly ONE wire objective — this one — used
    identically by the node solver, the router's gates, and the global layout
    score. */

/** Bending stiffness: r* = the node-disc scale (bends happen at the scale of
    the objects they route around); beta = r*² × unit tension. Derived, not
    tuned. */
export const rodBeta = (e: Engine): number => (DISC_R * e.scale) ** 2

export function wireEnergy(e: Engine): number {
  return wireEnergyCapture(e).E
}

/** Per-wire nearness spaces (energy-drawn wires): DRAWN node discs + the
    wire's DRAWN forbidden cut circles + the frame, under the ONE clearance
    law (WIREP.sepR/sepSlope — the same falloff wires pay against each
    other). Shares the composed disc arrays per forbidden-set signature. */
export function wireNearSpaces(e: Engine, spaces: WireSpaces): (wid: WireId) => NearSpace {
  const nodes = drawnObstacles(e)
  const bounds = routeBounds(e)
  const R = WIREP.sepR * e.scale
  const slope = WIREP.sepSlope
  const plain: NearSpace = { discs: nodes, bounds, R, slope }
  const bySet = new Map<readonly RouteDisc[], NearSpace>()
  return (wid: WireId): NearSpace => {
    const forb = spaces.forbiddenDrawn.get(wid)
    if (forb === undefined || forb.length === 0) return plain
    let ns = bySet.get(forb)
    if (ns === undefined) {
      ns = { discs: [...nodes, ...forb], bounds, R, slope }
      bySet.set(forb, ns)
    }
    return ns
  }
}

/** Region-circle patch band (drawn units): a probe displaces one coordinate by
    FD_PROBE, and a minimal enclosing circle's centre and radius are each
    1-Lipschitz in a support disc's position, so the circle boundary moves at
    most 2·FD_PROBE; segs farther than that from the capture boundary keep
    their inside/outside status on BOTH sides and contribute exactly zero to
    the surcharge delta. 2× safety margin. */
const PROBE_BAND = 4 * FD_PROBE

/** A routed edge's frozen curve: its SOLVED interior anchors at the captured
    optimum (endpoints re-derived live at probe time; the family chain through
    live endpoints + frozen anchors is the envelope-theorem majorizer). */
export type FrozenEdge = { readonly wid: string; readonly u: number; readonly v: number; readonly anchors: readonly Vec2[] }

/** Exact wire energy PLUS the frozen-path capture the probe evaluator needs and
    the drawn curve segments (the same ones `segSeparationE` sums over). */
export function wireEnergyCapture(e: Engine): { E: number; edges: FrozenEdge[]; segs: WireSeg[] } {
  const spaces = wireRouteSpaces(e)
  const nsOf = wireNearSpaces(e, spaces)
  const beta = rodBeta(e)
  let E = 0
  const edges: FrozenEdge[] = []
  const segs: WireSeg[] = []
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    const fs = spaces.space(wid)
    const ns = nsOf(wid)
    const bcs = wireTerminalBCs(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    for (const [u, v] of w.net.edges) {
      const pu = pos(u), pv = pos(v)
      const r = route(fs, pu, pv)
      const sol = solveEdgeCurve(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, pu, pv, r.hugs, ns, beta)
      E += curveEnergy(sol.pts, ns, beta)
      edges.push({ wid, u, v, anchors: sol.anchors })
      for (let i = 0; i + 1 < sol.pts.length; i++) segs.push({ wid, a: sol.pts[i]!, b: sol.pts[i + 1]! })
    }
  }
  return { E: E + segSeparationE(segs, e.scale), edges, segs }
}

/**
 * ENVELOPE-THEOREM PROBE EVALUATOR: the routed cost is a minimum over paths,
 * so at the captured optimum the frozen-path cost has the same derivative as
 * the true cost wherever the optimal path is unique (envelope theorem); the
 * one-sided slope selection brackets the exceptional kinks. Gradient probes
 * therefore rebuild the drawn curve from the CAPTURED route waypoints — the
 * curve construction is deterministic and cheap; only the routing solve (the
 * visibility precompute dominated probe cost ~19×, measured 2026-07-24) is
 * frozen. Every ACCEPTANCE gate still evaluates the exact routed energy:
 * strict descent is exact; only probe DIRECTIONS use the equal-derivative
 * majorizer.
 */
export function frozenWireEnergy(e: Engine, edges: readonly FrozenEdge[]): number {
  const spaces = wireRouteSpaces(e)
  const nsOf = wireNearSpaces(e, spaces)
  const beta = rodBeta(e)
  let E = 0
  const segs: { wid: string; a: Vec2; b: Vec2 }[] = []
  const perWire = new Map<string, { terms: Vec2[]; bcs: CurveBC[]; junctions: Vec2[]; ns: NearSpace }>()
  for (const fe of edges) {
    let c = perWire.get(fe.wid)
    if (c === undefined) {
      const w = e.wires.get(fe.wid)!
      c = {
        terms: wireTerminalPoints(e, w), bcs: wireTerminalBCs(e, w), junctions: w.net.junctions,
        ns: nsOf(fe.wid),
      }
      perWire.set(fe.wid, c)
    }
    const cc = c
    const pos = (v: number): Vec2 => (v < cc.terms.length ? cc.terms[v]! : cc.junctions[v - cc.terms.length]!)
    const bu = fe.u < cc.bcs.length ? cc.bcs[fe.u]! : null
    const bv = fe.v < cc.bcs.length ? cc.bcs[fe.v]! : null
    // a clamped end's rim anchor REPLACES the terminal point, exactly as the
    // solve's own chain construction does — same anchors ⇒ same curve
    const pts = sampleCubics(chainThroughAnchors(bu, bv, [bu !== null ? bu.p : pos(fe.u), ...fe.anchors, bv !== null ? bv.p : pos(fe.v)]))
    E += curveEnergy(pts, cc.ns, beta)
    for (let i = 0; i + 1 < pts.length; i++) segs.push({ wid: fe.wid, a: pts[i]!, b: pts[i + 1]! })
  }
  return E + segSeparationE(segs, e.scale)
}

// ---- FROZEN-PROBE LOCALITY DELTA (plan Task 8b) ----
// A gradient probe displaces ONE coordinate of ONE body; within the FROZEN model
// (route corridors fixed) that changes frozenWireEnergy in exactly four ways —
// (1) the curves of wires with a terminal on the probed body, (2) every OTHER
// wire's obstacle surcharge, and only through the probed body's ONE moved disc,
// (3) the separation pairs the rebuilt segments touch, (4) content (the caller
// keeps that a full recompute). NO ROUTING is involved — this is arithmetic on
// cached geometry — so it is exact AND ~O(one body's neighborhood), replacing the
// ~114×-per-step full frozenWireEnergy rebuild.

/** One wire's frozen capture: its edges (to rebuild the curve), the [start,end)
    range of its segments in the flat base array, and its base rodCost. */
type FrozenWireCap = { readonly wid: WireId; readonly edges: FrozenEdge[]; readonly segStart: number; readonly segEnd: number; readonly rod: number }

export type FrozenState = {
  readonly segs: WireSeg[]
  readonly segWire: Int32Array
  readonly wires: FrozenWireCap[]
  readonly termWires: Map<string, number[]>
  readonly obstacle: Map<string, RouteDisc>
  /** Per-wire forbidden region ids (shared arrays from wireRouteSpaces). The
      frozen model freezes CORRIDORS only; discs — node AND region — are LIVE,
      so probe directions see the cut-obstacle coupling a body move creates by
      dragging its ancestor circles (without this the probes reported downhill
      where the true energy rose on every cut-heavy trial — measured 100% of
      1360 fallback trials uphill, 2026-07-31). */
  readonly forbiddenRids: ReadonlyMap<WireId, readonly RegionId[]>
  /** Inflated forbidden circles at capture (r = drawn + ROUTE_CLEAR·scale). */
  readonly regionDiscs: Map<RegionId, RouteDisc>
  /** Wire indices whose forbidden set contains each region (patch fan-out). */
  readonly ridWires: Map<RegionId, number[]>
  /** Per region, the cached seg indices within PROBE_BAND of the capture
      circle's boundary — the only segs whose surcharge a probe-scale circle
      change can touch (Lipschitz: |Δcentre|+|Δradius| ≤ 2·FD_PROBE per moved
      support disc, band = 4·FD_PROBE with a 2× margin). Larger displacements
      fall back to the wire's full seg range. */
  readonly ridBandSegs: Map<RegionId, number[]>
  readonly grid: SepGrid
  readonly R: number
  /** Nearness falloff slope (WIREP.sepSlope) — the one clearance law. */
  readonly nearSlope: number
  readonly beta: number
  readonly sc: number
  readonly bounds: Bounds | null
  readonly frozenTotal: number
  /** Per-wire base separation contribution (each cross-wire near pair added to BOTH
      its wires); the probe reads it to skip re-scanning a wire's OLD near pairs. */
  readonly wireSep: Float64Array
  readonly seen: Int32Array
  stamp: number
}

/** Build the frozen state ONCE per operatorStep from a base capture. It IS a full
    exact eval (the routing solve), so it replaces the step's wireEnergyCapture. */
export function mkFrozenState(e: Engine): FrozenState {
  const spaces = wireRouteSpaces(e)
  const nsOf = wireNearSpaces(e, spaces)
  const bounds = routeBounds(e)
  const beta = rodBeta(e)
  const sc = e.scale
  const R = WIREP.sepR * sc
  const segs: WireSeg[] = []
  const segWire: number[] = []
  const wires: FrozenWireCap[] = []
  const termWires = new Map<string, number[]>()
  const push = (m: Map<string, number[]>, k: string, v: number): void => { const l = m.get(k); if (l !== undefined) l.push(v); else m.set(k, [v]) }
  let rodTotal = 0
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    const fs = spaces.space(wid)
    const ns = nsOf(wid)
    const bcs = wireTerminalBCs(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    const wi = wires.length
    const start = segs.length
    const edges: FrozenEdge[] = []
    let rod = 0
    for (const [u, v] of w.net.edges) {
      const pu = pos(u), pv = pos(v)
      const r = route(fs, pu, pv)
      const sol = solveEdgeCurve(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, pu, pv, r.hugs, ns, beta)
      rod += curveEnergy(sol.pts, ns, beta)
      edges.push({ wid, u, v, anchors: sol.anchors })
      for (let i = 0; i + 1 < sol.pts.length; i++) { segs.push({ wid, a: sol.pts[i]!, b: sol.pts[i + 1]! }); segWire.push(wi) }
    }
    wires.push({ wid, edges, segStart: start, segEnd: segs.length, rod })
    rodTotal += rod
    for (const bd of w.binds) push(termWires, bd.body, wi)
  }
  const obstacle = new Map<string, RouteDisc>()
  for (const b of e.bodies.values()) {
    if (isBodyObstacle(b)) {
      obstacle.set(b.id, {
        c: { x: b.pos.x, y: b.pos.y },
        r: b.discR * sc,
      })
    }
  }
  const regionDiscs = new Map<RegionId, RouteDisc>()
  for (const [rid, g] of e.regions) {
    if (e.d.regions[rid]!.kind === 'sheet') continue
    regionDiscs.set(rid, { c: { x: g.center.x, y: g.center.y }, r: g.radius })
  }
  const ridWires = new Map<RegionId, number[]>()
  for (let wi = 0; wi < wires.length; wi++) {
    for (const rid of spaces.forbiddenRids.get(wires[wi]!.wid) ?? []) {
      const l = ridWires.get(rid)
      if (l !== undefined) l.push(wi)
      else ridWires.set(rid, [wi])
    }
  }
  const ridBandSegs = new Map<RegionId, number[]>()
  for (const [rid, D] of regionDiscs) {
    const wl = ridWires.get(rid)
    if (wl === undefined) continue
    const band: number[] = []
    for (const wi of wl) {
      const cap = wires[wi]!
      for (let si = cap.segStart; si < cap.segEnd; si++) {
        const seg = segs[si]!
        // nearness reaches R beyond the boundary and ALL depths inside (the
        // quadratic keeps a nonzero gradient at any depth), so the band is
        // every seg whose MIDPOINT (the quadrature point) is within R of the
        // capture disc, plus the probe-scale Lipschitz margin.
        const mx = (seg.a.x + seg.b.x) / 2, my = (seg.a.y + seg.b.y) / 2
        if (Math.hypot(mx - D.c.x, my - D.c.y) <= D.r + R + PROBE_BAND) band.push(si)
      }
    }
    ridBandSegs.set(rid, band)
  }
  const grid = buildSepGrid(segs, R)
  // one near-pair pass yields both the total and each wire's contribution.
  const wireSep = new Float64Array(wires.length)
  let sepTotal = 0
  eachNearPair(segs, grid, R, (i, j) => {
    const ePair = segPairSepE(segs[i]!, segs[j]!, R)
    sepTotal += ePair
    wireSep[segWire[i]!]! += ePair
    wireSep[segWire[j]!]! += ePair
  })
  return {
    segs, segWire: Int32Array.from(segWire), wires, termWires, obstacle,
    forbiddenRids: spaces.forbiddenRids, regionDiscs, ridWires, ridBandSegs,
    grid, R, nearSlope: WIREP.sepSlope, beta, sc, bounds,
    frozenTotal: rodTotal + sepTotal, wireSep, seen: new Int32Array(segs.length), stamp: 0,
  }
}

/** The base segments of the affected wires (their cached curves). */
function affectedBaseSegs(fst: FrozenState, affSet: ReadonlySet<number>): WireSeg[] {
  const out: WireSeg[] = []
  for (const wi of affSet) { const cap = fst.wires[wi]!; for (let s = cap.segStart; s < cap.segEnd; s++) out.push(fst.segs[s]!) }
  return out
}

/** Σ separation of each `source` segment against the NON-affected base segments it
    is near (grid-enumerated, per-source dedup, cross-wire only). Used for both the
    OLD (source = affected base segs) and NEW (source = rebuilt segs) contributions. */
function affectedCrossSep(fst: FrozenState, affSet: ReadonlySet<number>, source: readonly WireSeg[]): number {
  const inv = 1 / fst.R, R = fst.R
  let E = 0
  const consider = (s: WireSeg, t: number, st: number): void => {
    if (fst.seen[t] === st) return
    fst.seen[t] = st
    if (affSet.has(fst.segWire[t]!)) return // affected base seg → the internal term handles it
    const bs = fst.segs[t]!
    if (bs.wid === s.wid) return
    E += segPairSepE(s, bs, R)
  }
  for (const s of source) {
    const st = ++fst.stamp
    const [cx0, cx1, cy0, cy1] = segCellSpan(s, inv)
    const cells = (cx1 - cx0 + 1) * (cy1 - cy0 + 1)
    if (!(cells >= 1 && cells <= GRID_MAX_CELLS)) {
      // a degenerate (huge/non-finite) source segment cannot query the grid.
      for (let t = 0; t < fst.segs.length; t++) consider(s, t, st)
      continue
    }
    for (let cx = cx0 - 1; cx <= cx1 + 1; cx++) for (let cy = cy0 - 1; cy <= cy1 + 1; cy++) {
      const b = fst.grid.grid.get(sepCellKey(cx, cy))
      if (b === undefined) continue
      for (const t of b) consider(s, t, st)
    }
    for (const t of fst.grid.large) consider(s, t, st) // large (non-bucketed) base segs
  }
  return E
}

/** Σ separation over cross-wire pairs WITHIN one segment list (the affected wires'
    internal contribution — small, so all-pairs). */
function internalCrossSep(arr: readonly WireSeg[], R: number): number {
  let E = 0
  for (let i = 0; i < arr.length; i++) for (let j = i + 1; j < arr.length; j++) {
    if (arr[i]!.wid === arr[j]!.wid) continue
    E += segPairSepE(arr[i]!, arr[j]!, R)
  }
  return E
}

/** The exact change in frozenWireEnergy when body `bodyId` is displaced to its
    CURRENT pose on `e`, relative to the base captured in `fst`. */
export function frozenProbe(fst: FrozenState, e: Engine, bodyId: string): number {
  const affWires = fst.termWires.get(bodyId)
  const affSet = affWires !== undefined ? new Set(affWires) : null
  let dRod = 0
  const newSegs: WireSeg[] = []

  // (1) rebuild the curves of wires terminating on bodyId (frozen anchors,
  // live endpoints — the envelope majorizer); full curveEnergy delta against
  // the LIVE drawn discs (regions were recomputed by the caller).
  const curRegionDisc = (rid: RegionId): RouteDisc => {
    const g = e.regions.get(rid)!
    return { c: g.center, r: g.radius }
  }
  if (affSet !== null) {
    const nodes = drawnObstacles(e)
    for (const wi of affSet) {
      const cap = fst.wires[wi]!
      const w = e.wires.get(cap.wid)!
      const terms = wireTerminalPoints(e, w)
      const bcs = wireTerminalBCs(e, w)
      const rids = fst.forbiddenRids.get(cap.wid) ?? []
      const ns: NearSpace = {
        discs: rids.length > 0 ? [...nodes, ...rids.map(curRegionDisc)] : nodes,
        bounds: fst.bounds, R: fst.R, slope: fst.nearSlope,
      }
      const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
      let newRod = 0
      for (const fe of cap.edges) {
        const bu = fe.u < bcs.length ? bcs[fe.u]! : null
        const bv = fe.v < bcs.length ? bcs[fe.v]! : null
        const pts = sampleCubics(chainThroughAnchors(bu, bv, [bu !== null ? bu.p : pos(fe.u), ...fe.anchors, bv !== null ? bv.p : pos(fe.v)]))
        newRod += curveEnergy(pts, ns, fst.beta)
        for (let i = 0; i + 1 < pts.length; i++) newSegs.push({ wid: cap.wid, a: pts[i]!, b: pts[i + 1]! })
      }
      dRod += newRod - cap.rod
    }
  }

  // (2) obstacle-surcharge patch: if bodyId is an obstacle whose disc MOVED, every
  // NON-affected wire's surcharge changes only through that one disc (length,
  // bending, frame, and every other disc are identical). Single-disc segSoftCost is
  // |seg| + that disc's surcharge, and the |seg| cancels in the new−old difference.
  const baseDisc = fst.obstacle.get(bodyId)
  if (baseDisc !== undefined) {
    const b = e.bodies.get(bodyId)!
    if (b.pos.x !== baseDisc.c.x || b.pos.y !== baseDisc.c.y) {
      const r = baseDisc.r, o = baseDisc.c, p = b.pos
      const oldD = baseDisc
      const newD = { c: p, r }
      // A segment's nearness against this disc is nonzero only within R of its
      // boundary, so a segment whose bbox is farther than r+R from BOTH the
      // old and new centre contributes exactly 0 to the difference — skip it.
      const reach = (r + fst.R) * (r + fst.R)
      const farFrom = (seg: WireSeg, c: Vec2): boolean => {
        const x0 = Math.min(seg.a.x, seg.b.x), x1 = Math.max(seg.a.x, seg.b.x)
        const y0 = Math.min(seg.a.y, seg.b.y), y1 = Math.max(seg.a.y, seg.b.y)
        const dx = c.x - Math.max(x0, Math.min(c.x, x1)), dy = c.y - Math.max(y0, Math.min(c.y, y1))
        return dx * dx + dy * dy > reach
      }
      for (let s = 0; s < fst.segs.length; s++) {
        if (affSet !== null && affSet.has(fst.segWire[s]!)) continue
        const seg = fst.segs[s]!
        if (farFrom(seg, o) && farFrom(seg, p)) continue
        dRod += segNearness(seg.a, seg.b, newD, fst.R, fst.nearSlope) - segNearness(seg.a, seg.b, oldD, fst.R, fst.nearSlope)
      }
    }
  }

  // (2b) region-circle surcharge patch: the displaced body drags its ancestor
  // circles, and every NON-affected wire whose forbidden set contains a changed
  // circle keeps its frozen curve while that curve's obstacle surcharge
  // changes. Single-disc segSoftCost differences (the |seg| term cancels), over
  // the precomputed boundary-band segs for probe-scale changes, or the wires'
  // full seg ranges for larger ones — exact either way (out-of-band segs keep
  // their inside/outside status by the Lipschitz bound).
  for (const [rid, oldD] of fst.regionDiscs) {
    const wl = fst.ridWires.get(rid)
    if (wl === undefined) continue
    const newD = curRegionDisc(rid)
    const w = Math.hypot(newD.c.x - oldD.c.x, newD.c.y - oldD.c.y) + Math.abs(newD.r - oldD.r)
    if (w === 0) continue
    const patchSeg = (si: number): void => {
      if (affSet !== null && affSet.has(fst.segWire[si]!)) return
      const seg = fst.segs[si]!
      dRod += segNearness(seg.a, seg.b, newD, fst.R, fst.nearSlope) - segNearness(seg.a, seg.b, oldD, fst.R, fst.nearSlope)
    }
    if (w <= PROBE_BAND) {
      for (const si of fst.ridBandSegs.get(rid) ?? []) patchSeg(si)
    } else {
      for (const wi of wl) {
        const cap = fst.wires[wi]!
        for (let si = cap.segStart; si < cap.segEnd; si++) patchSeg(si)
      }
    }
  }

  // (3) separation delta: only pairs touching a rebuilt (affected) segment change.
  //   touchedOld = Σ wireSep[w] − internalCrossSep(oldAff)  [cached; each affected
  //     wire's near pairs summed once, minus the affected–affected pairs the wireSep
  //     sum double-counted], touchedNew = affectedCrossSep(new) + internalCrossSep(new).
  //   Caching the OLD side avoids re-scanning every affected wire's near pairs.
  let dSep = 0
  if (affSet !== null) {
    const oldAff = affectedBaseSegs(fst, affSet)
    for (const wi of affSet) dSep -= fst.wireSep[wi]!
    dSep += internalCrossSep(oldAff, fst.R)         // undo the double-counted affected–affected old pairs
    dSep += affectedCrossSep(fst, affSet, newSegs)  // affectedNEW × non-affected
    dSep += internalCrossSep(newSegs, fst.R)        // affectedNEW internal (cross-wire)
  }
  return dRod + dSep
}

// ---- content energy (plan 23): the sibling-spacing preference and the
// scope-ring containment become ENERGY TERMS in the SAME functional the wires
// descend, so ONE strict per-DOF gate moves everything. The former sibling
// FORCE (a saturating barrier below REST_LO, a zero-force dead interval, then
// saturated cohesion beyond REST_HI) is exactly the negative gradient of
// `sibU`; there is no separate velocity-integrated content mover. ----

/** Sibling-spacing POTENTIAL over the circle gap: the exact antiderivative of
    the former sibling pair force (barrier + dead interval + cohesion), taken so
    U = 0 across the whole [REST_LO, REST_HI] rest interval and rising on both
    sides. C1 (force continuous) at both interval edges.

    PLAN 23: the barrier is UNCAPPED — it must DOMINATE everything (the USER's
    "the projection owns hard legality" made an energy term). Two sibling cuts
    tied by a line of identity are pulled together by the leg tension; a finite
    barrier (plan-22's cap, needed only because momentum could sling content into
    an unbounded barrier and exile it) LOSES that tug and rests with the cuts
    overlapping — a hard-law violation the per-tick projection used to hide.
    Under strict GATED descent there is no slinging, so the barrier can grow
    without bound and the gate simply never accepts a move deeper into overlap;
    it dominates the leg tension and the sibling cuts rest disjoint (measured:
    pc16's cuts overlapped by ~150 wu with the cap, 0 without it). The force is
    domain-clamped at gap+8 ≥ 0.5 (as the plan-22 force already was) so the log
    is never taken of a non-positive argument; below the clamp it grows linearly
    at the (enormous) clamp-floor force. */
function sibU(gap: number, sc: number): number {
  const LO = REST_LO(sc), HI = REST_HI(sc), g = PACE.sibGap * sc
  if (gap >= HI) {
    // cohesion: force ramps 0→SOFT_MAX over [HI, HI+g], constant beyond
    const over = gap - HI
    return over <= g ? (SOFT_MAX() * over * over) / (2 * g) : SOFT_MAX() * (g / 2 + (over - g))
  }
  if (gap >= LO) return 0
  // barrier: B(x) = rep·((LO+8)/max(x+8, 0.5) − 1), integrated gap→LO.
  const c = 8, k = PACE.rep, floor = 0.5
  const F = (x: number): number => k * ((LO + c) * Math.log(x + c) - x) // ∫ over x+c ≥ floor
  const gFloor = floor - c // below here the force is the constant clamp value
  const Bmax = k * ((LO + c) / floor - 1)
  return gap >= gFloor ? F(LO) - F(gap) : (F(LO) - F(gFloor)) + Bmax * (gFloor - gap)
}

/** The CUT hard-wall barrier: an UNCAPPED penalty on a region circle exceeding the
    fixed frame (USER 2026-07-06 — the border is a hard wall on CUTS, not just discs).
    Uncapped (like the sibling barrier) so under strict gated descent it DOMINATES the
    wire tension and the gate never accepts a member move that pushes the region past
    the border — the cut stays fully inside. The root sheet is exempt (it is not a
    drawn cut and encloses everything). Sums the overshoot on all four walls. */
function frameContainE(e: Engine): number {
  const f = e.frame
  if (f === null) return 0
  let E = 0
  for (const [rid, g] of e.regions) {
    if (rid === e.d.root) continue
    let pen = 0
    const rt = g.center.x + g.radius - (f.center.x + f.half); if (rt > 0) pen += rt
    const lf = (f.center.x - f.half) - (g.center.x - g.radius); if (lf > 0) pen += lf
    const bt = g.center.y + g.radius - (f.center.y + f.half); if (bt > 0) pen += bt
    const tp = (f.center.y - f.half) - (g.center.y - g.radius); if (tp > 0) pen += tp
    if (pen > 0) E += PACE.rep * pen * pen
  }
  return E
}

/** Total CONTENT energy: sibling spacing over every region's sibling pairs
    (content discs + child region circles; wire-owned dots take no sibling term —
    the wire barrier owns their clearance), the scope-ring containment of every
    wire-owned dot, and the CUT frame-containment hard wall. Region circles are
    read live, so a probe that moved a body must `recomputeRegions` first (the
    gates do). */
export function contentEnergy(e: Engine): number {
  const sc = e.scale
  let E = frameContainE(e)
  for (const rid of e.regions.keys()) {
    const items: { r: number; c: Vec2 }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      // ∃/∀ dots are ORDINARY nodes for layout (USER ruling 2026-07-24: nothing
      // is special about dangling wires — a dot is just a smaller node), so
      // they participate in the same disc+gap overlap energy as every body.
      items.push({ r: b.discR * sc, c: b.pos })
    }
    for (const cId of e.childrenOf.get(rid)!) { const g = e.regions.get(cId)!; items.push({ r: g.radius, c: g.center }) }
    for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
      const A = items[i]!, B = items[j]!
      const dist = Math.max(Math.hypot(A.c.x - B.c.x, A.c.y - B.c.y), 1)
      E += sibU(dist - A.r - B.r, sc)
    }
  }
  return E
}

/** The ONE energy the whole system descends: wires + content. Every gated step
    lowers a localized subset of it; its monotone non-increase across every
    settleStep is a theorem of the strict-descent architecture (pinned as a law). */
export function totalEnergy(e: Engine): number {
  return wireEnergy(e) + contentEnergy(e)
}

/** Single-body legality projection: push ONE body out of any sibling overlap in
    its own region (content vs content/child-region by discR+discR/radius+sibGap;
    a wire-owned dot only stays outside child circles — the wire barrier owns its
    disc clearance). This is the "project the trial onto the feasible set" step of
    the gated candidate evaluation (propose → project → evaluate E → accept only
    if lower); moving just the proposed body keeps the single-DOF gate monotone.
    Global legality across all bodies is the discrete-event `resolveOverlaps`. */
function projectBodyPos(e: Engine, b: Body, p: Vec2): Vec2 {
  let x = p.x, y = p.y
  const push = (cx: number, cy: number, need: number): void => {
    const dx = x - cx, dy = y - cy, d = Math.hypot(dx, dy)
    if (d >= need) return
    const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
    x = cx + ux * need; y = cy + uy * need
  }
  const sc = e.scale
  for (const mid of e.membersOf.get(b.region)!) {
    if (mid === b.id) continue
    const o = e.bodies.get(mid)!
    // dots are ordinary nodes (USER 2026-07-24): the same disc+gap projection
    push(o.pos.x, o.pos.y, (b.discR + o.discR) * sc + PACE.sibGap * sc)
  }
  for (const cId of e.childrenOf.get(b.region)!) {
    const g = e.regions.get(cId)!
    push(g.center.x, g.center.y, b.discR * sc + g.radius + PACE.sibGap * sc)
  }
  // the fixed frame is a hard wall (plan 24): a trial past the inner edge is
  // projected back in, so no content disc is ever accepted outside the frame
  return clampToFrame(e, b, { x, y })
}

/** Project a DRAGGED body's target position onto the SEMANTIC-feasible set: the
    body must stay OUTSIDE every region circle it is not a member of. This is HARD
    SEMANTIC CONTAINMENT (USER LAW): a node crossing into a cut it isn't part of
    CHANGES WHAT THE DIAGRAM MEANS, so it must not happen even transiently during a
    drag. The body is already inside its OWN region by construction — region circles
    are DERIVED to contain their members, so the region follows the dragged body —
    hence only the "outside non-member circles" half needs projecting. `p` is the
    unguarded cursor target; every non-ancestor cut circle pushes the body's
    disc fully clear with the sibling gap (the same bound the settling projection
    uses, so releasing the drag adds no jump). Ancestors of the body's region (the
    cuts it IS inside) are exempt. */
export function clampDragToFeasible(e: Engine, b: Body, p: Vec2): Vec2 {
  const ancestors = new Set<RegionId>()
  for (let r = b.region; ;) {
    ancestors.add(r)
    const reg = e.d.regions[r]!
    if (reg.kind === 'sheet') break
    r = reg.parent
  }
  const wall = e.frame
  const saved = b.pos
  const dirty = new Set<RegionId>([b.region])
  let x = p.x, y = p.y
  let pull = true
  let lastOver = Infinity
  let prePull = { x, y }
  // The three hard walls — foreign region circles, the fixed frame (plan 24),
  // and the CUT wall (USER 2026-07-06: the border contains the cuts too, so the
  // dragged body is pulled in until every ancestor circle fits) — are projected
  // ALTERNATELY to a joint fixed point. One sequential pass is wrong: the
  // cut-wall pull can drive the body straight through a foreign circle it was
  // pushed out of moments before (measured 4.75 wu deep), which both violates
  // hard semantic containment and freezes the drag frontier. Alternation makes
  // the pull and the push compose into a slide around the foreign clearance.
  // All bounds here are SEMANTIC (disc against drawn circle), not aesthetic:
  // a gap-inclusive push moves bodies that rest legally inside their gap, and
  // that sideways "healing" both surprises the cursor and reads as a worsening
  // to the frontier's strict no-deepening gate. Gap restoration is the live
  // settle's job. Terminates when a full round moves the point less than the
  // cut-wall tolerance (0.05 wu); measured on the wall-pull-through-circle
  // fixture the joint residual hits zero in 9–12 rounds, so the cap of 16 is
  // that plus margin — any residual past it is caught by the drag frontier's
  // relative gate rather than accepted.
  for (let it = 0; it < 16; it++) {
    const px = x, py = y
    for (const [rid, g] of e.regions) {
      if (ancestors.has(rid) || e.d.regions[rid]!.kind === 'sheet') continue
      const need = b.discR * e.scale + g.radius
      const dx = x - g.center.x, dy = y - g.center.y, d = Math.hypot(dx, dy)
      if (d >= need) continue
      const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
      x = g.center.x + ux * need; y = g.center.y + uy * need
    }
    const c0 = clampToFrame(e, b, { x, y })
    x = c0.x; y = c0.y
    if (wall !== null && pull) {
      b.pos = { x, y }
      recomputeRegions(e, dirty)
      let rt = 0, lf = 0, bt = 0, tp = 0
      for (const rid of ancestors) {
        if (e.d.regions[rid]!.kind === 'sheet') continue
        const g = e.regions.get(rid)
        if (g === undefined) continue
        rt = Math.max(rt, g.center.x + g.radius - (wall.center.x + wall.half))
        lf = Math.max(lf, (wall.center.x - wall.half) - (g.center.x - g.radius))
        bt = Math.max(bt, g.center.y + g.radius - (wall.center.y + wall.half))
        tp = Math.max(tp, (wall.center.y - wall.half) - (g.center.y - g.radius))
      }
      // A pull is only valid while it WORKS: an ancestor circle can spill
      // because of content that is not this body at all (its edge supported by
      // a sibling subtree), and pulling then just marches the body across the
      // scene by the spill amount every round without moving the circle
      // (measured: a 0.73 wu residual spill dragged the body 11 wu off the
      // cursor). If a round fails to reduce the worst overshoot, undo that
      // round's pull and stop pulling — the residual is not this drag's to fix
      // and the frontier's relative gate tolerates it at its baseline.
      const over = Math.max(rt, lf, bt, tp, 0)
      if (over >= lastOver - 0.01) {
        x = prePull.x; y = prePull.y
        pull = false
      } else {
        lastOver = over
        prePull = { x, y }
        const dx = rt > lf ? -rt : lf, dy = bt > tp ? -bt : tp
        const c = clampToFrame(e, b, { x: x + dx, y: y + dy })
        x = c.x; y = c.y
        // If the pull landed inside a foreign circle, slide ALONG that circle
        // to the pulled axis line (the joint projection for the pair) instead
        // of leaving the radial push to fight the pull — plain alternation
        // drifts tangentially by a sliver per round and never resolves a
        // head-on pull (measured 3.7 wu penetration left after 16 rounds).
        for (const [rid, g] of e.regions) {
          if (ancestors.has(rid) || e.d.regions[rid]!.kind === 'sheet') continue
          const need = b.discR * e.scale + g.radius
          if (Math.hypot(x - g.center.x, y - g.center.y) >= need) continue
          if (dx !== 0 && Math.abs(x - g.center.x) < need) {
            const h = Math.sqrt(need * need - (x - g.center.x) * (x - g.center.x))
            y = g.center.y + (y >= g.center.y ? h : -h)
          } else if (dy !== 0 && Math.abs(y - g.center.y) < need) {
            const h = Math.sqrt(need * need - (y - g.center.y) * (y - g.center.y))
            x = g.center.x + (x >= g.center.x ? h : -h)
          }
        }
      }
    }
    if (Math.hypot(x - px, y - py) < 0.05) break
  }
  if (wall !== null) {
    b.pos = saved
    recomputeRegions(e, dirty)
  }
  return { x, y }
}

/**
 * THE per-frame NODE step (routed-network model): bodies are the only
 * dynamical coordinates — positions, rotations of port-bearing bodies, and
 * wire-owned ∃/∀ end dots. Every probe evaluates THE one energy (routed
 * wireEnergy + content); node rotation descends the same functional, so port
 * angles are calculated along with the curves. One-sided gradient
 * selection (piecewise-smooth content terms), one simultaneous sup-norm-
 * bounded trial per Δ halving with legality projection and a strict gate,
 * then single-coordinate fallback. Memoryless and deterministic.
 */
function operatorStep(e: Engine, pinned: ReadonlySet<string> | null): boolean {
  const sc = e.scale
  recomputeRegions(e)
  const wiredBodies = new Set<string>()
  for (const [, w] of e.wires) {
    for (const bd of w.binds) wiredBodies.add(bd.body)
  }

  // ONE exact routed eval captures the frozen state (paths + per-wire/segment
  // caches). Every gradient probe below re-measures it via the frozen-probe
  // LOCALITY DELTA (score change from displacing this one body), not a full
  // frozenWireEnergy rebuild — no routing solves, and no whole-scene re-eval.
  const fst = mkFrozenState(e)

  type Coord = {
    get(): number
    set(v: number): void
    /** Probe application: set + the SAME legality projection the trial gates
        apply (propose -> project -> evaluate). Probes that skip the projection
        measure a map the gates never test: on a packed seed every
        single-coordinate move violates a sibling gap, the projection cancels
        it, and the un-projected probes kept promising descent — the fallback
        then exhaustively disproved them at full-eval cost, ~336 trials/step,
        100% rejected (measured 2026-07-31). Rotation needs no projection. */
    probe(v: number): void
    probeRestore(): void
    readonly m: number
    readonly rot: boolean
    localE(): number
  }
  const coords: Coord[] = []
  const movedBodies: Body[] = []
  for (const b of e.bodies.values()) {
    const dirty = new Set<RegionId>([b.region])
    const localE = (): number => { recomputeRegions(e, dirty); return fst.frozenTotal + frozenProbe(fst, e, b.id) + contentEnergy(e) }
    if (pinned === null || !pinned.has(b.id)) {
      movedBodies.push(b)
      let saved: Vec2 | null = null
      const probeAt = (p: Vec2): void => {
        if (saved === null) saved = b.pos
        b.pos = projectBodyPos(e, b, p)
      }
      const probeRestore = (): void => { if (saved !== null) { b.pos = saved; saved = null } }
      coords.push({
        get: () => b.pos.x, set: (v) => { b.pos = { x: v, y: b.pos.y } },
        probe: (v) => probeAt({ x: v, y: b.pos.y }), probeRestore,
        m: 1, rot: false, localE,
      })
      coords.push({
        get: () => b.pos.y, set: (v) => { b.pos = { x: b.pos.x, y: v } },
        probe: (v) => probeAt({ x: b.pos.x, y: v }), probeRestore,
        m: 1, rot: false, localE,
      })
    }
    // rotation: an ordinary coordinate under the same budget (2026-07-24 law);
    // only port-bearing wired bodies feel it (content is rotation-invariant)
    if (wiredBodies.has(b.id) && b.localAnchor.size > 0) {
      coords.push({
        get: () => b.theta, set: (v) => { b.theta = v },
        probe: (v) => { b.theta = v }, probeRestore: () => {},
        m: Math.max(b.discR * sc, 1e-6), rot: true, localE,
      })
    }
  }

  // ── one-sided gradient (piecewise-smooth terms: keep the steeper strictly
  // descending side; a kink minimum contributes zero) at drawn-uniform probes ──
  const g: number[] = new Array(coords.length).fill(0)
  const baseMemo = new Map<Coord['localE'], number>()
  const baseOf = (c: Coord): number => {
    let v = baseMemo.get(c.localE)
    if (v === undefined) { v = c.localE(); baseMemo.set(c.localE, v) }
    return v
  }
  for (let i = 0; i < coords.length; i++) {
    const c = coords[i]!
    const v0 = c.get()
    const h = FD_PROBE / c.m
    const e0 = baseOf(c)
    c.probe(v0 + h); const ep = c.localE()
    c.probeRestore()
    c.probe(v0 - h); const em = c.localE()
    c.probeRestore()
    c.set(v0)
    const slopeP = (ep - e0) / h
    const slopeM = (e0 - em) / h
    const descP = slopeP < 0, descM = slopeM > 0
    g[i] = descP && (!descM || -slopeP >= slopeM) ? slopeP : descM ? slopeM : 0
  }
  recomputeRegions(e)
  let gnorm2 = 0
  let gsup = 0
  for (let i = 0; i < coords.length; i++) {
    const su = g[i]! / coords[i]!.m
    gnorm2 += su * su
    const drawn = Math.abs(g[i]!) / coords[i]!.m
    if (drawn > gsup) gsup = drawn
  }

  const bodySnap = new Map<string, { pos: Vec2; theta: number }>()
  for (const b of e.bodies.values()) bodySnap.set(b.id, { pos: { ...b.pos }, theta: b.theta })
  const restore = (): void => {
    for (const b of e.bodies.values()) { const sn = bodySnap.get(b.id)!; b.pos = { ...sn.pos }; b.theta = sn.theta }
  }

  // fst.frozenTotal == the exact routed wireEnergy at base (frozen curves equal the
  // routed curves at the captured optimum), so this is the old `base.E + content`.
  const E0 = fst.frozenTotal + contentEnergy(e)
  const EPS = 1e-9 * (Math.abs(E0) + 1)

  // ── ANISOTROPIC TRUST REGION. A DOF's step ceiling is its own natural range,
  // which differs by KIND (USER 2026-07-25: rotation is not throttled like an ODE
  // integrator — it may turn as far as the geometry allows):
  //   • rotation — θ is periodic, so π is the largest DISTINCT turn (beyond π is
  //     the same orientation reached the short way). This is the false-rest cure:
  //     a node whose port faces AWAY from its partner sits at a rotation barrier
  //     that only a ~π turn clears; the old sub-radian cap rested against it. The
  //     ladder tries the largest turn FIRST, so it steps over the barrier instead
  //     of resting on the near side.
  //   • position — the per-tick LOCALITY budget (travelCap·scale). A body's
  //     position descends locally; GLOBAL positional reconfiguration is the search
  //     layer's job (the optimizer's subtree/hop moves), NOT the local step. A
  //     frame-scale joint position step was measured to defeat basin hopping — it
  //     lets one aggressive descent slide a hop-displaced subtree straight back
  //     into its trap, so the wedged-cut acceptance basin (anneal.test) became
  //     inescapable. Keeping the step local leaves the search's hops intact.
  // The ladder runs LARGEST→smallest and commits the first strictly-descending
  // rung. Its floor FD_PROBE is the gradient-probe drawn step — a trial finer than the
  // probe is below sensing noise. Memoryless: nothing persists between ticks.
  if (e.frame === null) throw new Error('operatorStep: frame must be established before descent')
  const posCeil = WIREP.travelCap * sc
  const rotCeil = (m: number): number => Math.PI * m // drawn ceiling of an m-metric rotation
  const ceilDrawn = (c: Coord): number => (c.rot ? rotCeil(c.m) : posCeil)

  // Joint trust region: the direction rides the box boundary of the FIRST
  // coordinate to saturate its own drawn ceiling, so no coordinate exceeds its
  // limit while the descent direction is preserved (each position coord is capped
  // at posCeil by its own term, so rotation may reach π here without the joint
  // position step ever exceeding the locality budget).
  let jointCeil = Infinity
  for (let i = 0; i < coords.length; i++) {
    if (g[i] === 0) continue
    const c = coords[i]!
    const drawnGrad = Math.abs(g[i]!) / c.m
    jointCeil = Math.min(jointCeil, (ceilDrawn(c) * gsup) / drawnGrad)
  }

  for (let delta = jointCeil; gsup > 0 && delta >= FD_PROBE; delta /= 2) {
    if (delta * (gnorm2 / gsup) < EPS) break
    // one simultaneous trial: the M-metric steepest-descent DIRECTION, scaled
    // so the LARGEST drawn coordinate displacement is delta (the trust radius)
    for (let i = 0; i < coords.length; i++) {
      const c = coords[i]!
      c.set(c.get() - delta * (g[i]! / (c.m * c.m)) / gsup)
    }
    for (const b of movedBodies) b.pos = projectBodyPos(e, b, b.pos)
    recomputeRegions(e)
    const E1 = wireEnergy(e) + contentEnergy(e)
    if (E1 < E0 - EPS) return true
    restore()
    recomputeRegions(e)
  }
  // ── COORDINATE FALLBACK: a crease from coordinate interactions can block the
  // joint direction while single coordinates still descend — try them in
  // steepest order under the same gate, each under its own drawn ceiling.
  //
  // GATE VIA THE EXACT INCREMENTAL DELTA (annealing redesign D1): each trial
  // here is base + ONE coordinate — the incremental evaluator's best case —
  // so the gate reads applyMove's exact dE against a ScoreState captured once
  // at the base, instead of a whole-scene routed eval per trial (the measured
  // ~890 whole-scene evaluations per settle step on large scenes). The gate
  // stays EXACT: dE is proven exact (score-delta.test), so acceptance is
  // bit-for-bit the strict-descent criterion. The JOINT trials above keep
  // fresh full evals (all coordinates move → the delta degenerates to a full
  // eval; measured to regress). The ScoreState is built lazily — a joint
  // accept never pays for it. ──
  const order = coords.map((_, i) => i).filter((i) => g[i] !== 0)
  order.sort((x, y) => Math.abs(g[y]! / coords[y]!.m) - Math.abs(g[x]! / coords[x]!.m) || x - y)
  let st: ScoreState | null = null
  for (const i of order) {
    const c = coords[i]!
    const dir = -Math.sign(g[i]!)
    for (let delta = ceilDrawn(c); delta >= FD_PROBE; delta /= 2) {
      if ((delta * Math.abs(g[i]!)) / c.m < EPS) break
      if (st === null) st = mkScoreState(e)
      c.set(c.get() + (dir * delta) / c.m)
      for (const b of movedBodies) b.pos = projectBodyPos(e, b, b.pos)
      recomputeRegions(e)
      // the actual moved set: the trial coordinate's body plus anything the
      // legality projection displaced (compared against the base snapshot)
      const moved = new Set<string>()
      for (const b of e.bodies.values()) {
        const sn = bodySnap.get(b.id)!
        if (b.pos.x !== sn.pos.x || b.pos.y !== sn.pos.y || b.theta !== sn.theta) moved.add(b.id)
      }
      const mr = applyMove(e, st, moved)
      if (mr.dE < -EPS) return true
      mr.abort()
      restore()
      recomputeRegions(e)
    }
  }
  return false
}

/**
 * ASYNCHRONOUS LAYOUT SEARCH (USER rulings 2026-07-24): whole-layout global
 * optimization runs asynchronously — "the user should not perceive anything
 * from a heavy search". A frame with a search attached does ONLY bounded
 * cheap work: push live state to the searcher, take one bounded approach
 * step toward the best-known layout when one strictly better is known, and
 * advance the wire presentation walk. The heavy minimization (local descent
 * + the trial schedule) runs elsewhere (a worker) and publishes best
 * snapshots through this interface. Engines with no search attached (tests,
 * `settle`, the searcher's own scratch engines) run the full local solvers
 * synchronously, unchanged.
 */
export type LayoutSearch = {
  /** Push the live boundary state (diagram identity, pins, live poses). */
  sync(e: Engine, pinned: ReadonlySet<string> | null): void
  /** Newest best-known layout (asynchronously updated), or null. */
  best(): LayoutBest | null
  /** The live layout is strictly better than the stored best — publish it. */
  adoptLive(e: Engine, score: number): void
  /** Search work still in flight (frames must keep polling). */
  readonly searching: boolean
}

const LAYOUT_SEARCH = new WeakMap<Engine, LayoutSearch>()
export function attachLayoutSearch(e: Engine, s: LayoutSearch | null): void {
  if (s === null) LAYOUT_SEARCH.delete(e)
  else LAYOUT_SEARCH.set(e, s)
}

/** Exact live-configuration key (poses + nets): the score cache's validity. */
function liveKey(e: Engine): string {
  const parts: (string | number)[] = []
  for (const [id, b] of e.bodies) parts.push(id, b.pos.x, b.pos.y, b.theta)
  for (const [wid, w] of e.wires) {
    parts.push(wid)
    for (const p of w.net.junctions) parts.push(p.x, p.y)
    for (const [u, v] of w.net.edges) parts.push(u, v)
  }
  return parts.join(',')
}

/** Lazily-cached live layout score: the full energy is evaluated only at
    DECISION EVENTS (a new best arrived, or the live layout came to rest) —
    never per frame. */
const liveScoreCache = new WeakMap<Engine, { key: string; score: number }>()
function liveScoreAt(e: Engine): number {
  const key = liveKey(e)
  const hit = liveScoreCache.get(e)
  if (hit !== undefined && hit.key === key) return hit.score
  const score = layoutScore(e)
  liveScoreCache.set(e, { key, score })
  return score
}

/** Per-engine sticky approach decision: re-scored only at DECISION EVENTS (a
    new best snapshot, or a mismatch REAPPEARING after the live layout had
    matched — e.g. a walk topology change unlocked junction approach) — never
    per frame. */
const searchFrameState = new WeakMap<Engine, { decidedFor: LayoutBest | null; approach: boolean; rematch: boolean; lastAdoptKey: string; lastWalkKey: string }>()

/** Same wire topology = same edge list (junction indices correspond). */
const sameTopology = (a: WireNet, b: WireNet): boolean =>
  a.junctions.length === b.junctions.length && JSON.stringify(a.edges) === JSON.stringify(b.edges)

/** Does the live layout differ (beyond float dust) from the best snapshot on
    any coordinate the approach may move? Junctions of topology-matched wires
    are approach coordinates like body poses: the approach must carry them all
    the way into the searcher's basin (a gated walk cannot cross the barrier
    the searcher's hop crossed). */
function bestMismatch(e: Engine, best: LayoutBest, pinned: ReadonlySet<string> | null): boolean {
  for (const [id, b] of e.bodies) {
    if (pinned !== null && pinned.has(id)) continue
    const t = best.poses.get(id)
    if (t === undefined) continue
    if (Math.abs(t.pos.x - b.pos.x) > 1e-6 || Math.abs(t.pos.y - b.pos.y) > 1e-6) return true
    if (Math.abs(Math.atan2(Math.sin(t.theta - b.theta), Math.cos(t.theta - b.theta))) > 1e-6) return true
  }
  for (const [wid, w] of e.wires) {
    const n = best.nets.get(wid)
    if (n === undefined || !sameTopology(w.net, n)) continue
    for (let j = 0; j < w.net.junctions.length; j++) {
      const p = w.net.junctions[j]!, q = n.junctions[j]!
      if (Math.abs(q.x - p.x) > 1e-6 || Math.abs(q.y - p.y) > 1e-6) return true
    }
  }
  return false
}

/** The shortest path from a body's position to `target` that respects
    semantic containment, as a polyline: the body's non-ancestor region circles
    are routing obstacles inflated to the aesthetic clearance (sibGap included,
    shrunk by a hair so a body resting ON that boundary routes from a feasible
    point) — the path PREFERS keeping the gap where room exists, while the drag
    clamp and the frontier gate enforce only the tighter semantic bound. The
    frame participates as the route's bounds (steep soft cost outside), so the
    path picks a side with a real corridor instead of wedging into the pocket
    between a circle and the wall; the wall itself stays hard via the drag
    clamp. With no blocking circle this is the straight segment at the same
    cost. Both the presentation approach and the drag frontier move bodies
    ALONG this path — the straight chord to a target on the far side of a cut
    passes through the cut, so any straight-line interpolation either violates
    containment or wedges radially against it. */
export function containedPath(e: Engine, b: Body, target: Vec2): readonly Vec2[] {
  const ancestors = new Set<RegionId>()
  for (let r = b.region; ;) {
    ancestors.add(r)
    const reg = e.d.regions[r]!
    if (reg.kind === 'sheet') break
    r = reg.parent
  }
  const discs: RouteDisc[] = []
  for (const [rid, g] of e.regions) {
    if (ancestors.has(rid) || e.d.regions[rid]!.kind === 'sheet') continue
    const need = b.discR * e.scale + g.radius + PACE.sibGap * e.scale
    discs.push({ c: g.center, r: need - 1e-3 })
  }
  return route(mkFreeSpace(discs, routeBounds(e)), b.pos, target).pts
}

/** The point `st` of arclength along a polyline (its end once `st` covers it). */
function advanceAlong(pts: readonly Vec2[], st: number): Vec2 {
  let remaining = st
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1]!, q = pts[i]!
    const seg = Math.hypot(q.x - a.x, q.y - a.y)
    if (seg >= remaining) {
      const f = seg < 1e-12 ? 0 : remaining / seg
      return { x: a.x + (q.x - a.x) * f, y: a.y + (q.y - a.y) * f }
    }
    remaining -= seg
  }
  return { ...pts[pts.length - 1]! }
}

/** One bounded step from a body toward `target` along `containedPath`. */
function stepAroundForeignCuts(e: Engine, b: Body, target: Vec2, st: number): Vec2 {
  return advanceAlong(containedPath(e, b, target), st)
}

/** One bounded step of a whole region's CIRCLE toward `target`, as the
    translation to apply to its subtree.

    The circle is routed as a DISC among its in-parent sibling circles (each
    inflated to the clearance below, shrunk a hair so a region resting ON that
    clearance routes from a feasible point), inside the frame bounds — the same
    soft-cost routing `containedPath` gives a body, lifted to the group and
    clamped back onto that clearance. Choosing the way around ONCE per region is
    what a per-body route cannot express: a region circle is a property of its
    whole subtree, so members that round a sibling circle on OPPOSITE sides
    sweep the derived circle straight across it however clear each member
    itself stays. */
function regionEnvelopeStep(e: Engine, parent: RegionId, rid: RegionId, target: Vec2, st: number): Vec2 {
  const live = e.regions.get(rid)!
  // The clearance this travel KEEPS around each in-parent sibling: the aesthetic
  // gap, but never more than the destination itself keeps (a best that parks the
  // region closer must stay reachable) and never more than the region already
  // has (this layer preserves clearance; healing a violation is the settle's
  // job, and a healing push would break the presentation travel bound). The
  // semantic floor underneath is the frontier gate's, not this layer's.
  const clear: { readonly c: Vec2; readonly need: number }[] = []
  for (const sid of e.childrenOf.get(parent)!) {
    if (sid === rid) continue
    const g = e.regions.get(sid)!
    const want = live.radius + g.radius + PACE.sibGap * e.scale
    const held = Math.hypot(live.center.x - g.center.x, live.center.y - g.center.y)
    const dest = Math.hypot(target.x - g.center.x, target.y - g.center.y)
    clear.push({ c: g.center, need: Math.min(want, held, dest) })
  }
  const discs: RouteDisc[] = clear.map(({ c, need }) => ({ c, r: need - 1e-3 }))
  const walked = advanceAlong(route(mkFreeSpace(discs, routeBounds(e)), live.center, target).pts, st)
  let px = walked.x, py = walked.y
  // Ride that clearance boundary EXACTLY. A routed hug is polylined into chords
  // that fall inside the circle they hug, so a walker following them drifts in;
  // re-routing from the drifted centre then shrinks the clearance again, and
  // once the centre is INSIDE a disc the tangent detour ceases to exist at all
  // and the route degenerates to the straight segment THROUGH the sibling
  // (measured: the travel abandons its arc mid-journey and drives at the cut).
  // Projecting the stepped centre back onto the boundary holds the homotopy the
  // route chose, for the same reason the drag clamps every path point.
  for (const { c, need } of clear) {
    const dx = px - c.x, dy = py - c.y, d = Math.hypot(dx, dy)
    if (d >= need) continue
    const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
    px = c.x + ux * need; py = c.y + uy * need
  }
  return { x: px - live.center.x, y: py - live.center.y }
}

/** This frame's per-body target positions for the interior of `rid`, at the one
    presentation `bound`.

    Direct members step individually along their contained paths. A child region
    whose BEST circle sits elsewhere TRAVELS: its circle takes one envelope step
    and the whole subtree rides it RIGIDLY (a translated disc set has the
    translated minimal enclosing circle, so the region's derived circle follows
    the routed homotopy exactly). Only once a traveling region has ARRIVED does
    its interior refine, by this same scheme one level down — its members toward
    their best poses, its own traveling children as envelopes against their
    in-region siblings. Arrival is exact: steps are min(distance, bound), so the
    last one lands on the target centre. */
function approachTargets(
  e: Engine,
  rid: RegionId,
  best: LayoutBest,
  bestCircles: ReadonlyMap<RegionId, RegionCircle>,
  bound: number,
  pinned: ReadonlySet<string> | null,
  out: Map<string, Vec2>,
): void {
  for (const mid of e.membersOf.get(rid)!) {
    if (pinned !== null && pinned.has(mid)) continue
    const b = e.bodies.get(mid)!
    const t = best.poses.get(mid)
    if (t === undefined) continue
    const d = Math.hypot(t.pos.x - b.pos.x, t.pos.y - b.pos.y)
    if (d <= 1e-9) continue
    out.set(mid, stepAroundForeignCuts(e, b, t.pos, Math.min(d, bound)))
  }
  for (const cid of e.childrenOf.get(rid)!) {
    const live = e.regions.get(cid)!
    const goal = bestCircles.get(cid)!.center
    const d = Math.hypot(goal.x - live.center.x, goal.y - live.center.y)
    if (d <= 1e-9) {
      approachTargets(e, cid, best, bestCircles, bound, pinned, out)
      continue
    }
    const step = regionEnvelopeStep(e, rid, cid, goal, Math.min(d, bound))
    for (const mid of subtreeCarriers(e, cid)) {
      if (pinned !== null && pinned.has(mid)) continue
      const b = e.bodies.get(mid)!
      out.set(mid, { x: b.pos.x + step.x, y: b.pos.y + step.y })
    }
  }
}

/** PRESENTATION pace (USER ruling 2026-07-25): the visible settling should
    read as a GENTLE approach to the minimum, not a rapid jerk — on-screen
    motion runs ~5× slower than the solver's trust region. Presentation-only:
    the worker's relaxations and the local solver path are untouched. The
    value is user-calibrated ("a slow down of maybe around five x… let's see
    if that looks good"), re-judged visually, never tuned blindly. */
export const PRESENT_SLOW = 5

/** One bounded approach step toward the best snapshot. EVERY visible DOF moves
    under the ONE presentation bound — body positions, body angles, and the
    junctions of wires whose topology matches the best's (their indices
    correspond, so each junction has a target). A differing topology is NEVER
    adopted (adopting a net whole teleports junction state — the measured
    ~10 wu snap): the presentation walk evolves those wires through its own
    coincidence-scale contract/split events instead. Returns the set of wires
    the approach owns this frame, so the walk leaves them alone (running both
    on one wire is the measured approach-vs-descent tug-of-war). */
function approachStep(e: Engine, best: LayoutBest, pinned: ReadonlySet<string> | null): Set<WireId> {
  const bound = (WIREP.travelCap / PRESENT_SLOW) * e.scale
  // HARD SEMANTIC CONTAINMENT (USER LAW, restated 2026-07-30 for the approach):
  // the animation toward a searched best obeys exactly the law a drag does — no
  // node enters a cut it is not part of, no two cut circles meet, not even
  // transiently. The approach therefore composes the SAME three layers the drag
  // frontier does, with the routing layer lifted to whole regions
  // (`approachTargets`) because the derived circle a region draws is a property
  // of its subtree, not of any one member. The frontier then walks the joint
  // candidate back to the last position set that introduces or deepens NO
  // semantic conflict, so a frame that would cross a bound simply moves less.
  // Every circle read while the targets are built — the foreign circles in each
  // member's `containedPath`, the live and sibling circles in each envelope
  // step — is read BEFORE any position is written, so the whole frame's targets
  // are derived from one consistent scene. Writing bodies as they are decided
  // would make each later body clamp against a circle the earlier ones have
  // already invalidated.
  const targets = new Map<string, Vec2>()
  approachTargets(
    e, e.d.root, best,
    regionCirclesAt(e, (mid) => best.poses.get(mid)?.pos ?? e.bodies.get(mid)!.pos),
    bound, pinned, targets,
  )
  commitBodyPositions(e, projectDragToSemanticFrontier(e, targets).positions)
  for (const [id, b] of e.bodies) {
    if (pinned !== null && pinned.has(id)) continue
    const t = best.poses.get(id)
    if (t === undefined) continue
    const dth = Math.atan2(Math.sin(t.theta - b.theta), Math.cos(t.theta - b.theta))
    const thBound = bound / Math.max(b.discR * e.scale, 1e-6)
    if (Math.abs(dth) > 1e-9) b.theta += Math.sign(dth) * Math.min(Math.abs(dth), thBound)
  }
  const owned = new Set<WireId>()
  for (const [wid, w] of e.wires) {
    const n = best.nets.get(wid)
    if (n === undefined || !sameTopology(w.net, n)) continue
    owned.add(wid)
    for (let j = 0; j < w.net.junctions.length; j++) {
      const p = w.net.junctions[j]!, q = n.junctions[j]!
      const dx = q.x - p.x, dy = q.y - p.y
      const d = Math.hypot(dx, dy)
      if (d > 1e-9) {
        const st = Math.min(d, bound)
        w.net.junctions[j] = { x: p.x + (dx / d) * st, y: p.y + (dy / d) * st }
      }
    }
  }
  return owned
}

/** The wire presentation walk: bounded continuation toward each wire's own routed
    target. Returns whether anything moved.

    STRICT-DESCENT GATE (plan Task 8, USER limit-cycle repro): the walk moves ONE
    wire's junctions at a time, so the only terms of the total energy that change
    are that wire's rod cost AND the separation pairs between its segments and the
    OTHER wires' (fixed) segments — everything else (other wires' rod, other-vs-other
    separation, content) is constant. Gating each wire's substep and split on
    `rod(w) + separation(w vs others)` therefore gates ΔE_total exactly, so the walk
    strictly descends the whole objective. Gating on rod alone (the old behavior)
    let the walk trade rod down while pushing separation up without bound — a limit
    cycle that never rested. The Δsep term is charged via the spatial grid of the
    other wires' segments (they do not move while this wire walks). */
function walkWires(e: Engine, presentation = false, skip: ReadonlySet<WireId> | null = null): boolean {
  const spaces = wireRouteSpaces(e)
  const nsOf = wireNearSpaces(e, spaces)
  const beta = rodBeta(e), sc = e.scale, R = WIREP.sepR * sc
  // the walk moves VISIBLE junction state: presentation frames use the one
  // presentation bound (the same per-frame pace every visible DOF gets);
  // solver walks keep the full trust region (descent is optimization, not
  // simulation — 2026-07-25)
  const bound = presentation ? (WIREP.travelCap / PRESENT_SLOW) * sc : WIREP.travelCap * sc
  const walkers: { wid: WireId; w: WireView; terms: Vec2[]; bcs: CurveBC[]; fs: FreeSpace; ns: NearSpace }[] = []
  const segsByWid = new Map<WireId, Seg2[]>()
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    const fsW = spaces.space(wid)
    const nsW = nsOf(wid)
    const bcs = wireTerminalBCs(e, w)
    walkers.push({ wid, w, terms, bcs, fs: fsW, ns: nsW })
    segsByWid.set(wid, netEval(w.net, terms, fsW, nsW, bcs, beta).segs)
  }
  let routed = false
  for (const { wid, w, terms, bcs, fs, ns } of walkers) {
    if (skip !== null && skip.has(wid)) continue
    // grid of every OTHER wire's current segments (fixed while this wire walks).
    const others: Seg2[] = []
    for (const [owid, segs] of segsByWid) if (owid !== wid) for (const s of segs) others.push(s)
    const sg = buildSepGrid(others, R)
    const seen = new Int32Array(others.length)
    let stamp = 0
    const inv = 1 / R
    const gate = (n: WireNet): number => {
      const { L, segs } = netEval(n, terms, fs, ns, bcs, beta)
      let sep = 0
      for (const s of segs) {
        stamp++
        const [cx0, cx1, cy0, cy1] = segCellSpan(s, inv)
        const cells = (cx1 - cx0 + 1) * (cy1 - cy0 + 1)
        if (!(cells >= 1 && cells <= GRID_MAX_CELLS)) {
          // a degenerate (huge/non-finite) segment cannot query the grid — its
          // neighborhood would be unbounded — so charge it against every other.
          for (let t = 0; t < others.length; t++) sep += segPairSepE(s, others[t]!, R)
          continue
        }
        for (let cx = cx0 - 1; cx <= cx1 + 1; cx++) for (let cy = cy0 - 1; cy <= cy1 + 1; cy++) {
          const b = sg.grid.get(sepCellKey(cx, cy))
          if (b === undefined) continue
          for (const t of b) { if (seen[t] === stamp) continue; seen[t] = stamp; sep += segPairSepE(s, others[t]!, R) }
        }
        // plus the large (non-bucketed) other segments.
        for (const t of sg.large) { if (seen[t] === stamp) continue; seen[t] = stamp; sep += segPairSepE(s, others[t]!, R) }
      }
      return L + sep
    }
    // ONE presentation substep at the presentation bound = the per-frame wire
    // travel equals the body travel; solver walks keep their full budget
    routed = advanceNetwork(w.net, terms, fs, { substeps: presentation ? 1 : 20, bound, ns, bcs, beta, gate }) || routed
    // this wire moved → refresh its segments so later wires see the new positions.
    segsByWid.set(wid, netEval(w.net, terms, fs, ns, bcs, beta).segs)
  }
  return routed
}

/** The searched frame: strictly bounded per-frame work. The approach owns the
    coordinates with a known target (body poses + junctions of topology-matched
    wires) when a strictly better layout is known; the presentation walk keeps
    every OTHER wire settling on the SAME frame — wires never freeze while
    bodies move (the measured lag-then-snap), and no coordinate is moved by
    both (the measured tug-of-war). The full energy is evaluated only at
    decision events. */
function searchedFrame(e: Engine, pinned: ReadonlySet<string> | null, search: LayoutSearch): boolean {
  search.sync(e, pinned)
  const best = search.best()
  const st = searchFrameState.get(e) ?? { decidedFor: null, approach: false, rematch: false, lastAdoptKey: '', lastWalkKey: '' }
  searchFrameState.set(e, st)
  let approached = false
  let owned: ReadonlySet<WireId> | null = null
  if (best !== null && bestMismatch(e, best, pinned)) {
    if (st.decidedFor !== best || st.rematch) {
      const live = liveScoreAt(e)
      const EPS = 1e-6 * (Math.abs(live) + 1)
      if (live < best.score - EPS) {
        search.adoptLive(e, live)
        st.approach = false
      } else {
        st.approach = best.score < live - EPS
      }
      st.decidedFor = best
      st.rematch = false
    }
    if (st.approach) {
      owned = approachStep(e, best, pinned)
      approached = true
    }
  } else {
    st.decidedFor = best
    st.approach = false
    st.rematch = true
  }
  // WALK REST CERTIFICATE (exact-snapshot, self-healing — the same pattern as
  // the interactive rest certificate): the walk is a deterministic function
  // of body poses + wire nets + frame/scale, so if the LAST walk on exactly
  // this state moved nothing, re-running it is a proven no-op — and at rest
  // it was the whole frame cost (measured 46 ms/frame of re-derived seeds,
  // gates, separation grids, and tangent graphs concluding "nothing to do").
  // Any mutation from any path changes the key and the walk resumes.
  const walkKey = approached ? '' : liveKey(e)
  const walked = !approached && walkKey === st.lastWalkKey ? false : walkWires(e, true, owned)
  st.lastWalkKey = !walked && !approached ? walkKey : ''
  const acted = approached || walked
  if (!acted) {
    // live rest: offer the layout to the searcher once per configuration
    const key = liveKey(e)
    if (key !== st.lastAdoptKey) {
      st.lastAdoptKey = key
      const live = liveScoreAt(e)
      const b = search.best()
      if (b === null || live < b.score - 1e-6 * (Math.abs(live) + 1)) search.adoptLive(e, live)
    }
  }
  recomputeRegions(e)
  e.tick++
  return acted || search.searching
}

export function settleStep(e: Engine, pinned: ReadonlySet<string> | null = null): boolean {
  recomputeRegions(e)
  if (e.frame === null) establishFrame(e)

  const search = LAYOUT_SEARCH.get(e)
  if (search !== undefined) return searchedFrame(e, pinned, search)

  let moved = operatorStep(e, pinned)
  moved = walkWires(e) || moved
  recomputeRegions(e)
  e.tick++
  return moved
}

/** Run a tick budget of strict descent, bracketed by the DISCRETE construction-
    time legality projection (the only place `resolveOverlaps` runs).

    The LEADING projection is load-bearing, not decorative. The spiral seed
    (mkEngine, radial spacing 5 wu against ~6.5 wu disc radii) lands nodes deeply
    overlapping, and under the plan-23 UNCAPPED sibling barrier a dense-overlap
    configuration is a coordinate-descent TRAP: every single-DOF axis step out of
    one overlap lands in another, so the strict gate can find no downhill move and
    the descent FALSE-RESTS at a high-energy stalled state instead of separating
    the discs (measured plusComm@20: the un-projected descent flatlines at total E
    3.92e6 / cE 3.90e6 by tick ~700 and never recovers; the trailing projection
    then drops it to 6.7e4 in one discrete step — proof the flat state was a
    coordinate-descent stall, not an energy minimum). Projecting the SEED onto the
    feasible set BEFORE the descent — plan 23's sanctioned "one-time projection at
    construction, a discrete event outside the descent" — gives the gate a legal
    start (cE 2.9e4) from which it descends smoothly and rests by ~200 ticks
    (measured), drift → 0. Without it, no tick budget converges: the descent is
    wedged the whole time and only the final projection moves anything, leaving an
    unconverged tail (the drift the plan-23 close-out mismeasured as rest).

    The TRAILING projection remains the at-rest guarantee for a layout an external
    rewrite constructs overlapping after the descent has run.

    `ticks` is a CAP, not a fixed schedule: the descent stops the sweep AFTER the
    first that changes nothing (a proven fixed point — see descentSweep), so a
    settled diagram terminates in far fewer ticks than the backstop budget. Stopping
    there is bit-identical to burning the full budget, since every skipped sweep
    would have been a no-op. Returns the number of ticks actually run. */
export function settle(e: Engine, ticks: number): number {
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e) // fix the frame from the legal seed, before any settling
  let used = 0
  for (let t = 0; t < ticks; t++) { used++; if (!settleStep(e)) break }
  recomputeRegions(e)
  resolveOverlaps(e)
  return used
}
