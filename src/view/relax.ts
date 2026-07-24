import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, LegShape, WireLeg, WireLegEnd, WireView, StoredFrame } from './engine'
import { mkEngine, subtreeCarriers, worldBindAnchor, resolveLeg, traceLeg, frameSlots, resolvedFrameSlot, FRAME_MARGIN } from './engine'
import { ELASTICA, QN, mkLegCache } from './elastica'
import type { LegCache } from './elastica'

/** Live-build marker for serving-path verification (2026-07-23). */
export const PHYSICS_REV = 'step-operator@2026-07-24b'
console.info('[physics] rev', PHYSICS_REV)

/** LIVE-TUNABLE wire ENERGY parameters (plan 22, promoted from the accepted
    round-10 demo's `P`). The leg's own tension/bend live in ELASTICA (the
    solver reads them); these are the terms beyond the leg — node clearance,
    wire↔wire separation, junction spread, ∃-tip standoff — plus the trust
    region. Defaults are the demo's first-pass values (re-derivable on the tune
    board). Wire↔node collision has NO semantic meaning (USER): the barrier is
    SOFT (finite depth), so stressed geometry passes through; only at-rest
    overlap is forbidden. */
export const WIREP = {
  /** node clearance line-integral slope (pushes wires off discs they cross) */
  clearSlope: 3.2,
  /** clearance reach beyond a disc's radius */
  clearMargin: 5,
  /** wire↔wire separation slope (transverse crossings cheap, co-running dear) */
  sepSlope: 1.4,
  /** wire↔wire separation radius */
  sepR: 5,
  /** ∃-tip standoff radius (the dot never sinks into its own wire) */
  standoffR: 8,
  /** wire↔FRAME containment stiffness: an UNCAPPED quadratic penalty on any wire
      sample OUTSIDE the border (USER STANDING LAW — nothing is ever drawn outside
      the frame). Uncapped so under gated descent it dominates a leg's tension·L,
      including a blind-cone fallback arc: a wire that would arc outside is instead
      pulled in — the escape is the NODE rotating / the hub migrating so the leg
      stays a short curve inside (Task-3/4 dynamics), never a diagram-wrapping arc. */
  frameContain: 30,
  /** trust region: max per-tick motion of any wire DOF (continuity law) */
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
  /** scope-ring containment on ∃ tips: slope must exceed wire pull (1–2) */
  ringSlope: 8,
  ringBand: 4,
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
    const discs: Disc[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      discs.push({ c: b.pos, r: b.discR * e.scale, mid })
    }
    for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius + REGION_PAD * 0.8 * e.scale, sub: c })
    if (discs.length === 0) {
      // only a contentless sheet reaches here (empty leaf regions carry an
      // anchor body)
      e.regions.set(rid, { center: { x: 0, y: 0 }, radius: 10 * e.scale, support: [] })
      continue
    }
    const mec = minimalEnclosingCircle(discs)
    e.regions.set(rid, {
      center: mec.center,
      radius: Math.max(mec.radius + REGION_PAD * e.scale, 10 * e.scale),
      support: mec.support.map((m) => (m.mid !== undefined ? { mid: m.mid } : { sub: m.sub! })),
    })
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
    if (b.kind === 'end') continue
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
    for (let k = 0; k < w.branches.length; k++) w.branches[k] = map(w.branches[k]!)
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
export function seedProject(e: Engine, noScale = false): void {
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e)
  if (!noScale) { applyContentScale(e); clampContentToFrame(e) }
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
  // Wire-owned bodies (homed ∃ ends / ∀ tips): hard legality is SEMANTIC
  // for REGIONS — a root-scoped ∃ inside a cut circle reads as the wrong
  // quantifier scope, so region pairs keep projecting them. Disc-vs-disc
  // spacing is NOT semantic for a wire-end dot: the wire's own barrier
  // handles disc clearance, and a hard PACE.sibGap projection against soft
  // wire tension parks the dot 15 wu out and cycles forever (measured).
  const wireOwnedP = new Set<string>()
  for (const b of e.bodies.values()) if (b.kind === 'end') wireOwnedP.add(b.id)
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
        // wire-owned dots skip DISC pairs (wire barrier's job); region
        // pairs still project them (scope legality)
        const aOwned = A.sub === null && wireOwnedP.has(A.id)
        const bOwned = B.sub === null && wireOwnedP.has(B.id)
        if ((aOwned && B.sub === null) || (bOwned && A.sub === null)) continue
        const ca = centerOf(A), cb = centerOf(B)
        const dx = cb.x - ca.x, dy = cb.y - ca.y
        const dist = Math.hypot(dx, dy)
        // a wire-owned dot vs a REGION: legality is center-outside-circle
        // only — the ∀ tip LIVES in the ring annulus (loose-ends law), and
        // demanding content spacing (disc + sibGap) put the projection wall
        // inside the territory the ring energy owns: tension pressed the
        // tip into the wall every tick and the reaction walked the whole
        // assembly across the sheet forever (measured 0.05 wu/tick, E
        // oscillating, never resting)
        const need = aOwned && B.sub !== null ? B.r
          : bOwned && A.sub !== null ? A.r
          : A.r + B.r + PACE.sibGap * e.scale
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

// ---- the wire energy (plan 22): every term of the demo's energy(), same
// constants, evaluated over the massless-elastica legs. The DOF (bodies, hub
// points, arrival angles) descend −∇E by MOMENTUM; the gradient is central
// differences over these terms, localized (only the legs a DOF touches are
// re-solved, everything else reads its cached shape) so a probe is cheap. ----

/** Node clearance saturating potential: gradient ramps 0→clearSlope over the
    outer half of the clearance zone, constant clearSlope inside (finite depth
    — the SOFT barrier that lets stressed wires pass through). */
function clearU(d: number, R: number): number {
  if (d >= R) return 0
  const h = R / 2
  if (d >= h) { const t = (R - d) / h; return (WIREP.clearSlope * h * t * t) / 2 }
  return (WIREP.clearSlope * h) / 2 + WIREP.clearSlope * (h - d)
}

/** ∃-tip standoff potential (C1, radius standoffR, slope 2·tension — dominates
    the single-tension pull on an endpoint so the dot never sinks into its own
    wire; an energy term, never a position clamp). */
function standoffU(d: number, sc: number): number {
  const R = WIREP.standoffR * sc
  if (d >= R) return 0
  const h = R / 2, slope = 2 * ELASTICA.tension
  if (d >= h) { const t = (R - d) / h; return (slope * h * t * t) / 2 }
  return (slope * h) / 2 + slope * (h - d)
}

/** A disc for the clearance integral (node bodies only; junction dots are not
    discs). Holds the live body so a probe that moves it reads the new centre. */
type DiscRec = { readonly id: string; readonly body: Body; readonly r: number }

/** The node clearance line integral of one leg's samples against near discs —
    the own end discs exempt near their rim by an arc-distance ramp (the wire
    starts ON the rim heading outward and legitimately passes through there). */
function legClearance(samples: readonly Vec2[], L: number, ownA: string | null, ownB: string | null, near: readonly DiscRec[], sc: number): number {
  if (near.length === 0) return 0
  const ds = L / QN
  let E = 0
  for (let k = 1; k < samples.length; k++) {
    const s = samples[k]!
    for (const D of near) {
      const R = D.r + WIREP.clearMargin * sc
      const dx = s.x - D.body.pos.x, dy = s.y - D.body.pos.y
      const d = Math.hypot(dx, dy)
      if (d >= R) continue
      let m = 1
      if (D.id === ownA || D.id === ownB) {
        const arc = D.id === ownA ? k * ds : (samples.length - 1 - k) * ds
        m = Math.max(0, Math.min(1, (arc - R) / R))
      }
      E += m * clearU(d, R) * ds
    }
  }
  return E
}

/** Wire↔FRAME containment: the summed squared overshoot of a leg/trunk's samples
    past the fixed border (USER STANDING LAW — nothing drawn outside the frame).
    Uncapped so the gate never rests with a wire arcing outside; 0 with no frame. */
function legFrameE(samples: readonly Vec2[], f: Engine['frame']): number {
  if (f === null) return 0
  const maxX = f.center.x + f.half, minX = f.center.x - f.half
  const maxY = f.center.y + f.half, minY = f.center.y - f.half
  let E = 0
  for (const s of samples) {
    let o = 0
    if (s.x > maxX) o += s.x - maxX; else if (s.x < minX) o += minX - s.x
    if (s.y > maxY) o += s.y - maxY; else if (s.y < minY) o += minY - s.y
    if (o > 0) E += o * o
  }
  return WIREP.frameContain * E
}

/** A leg's own energy: tension·L + bend closed form + arrival well (all inside
    the solve) + its clearance line integral. Every leg is the true θ-quadratic
    (the free-end candidate grid keeps free-end legs representable up to ~144°
    behind; the only bound is the numerical L-cap in resolveLeg). NO blend/second
    shape family — the demo shipped without one and it is strictly preferable. */
function legIntrinsicE(shape: LegShape, samples: readonly Vec2[], near: readonly DiscRec[], sc: number): number {
  const { c1, c2, L, well } = shape.sol
  return ELASTICA.tension * L
    + (ELASTICA.bend * (c1 * c1 + 2 * c1 * c2 + (4 / 3) * c2 * c2)) / L
    + well
    + legClearance(samples, L, shape.ownA, shape.ownB, near, sc)
}

/** Wire↔wire separation between two legs' samples (every 3rd point: transverse
    crossings spend almost no arc in the band, co-running legs pay). The band
    radius scales with the content-fill scale so co-routed wires stay separated in
    proportion to the drawn size. */
function sepPair(sa: readonly Vec2[], sb: readonly Vec2[], sc: number): number {
  const R = WIREP.sepR * sc
  let E = 0
  for (let k = 0; k < sa.length; k += 3) for (let l = 0; l < sb.length; l += 3) {
    const dx = sa[k]!.x - sb[l]!.x, dy = sa[k]!.y - sb[l]!.y
    const d = Math.hypot(dx, dy)
    if (d < R) E += (WIREP.sepSlope * (R - d) * (R - d)) / R
  }
  return E
}

/** The ∃-tip standoff energy: the loose end floats to a scope standoff from its
    single port. Applies ONLY to a dangling ∃ (exactly one bind + its END body); a
    ∀ via (binds ≥ 2) is positioned by its tree + scope homing, no standoff. */
function tipStandoffE(e: Engine, w: WireView): number {
  if (w.endBodyId === null || w.binds.length !== 1) return 0
  const tip = e.bodies.get(w.endBodyId)!
  // the standoff is measured from the tip to its wire's port anchor (the
  // first — and only — bind of a dangling ∃)
  const bd = w.binds[0]
  if (bd === undefined) return 0
  const a = worldBindAnchor(e, e.bodies.get(bd.body)!, bd.key)
  return standoffU(Math.hypot(tip.pos.x - a.x, tip.pos.y - a.y), e.scale)
}

/** Total WIRE energy of the engine (leg intrinsic + clearance, ∃-tip standoff,
    wire↔wire separation) — one half of `totalEnergy`; `contentEnergy` is the other.
    Junction geometry carries no separate term: a branch/hub leg's tangents are free
    per-leg DOFs already scored inside its intrinsic energy (tension + bend + arrival
    well). A boundary leg reaches its FIXED frame slot as an ordinary leg endpoint (the
    slot is a fixed point, resolved inside resolveLeg), so there is no separate
    exit→slot attraction term. Uses the full memoryless grid solve for every leg. */
export function wireEnergy(e: Engine): number {
  const sc = e.scale
  const discs: DiscRec[] = [...e.bodies.values()]
    .filter((b) => b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom')
    .map((b) => ({ id: b.id, body: b, r: b.discR * sc }))
  // resolve + trace every leg once
  const legSamples: { wid: string; samples: Vec2[] }[] = []
  let E = 0
  for (const [wid, w] of e.wires) {
    for (const leg of w.legs) {
      const shape = resolveLeg(e, w, leg, leg.cache)
      const samples: Vec2[] = []
      traceLeg(shape, samples, QN)
      const near = discs.filter((D) => bboxNear(samples, D.body.pos, D.r + WIREP.clearMargin * sc))
      E += legIntrinsicE(shape, samples, near, sc) + legFrameE(samples, e.frame)
      legSamples.push({ wid, samples })
    }
    E += tipStandoffE(e, w)
  }
  // wire↔wire separation (different wires only)
  for (let a = 0; a < legSamples.length; a++) {
    for (let b = a + 1; b < legSamples.length; b++) {
      if (legSamples[a]!.wid === legSamples[b]!.wid) continue
      E += sepPair(legSamples[a]!.samples, legSamples[b]!.samples, sc)
    }
  }
  return E
}

/** Whether a sample polyline's bounding box comes within `r` of a point. */
function bboxNear(samples: readonly Vec2[], p: Vec2, r: number): boolean {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
  for (const s of samples) {
    if (s.x < minX) minX = s.x
    if (s.y < minY) minY = s.y
    if (s.x > maxX) maxX = s.x
    if (s.y > maxY) maxY = s.y
  }
  return p.x >= minX - r && p.x <= maxX + r && p.y >= minY - r && p.y <= maxY + r
}

/** Whether two sample polylines' bounding boxes come within `r` of each other. */
function bboxOverlap(sa: readonly Vec2[], sb: readonly Vec2[], r: number): boolean {
  let aminX = Infinity, aminY = Infinity, amaxX = -Infinity, amaxY = -Infinity
  for (const s of sa) { if (s.x < aminX) aminX = s.x; if (s.y < aminY) aminY = s.y; if (s.x > amaxX) amaxX = s.x; if (s.y > amaxY) amaxY = s.y }
  let bminX = Infinity, bminY = Infinity, bmaxX = -Infinity, bmaxY = -Infinity
  for (const s of sb) { if (s.x < bminX) bminX = s.x; if (s.y < bminY) bminY = s.y; if (s.x > bmaxX) bmaxX = s.x; if (s.y > bmaxY) bmaxY = s.y }
  return aminX - r <= bmaxX && bminX - r <= amaxX && aminY - r <= bmaxY && bminY - r <= amaxY
}

/** Scope containment (soft): a finite-depth ring barrier keeping a wire-owned
    dot (∃ tip, ∀ hub) OUTSIDE each child region circle of its home region — it
    lives in its scope, never sunk into a nested cut. The hard legality is the
    projection; this is the field that parks the dot in the annulus without a
    standing contact cycle. */
function homedScopeE(e: Engine, body: Body): number {
  const band = PACE.ringBand * e.scale
  let E = 0
  for (const child of e.childrenOf.get(body.region) ?? []) {
    const g = e.regions.get(child)
    if (g === undefined) continue
    const rr = g.radius + body.discR * e.scale
    const dd = Math.hypot(body.pos.x - g.center.x, body.pos.y - g.center.y)
    if (dd >= rr + band) continue
    const pen = rr + band - dd
    E += (PACE.ringSlope / 2) * Math.min(pen, band) * pen
  }
  return E
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
      if (b.kind === 'end') continue
      items.push({ r: b.discR * sc, c: b.pos })
    }
    for (const cId of e.childrenOf.get(rid)!) { const g = e.regions.get(cId)!; items.push({ r: g.radius, c: g.center }) }
    for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
      const A = items[i]!, B = items[j]!
      const dist = Math.max(Math.hypot(A.c.x - B.c.x, A.c.y - B.c.y), 1)
      E += sibU(dist - A.r - B.r, sc)
    }
  }
  // scope-ring confines ∃ tips / ∀ via-body hubs to their scope
  for (const b of e.bodies.values()) if (b.kind === 'end') E += homedScopeE(e, b)
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
  const owned = b.kind === 'end'
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
    if (owned || o.kind === 'end') continue // disc-vs-dot pairs: wire barrier's job
    push(o.pos.x, o.pos.y, (b.discR + o.discR) * sc + PACE.sibGap * sc)
  }
  for (const cId of e.childrenOf.get(b.region)!) {
    const g = e.regions.get(cId)!
    push(g.center.x, g.center.y, owned ? g.radius : b.discR * sc + g.radius + PACE.sibGap * sc)
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
    cuts it IS inside) are exempt, as is a wire-owned dot's disc clearance (the wire
    barrier owns that) — a dot only clears the circle itself. */
export function clampDragToFeasible(e: Engine, b: Body, p: Vec2): Vec2 {
  const ancestors = new Set<RegionId>()
  for (let r = b.region; ;) {
    ancestors.add(r)
    const reg = e.d.regions[r]!
    if (reg.kind === 'sheet') break
    r = reg.parent
  }
  const owned = b.kind === 'end'
  let x = p.x, y = p.y
  for (const [rid, g] of e.regions) {
    if (ancestors.has(rid) || e.d.regions[rid]!.kind === 'sheet') continue
    const need = owned ? g.radius : b.discR * e.scale + g.radius + PACE.sibGap * e.scale
    const dx = x - g.center.x, dy = y - g.center.y, d = Math.hypot(dx, dy)
    if (d >= need) continue
    const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
    x = g.center.x + ux * need; y = g.center.y + uy * need
  }
  // the fixed frame is a hard wall (plan 24): a drag meets the edge and stops —
  // the node never crosses out and the frame never grows to chase the cursor
  const c0 = clampToFrame(e, b, { x, y })
  x = c0.x; y = c0.y
  // CUT hard wall (USER 2026-07-06): the border contains the CUTS too, not just the
  // discs. The dragged body is PINNED (the settle gate cannot relax it), so if its
  // own cut's circle would exit the border, pull the body in until every ancestor
  // region circle fits — the cut stops at the wall, so the dragged node stops with
  // it. Iterated because moving the body in shrinks/shifts the derived circle.
  const f = e.frame
  if (f !== null && b.kind !== 'end') {
    const saved = b.pos
    const dirty = new Set<RegionId>([b.region])
    for (let it = 0; it < 8; it++) {
      b.pos = { x, y }
      recomputeRegions(e, dirty)
      let rt = 0, lf = 0, bt = 0, tp = 0
      for (const rid of ancestors) {
        if (e.d.regions[rid]!.kind === 'sheet') continue
        const g = e.regions.get(rid)
        if (g === undefined) continue
        rt = Math.max(rt, g.center.x + g.radius - (f.center.x + f.half))
        lf = Math.max(lf, (f.center.x - f.half) - (g.center.x - g.radius))
        bt = Math.max(bt, g.center.y + g.radius - (f.center.y + f.half))
        tp = Math.max(tp, (f.center.y - f.half) - (g.center.y - g.radius))
      }
      const dx = rt > lf ? -rt : lf, dy = bt > tp ? -bt : tp
      if (Math.abs(dx) < 0.05 && Math.abs(dy) < 0.05) break
      const c = clampToFrame(e, b, { x: x + dx, y: y + dy })
      x = c.x; y = c.y
    }
    b.pos = saved
    recomputeRegions(e, dirty)
  }
  return { x, y }
}

/** Finite-difference probe scale (drawn units): each coordinate is probed at
    h = HX / m so the DRAWN perturbation is uniform across unlike coordinates. */
const HX = 0.02

// ═══════════ THE STEP OPERATOR — simultaneous trust-bounded descent ═══════════
// docs/superpowers/specs/2026-07-24-step-operator-design.md (ratified). One
// deterministic, MEMORYLESS step per frame: the M-metric gradient of the ONE
// total energy over ALL coordinates at once, a single simultaneous trial along
// −∇E with drawn-displacement norm Δ, legality projection, accepted iff the
// TRUE total E strictly drops; on rejection Δ halves; when nothing is accepted
// at the smallest Δ the frame is a proven, bit-stable rest.
//  · UNIFORM LOCALITY (user law 2026-07-24): every coordinate — node rotation
//    included — moves under the same Δ budget, measured as drawn displacement
//    (the metric M). No coordinate line-searches to its own optimum; the
//    per-DOF expanding-search gates this replaces were per-coordinate
//    approximate exact-minimization, the provably dangerous scheme.
//  · Stiff barriers shorten steps automatically: a wall ahead makes the full-Δ
//    trial RAISE E → rejected → Δ halves. Proportionate transients are an
//    operator property, not a tuning (IPC's structure).
//  · The accept test evaluates the full true E at the one trial state — there
//    is no localized stale proxy to conveyor against, structurally.
//  · Chart crossing is arithmetic (design §4): wire coordinates are chart-local
//    (root branch absolute, internal edges as (ℓ, θ), branch tangents); a trial
//    driving ℓ through 0 is EXPRESSED in the charts incident to that face (the
//    reparametrized current chart and its two NNI re-pairings, tangents carried,
//    the collapsed stub's angle quotiented) and the trial takes the steepest —
//    tangent-cone descent on the glued space, inside the one gate. No detection
//    window, no crossing event, no crossing-specific accept path.

/** Δ ladder depth: Δmin = Δmax / 2^8. A frame rejected at Δmin is a proven
    rest (deterministic operator + unchanged state ⇒ every later frame rejects
    identically). */
const DELTA_HALVINGS = 8

type TreeEdge = readonly [number, number]

/** Tree-node index of a branch-wire leg end: binds 0..nBind-1, slots nBind..nT-1,
    branch points nT.. (the buildJunctionTree convention). */
function endNodeIndex(end: WireLegEnd, nBind: number, nT: number): number {
  switch (end.kind) {
    case 'bind': return end.i
    case 'slot': return nBind + end.i
    case 'branch': return nT + end.i
    default: throw new Error(`a branch wire has a ${end.kind} leg end`)
  }
}
function nodeEnd(node: number, nBind: number, nT: number): WireLegEnd {
  if (node < nBind) return { kind: 'bind', i: node }
  if (node < nT) return { kind: 'slot', i: node - nBind }
  return { kind: 'branch', i: node - nT }
}

/** The current tree edges of a branch wire (all its legs are tree edges), in tree
    indices; and the world terminal positions (binds then slots) in tree order. */
function wireEdges(w: WireView, nBind: number, nT: number): TreeEdge[] {
  return w.legs.map((l) => [endNodeIndex(l.a, nBind, nT), endNodeIndex(l.b, nBind, nT)] as TreeEdge)
}
function wireTerminals(e: Engine, w: WireView): Vec2[] {
  const pos: Vec2[] = w.binds.map((bd) => worldBindAnchor(e, e.bodies.get(bd.body)!, bd.key))
  for (const si of w.slots) { const s = resolvedFrameSlot(e, si); pos.push(s !== null ? s.point : { x: 0, y: 0 }) }
  return pos
}

/** The two NNI re-pairings across an internal (branch–branch) edge — or [] unless
    both endpoints are degree-3 (the "two alternative pairings" case; a converged
    soap-film branch point is degree 3). Edges are UNORDERED. */
function nniAlternatives(edges: readonly TreeEdge[], nT: number, ei: number): TreeEdge[][] {
  const [bi, bj] = edges[ei]!
  if (bi < nT || bj < nT) return []
  const nbrs = (v: number): number[] => edges.flatMap(([a, b]) => (a === v ? [b] : b === v ? [a] : []))
  const biOthers = nbrs(bi).filter((x) => x !== bj)
  const bjOthers = nbrs(bj).filter((x) => x !== bi)
  if (biOthers.length !== 2 || bjOthers.length !== 2) return []
  const Q = biOthers[1]!, R = bjOthers[0]!, S = bjOthers[1]!
  const swap = (fromBi: number, fromBj: number): TreeEdge[] => edges.map(([a, b]) => {
    const is = (x: number, y: number): boolean => (a === x && b === y) || (a === y && b === x)
    if (is(bi, fromBi)) return [bj, fromBi] as TreeEdge
    if (is(bj, fromBj)) return [bi, fromBj] as TreeEdge
    return [a, b] as TreeEdge
  })
  return [swap(Q, R), swap(Q, S)]
}

/** One coordinate of Q, as the operator sees it: accessors into the live state
    plus its metric weight m (drawn displacement per unit coordinate — positions
    1, body rotation its drawn radius, an edge angle its length, a leg tangent
    its leg's length). Wire edge coordinates write through a reconstruction that
    keeps `w.branches` consistent. */
type Coord = {
  get(): number
  set(v: number): void
  readonly m: number
  /** localized energy for the gradient probe (the terms this coordinate touches;
      the untouched remainder cancels in the difference). Exact solves, always. */
  localE(): number
}

/** Chart-local parametrization of one wire's manifold point, built fresh each
    frame from the stored (T, b, τ): root branch absolute, each further branch
    reached by an internal edge's (ℓ, θ) in BFS order. `reconstruct` writes the
    implied branch positions back to `w.branches`; a trial that drives some
    ℓ < 0 has passed the face F_{T,e} and is resolved by `resolveCharts`. */
type WireParam = {
  readonly w: WireView
  readonly nBind: number
  readonly nT: number
  root: { x: number; y: number }
  /** BFS-oriented internal edges: child branch index (into w.branches), parent
      branch index, and the chart-local coordinates. */
  readonly edges: { child: number; parent: number; l: number; th: number }[]
  reconstruct(): void
}

function mkWireParam(w: WireView): WireParam | null {
  if (w.branches.length === 0) return null
  const nBind = w.binds.length
  const nT = nBind + w.slots.length + (w.endBodyId !== null ? 1 : 0)
  // branch-adjacency from the internal (branch–branch) legs
  const adj = new Map<number, number[]>()
  for (const leg of w.legs) {
    if (leg.a.kind !== 'branch' || leg.b.kind !== 'branch') continue
    const a = leg.a.i, b = leg.b.i
    ;(adj.get(a) ?? adj.set(a, []).get(a)!).push(b)
    ;(adj.get(b) ?? adj.set(b, []).get(b)!).push(a)
  }
  const edges: WireParam['edges'] = []
  const seen = new Set<number>([0])
  const queue = [0]
  while (queue.length > 0) {
    const parent = queue.shift()!
    for (const child of adj.get(parent) ?? []) {
      if (seen.has(child)) continue
      seen.add(child); queue.push(child)
      const pp = w.branches[parent]!, cp = w.branches[child]!
      edges.push({ child, parent, l: Math.hypot(cp.x - pp.x, cp.y - pp.y), th: Math.atan2(cp.y - pp.y, cp.x - pp.x) })
    }
  }
  const param: WireParam = {
    w, nBind, nT,
    root: { ...w.branches[0]! },
    edges,
    reconstruct(): void {
      w.branches[0] = { ...param.root }
      for (const ed of param.edges) {
        const pp = w.branches[ed.parent]!
        w.branches[ed.child] = { x: pp.x + ed.l * Math.cos(ed.th), y: pp.y + ed.l * Math.sin(ed.th) }
      }
    },
  }
  return param
}

/** Build the leg set of a candidate adjacency at the CURRENT positions: terminal
    legs carry their tangents unchanged (φ is the identity on intrinsic data);
    internal edges re-emerge with chord tangents (the collapsed stub's angle is
    quotiented). `srcLegs` supplies the carried terminal tangents. */
function buildChartLegs(e: Engine, w: WireView, nBind: number, nT: number, cand: readonly TreeEdge[], srcLegs: readonly WireLeg[]): WireLeg[] {
  const termPos = wireTerminals(e, w)
  const posOf = (node: number): Vec2 => {
    if (node >= nT) return w.branches[node - nT]!
    if (node < termPos.length) return termPos[node]!
    return e.bodies.get(w.endBodyId!)!.pos // END terminal (tree order: binds, slots, end)
  }
  const termTan = new Map<number, { angA: number; angB: number }>()
  for (const leg of srcLegs) {
    const t = leg.a.kind !== 'branch' ? endNodeIndex(leg.a, nBind, nT)
      : leg.b.kind !== 'branch' ? endNodeIndex(leg.b, nBind, nT) : -1
    if (t >= 0) termTan.set(t, { angA: leg.angA, angB: leg.angB })
  }
  return cand.map(([u0, v0]) => {
    const [u, v] = u0 < v0 ? [u0, v0] : [v0, u0]
    const endU = nodeEnd(u, nBind, nT), endV = nodeEnd(v, nBind, nT)
    if (u < nT) {
      const t = termTan.get(u) ?? { angA: 0, angB: 0 }
      return { a: endU, b: endV, angA: t.angA, angB: t.angB, cache: mkLegCache() }
    }
    const chord = Math.atan2(posOf(v).y - posOf(u).y, posOf(v).x - posOf(u).x)
    return { a: endU, b: endV, angA: chord, angB: chord, cache: mkLegCache() }
  })
}

/** The candidate adjacencies incident to the face(s) a trial crossed: the
    current adjacency (the re-parametrized chart) plus, per crossed internal
    edge (child, parent branch indices), its two NNI re-pairings. On the glued
    manifold the crossed point lies in ALL of these charts — its energy is
    their minimum, and a committed trial takes the steepest. */
function crossedAlternatives(w: WireView, nBind: number, nT: number, crossed: readonly { child: number; parent: number }[]): TreeEdge[][] {
  const edges = wireEdges(w, nBind, nT)
  const out: TreeEdge[][] = []
  for (const c of crossed) {
    const ei = edges.findIndex(([a, b]) =>
      (a === nT + c.child && b === nT + c.parent) || (a === nT + c.parent && b === nT + c.child))
    if (ei < 0) continue
    out.push(...nniAlternatives(edges, nT, ei))
  }
  return out
}

/** Express a trial whose internal edge coordinate went NEGATIVE in the charts
    incident to the crossed face and keep the steepest: candidates are the
    current chart as re-parametrized (positions already reflect the passage —
    ℓ<0 ≡ (|ℓ|, θ+π)) and the NNI re-pairings at the SAME branch positions.
    Deterministic candidate order; strict improvement to switch. Part of ONE
    trial evaluation — the ordinary gate accepts or rejects whatever this
    resolves to. */
function resolveCharts(e: Engine, w: WireView, nBind: number, nT: number, crossed: readonly { child: number; parent: number }[]): void {
  const alts = crossedAlternatives(w, nBind, nT, crossed)
  if (alts.length === 0) return
  const savedLegs = [...w.legs]
  let bestE = totalEnergy(e)
  let bestLegs: WireLeg[] | null = null
  for (const alt of alts) {
    const legs = buildChartLegs(e, w, nBind, nT, alt, savedLegs)
    w.legs.length = 0; for (const l of legs) w.legs.push(l)
    const E = totalEnergy(e)
    if (E < bestE) { bestE = E; bestLegs = legs }
    w.legs.length = 0; for (const l of savedLegs) w.legs.push(l)
  }
  if (bestLegs !== null) { w.legs.length = 0; for (const l of bestLegs) w.legs.push(l) }
}

/**
 * THE per-frame step (design §2): gradient → one simultaneous bounded trial →
 * project → accept iff the true total E strictly drops, halving Δ on rejection.
 * Returns whether the frame changed state; `false` is a PROVEN bit-stable rest
 * (memoryless + deterministic: the next frame recomputes identically and
 * rejects identically). `pinned` bodies' positions are constraints (rotation
 * stays free — USER 2026-07-07).
 */
function operatorStep(e: Engine, pinned: ReadonlySet<string> | null): boolean {
  const sc = e.scale
  recomputeRegions(e)
  const discs: DiscRec[] = []
  for (const b of e.bodies.values()) if (b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom') discs.push({ id: b.id, body: b, r: b.discR * sc })

  // ── frame snapshot of every leg (shapes, samples, neighbourhoods) for the
  // LOCALIZED gradient probes (only the probed coordinate's terms re-solve;
  // everything else reads its frame-start samples — exact for a single-
  // coordinate perturbation, since untouched terms cancel in the difference).
  type LegRec = { readonly wid: string; readonly w: WireView; readonly leg: WireLeg; readonly gi: number; readonly shape: LegShape; readonly samples: Vec2[]; readonly near: DiscRec[] }
  const cullR = (WIREP.clearMargin + WIREP.travelCap) * sc
  const legRecs: LegRec[] = []
  const legsOfWire = new Map<string, LegRec[]>()
  for (const [wid, w] of e.wires) {
    const arr: LegRec[] = []
    for (const leg of w.legs) {
      const shape = resolveLeg(e, w, leg)
      const samples: Vec2[] = []
      traceLeg(shape, samples, QN)
      const near = discs.filter((D) => bboxNear(samples, D.body.pos, D.r + cullR))
      const rec: LegRec = { wid, w, leg, gi: legRecs.length, shape, samples, near }
      legRecs.push(rec); arr.push(rec)
    }
    legsOfWire.set(wid, arr)
  }
  const bindLegs = new Map<string, LegRec[]>()
  for (const r of legRecs) for (const own of [r.shape.ownA, r.shape.ownB]) {
    if (own === null) continue
    const a = bindLegs.get(own); if (a === undefined) bindLegs.set(own, [r]); else a.push(r)
  }
  for (const [wid, w] of e.wires) {
    if (w.endBodyId === null) continue
    const tips = (legsOfWire.get(wid) ?? []).filter((r) => r.leg.b.kind === 'end')
    const a = bindLegs.get(w.endBodyId); if (a === undefined) bindLegs.set(w.endBodyId, tips); else a.push(...tips)
  }
  const discNearLegs = new Map<string, LegRec[]>()
  for (const D of discs) discNearLegs.set(D.id, legRecs.filter((r) => bboxNear(r.samples, D.body.pos, D.r + cullR)))
  const sepCull = (WIREP.sepR + 2 * WIREP.travelCap) * sc
  const crossNear = new Map<number, LegRec[]>()
  for (const r of legRecs) crossNear.set(r.gi, legRecs.filter((o) => o.wid !== r.wid && bboxOverlap(r.samples, o.samples, sepCull)))

  const scratchSamples: Vec2[][] = []
  const probeCache = new Map<number, LegCache>()
  const cacheOf = (gi: number): LegCache => { let c = probeCache.get(gi); if (c === undefined) { c = mkLegCache(); probeCache.set(gi, c) } return c }
  // A touched leg's shape under a gradient probe. `warm` = the envelope-theorem
  // fixed-turn fast path (plan 22): CORRECT for the first-order gradient at the
  // base and ~15x cheaper than the grid scan — used for gradient probes only,
  // never for accepts (plan-23 measured warm accepts breaking monotonicity).
  // Free-end legs stay exact even in probes (the fixed-turn warm gradient points
  // wrong there — measured, an ∃ tip cycling E ±0.4 forever).
  // Probes are EXACT (the memoryless grid solve): the warm fixed-turn fast path
  // smooths away the grid-switch creases the one-sided gradient selection needs
  // — probing warm re-creates the phantom-gradient stall in disguise (measured:
  // rest at ≤50 ticks vs 754 with real descent remaining).
  const solveTouched = (r: LegRec): LegShape => resolveLeg(e, r.w, r.leg, cacheOf(r.gi))
  // localized energy of a touched-leg set (leg intrinsic incl. clearance + frame
  // containment + cross-wire separation + ∃-tip standoff + optionally the moved
  // disc's clearance against far legs). Gradient probes only — the ACCEPT test
  // never uses this (it evaluates the full true E).
  const localE = (touched: readonly LegRec[], farBody: Body | null): number => {
    let E = 0
    const touchedSet = new Set(touched.map((r) => r.gi))
    const probeSamples = new Map<number, Vec2[]>()
    touched.forEach((r, idx) => {
      const shape = solveTouched(r)
      const samp = scratchSamples[idx] ?? (scratchSamples[idx] = [])
      traceLeg(shape, samp, QN)
      probeSamples.set(r.gi, samp)
      E += legIntrinsicE(shape, samp, r.near, sc) + legFrameE(samp, e.frame)
    })
    for (const r of touched) {
      const samp = probeSamples.get(r.gi)!
      for (const o of crossNear.get(r.gi)!) {
        if (touchedSet.has(o.gi) && r.gi >= o.gi) continue
        E += sepPair(samp, touchedSet.has(o.gi) ? probeSamples.get(o.gi)! : o.samples, sc)
      }
    }
    if (farBody !== null) {
      const near1: DiscRec[] = [{ id: farBody.id, body: farBody, r: farBody.discR * sc }]
      for (const r of discNearLegs.get(farBody.id)!) {
        if (touchedSet.has(r.gi)) continue
        E += legClearance(r.samples, r.shape.sol.L, r.shape.ownA, r.shape.ownB, near1, sc)
      }
    }
    for (const r of touched) if (r.leg.b.kind === 'end') E += tipStandoffE(e, r.w)
    return E
  }

  // ── the coordinate list ──
  const coords: Coord[] = []
  const movedBodies: Body[] = []
  for (const b of e.bodies.values()) {
    const touched = bindLegs.get(b.id) ?? []
    const far = b.kind === 'anchor' || b.kind === 'end' ? null : b
    const dirty = new Set<RegionId>([b.region])
    const bodyLocalE = (): number => { recomputeRegions(e, dirty); return localE(touched, far) + contentEnergy(e) }
    if (pinned === null || !pinned.has(b.id)) {
      movedBodies.push(b)
      coords.push({ get: () => b.pos.x, set: (v) => { b.pos = { x: v, y: b.pos.y } }, m: 1, localE: bodyLocalE })
      coords.push({ get: () => b.pos.y, set: (v) => { b.pos = { x: b.pos.x, y: v } }, m: 1, localE: bodyLocalE })
    }
    // rotation: an ordinary coordinate under the same budget (2026-07-24 law —
    // the unlimited-spin ruling is superseded). Content is rotation-invariant.
    if (touched.length > 0 && b.localAnchor.size > 0) {
      coords.push({ get: () => b.theta, set: (v) => { b.theta = v }, m: Math.max(b.discR * sc, 1e-6), localE: () => localE(touched, null) })
    }
  }
  const params: WireParam[] = []
  for (const [wid, w] of e.wires) {
    const param = mkWireParam(w)
    if (param === null) continue
    params.push(param)
    const wLegs = legsOfWire.get(wid)!
    // The wire's probe energy on the GLUED manifold: while every chart
    // coordinate is interior (ℓ ≥ 0) this is the ordinary localized energy; a
    // probe that crosses a face (some ℓ < 0) lies in every chart incident to
    // that face, so its energy is the MINIMUM over their expressions. Without
    // this the ℓ-probe sees only the current chart's crossed-leg energy, the
    // one-sided slope at the face points uphill, and descent can never pass —
    // the observed impassable boundary at ℓ = 0 (squeezed wire never re-pairs).
    const chartLegsE = (legs: readonly WireLeg[]): number => {
      let E = 0
      const sampled: Vec2[][] = []
      for (const leg of legs) {
        const shape = resolveLeg(e, w, leg, leg.cache)
        const samples: Vec2[] = []
        traceLeg(shape, samples, QN)
        const near = discs.filter((D) => bboxNear(samples, D.body.pos, D.r + cullR))
        E += legIntrinsicE(shape, samples, near, sc) + legFrameE(samples, e.frame)
        sampled.push(samples)
      }
      for (const samp of sampled) {
        for (const o of legRecs) {
          if (o.wid === wid) continue
          if (bboxOverlap(samp, o.samples, sepCull)) E += sepPair(samp, o.samples, sc)
        }
      }
      return E + tipStandoffE(e, w)
    }
    const wireLocalE = (): number => {
      const crossed = param.edges.filter((ed) => ed.l < 0)
      if (crossed.length === 0) return localE(wLegs, null)
      let best = chartLegsE(w.legs)
      for (const alt of crossedAlternatives(w, param.nBind, param.nT, crossed)) {
        best = Math.min(best, chartLegsE(buildChartLegs(e, w, param.nBind, param.nT, alt, w.legs)))
      }
      return best
    }
    coords.push({ get: () => param.root.x, set: (v) => { param.root.x = v; param.reconstruct() }, m: 1, localE: wireLocalE })
    coords.push({ get: () => param.root.y, set: (v) => { param.root.y = v; param.reconstruct() }, m: 1, localE: wireLocalE })
    for (const ed of param.edges) {
      coords.push({ get: () => ed.l, set: (v) => { ed.l = v; param.reconstruct() }, m: 1, localE: wireLocalE })
      // the edge ANGLE is quotiented at the face (Fact 0.3): below the drawing
      // resolution it moves nothing and is omitted, exactly the quotient.
      if (Math.abs(ed.l) > 0.01) {
        coords.push({ get: () => ed.th, set: (v) => { ed.th = v; param.reconstruct() }, m: Math.abs(ed.l), localE: wireLocalE })
      }
    }
    for (const rec of wLegs) {
      const leg = rec.leg
      const mTan = Math.max(rec.shape.sol.L, 1e-6)
      if (leg.a.kind === 'branch') coords.push({ get: () => leg.angA, set: (v) => { leg.angA = v }, m: mTan, localE: () => localE([rec], null) })
      if (leg.b.kind === 'branch') coords.push({ get: () => leg.angB, set: (v) => { leg.angB = v }, m: mTan, localE: () => localE([rec], null) })
    }
  }

  // ── gradient at drawn-uniform probes h = HX/m, with ONE-SIDED derivative
  // selection: the energy is PIECEWISE-smooth (the leg solver's grid-scan argmin
  // switches candidates at creases), and rests sit ON kinks — a central
  // difference straddling a kink minimum reports a large phantom gradient whose
  // trial then ASCENDS the one-sided slope (measured: theta components alone
  // raised every trial +6.9·Δ at a rest whose central "gradient" was 9.8). Per
  // coordinate: keep the steeper strictly-descending side; a kink minimum (both
  // sides ascend) contributes ZERO — that coordinate genuinely rests. At smooth
  // points both slopes agree and this IS the central estimate. ──
  const g: number[] = new Array(coords.length).fill(0)
  // base values shared per localE closure: coordinates of one family (a body's
  // x and y, a wire's root pair) see the identical base energy, so it is
  // evaluated once per family, not once per coordinate.
  const baseMemo = new Map<Coord['localE'], number>()
  const baseOf = (c: Coord): number => {
    let v = baseMemo.get(c.localE)
    if (v === undefined) { v = c.localE(); baseMemo.set(c.localE, v) }
    return v
  }
  for (let i = 0; i < coords.length; i++) {
    const c = coords[i]!
    const v0 = c.get()
    const h = HX / c.m
    const e0 = baseOf(c)
    c.set(v0 + h); const ep = c.localE()
    c.set(v0 - h); const em = c.localE()
    c.set(v0)
    const slopeP = (ep - e0) / h // right one-sided derivative
    const slopeM = (e0 - em) / h // left one-sided derivative
    const descP = slopeP < 0, descM = slopeM > 0
    g[i] = descP && (!descM || -slopeP >= slopeM) ? slopeP : descM ? slopeM : 0
  }
  recomputeRegions(e)
  let gnorm2 = 0
  for (let i = 0; i < coords.length; i++) { const s = g[i]! / coords[i]!.m; gnorm2 += s * s }
  const gnorm = Math.sqrt(gnorm2)
  // ── snapshot for restore-on-reject ──
  const bodySnap = new Map<string, { pos: Vec2; theta: number }>()
  for (const b of e.bodies.values()) bodySnap.set(b.id, { pos: { ...b.pos }, theta: b.theta })
  const wireSnap = [...e.wires.values()].map((w) => ({
    w,
    branches: w.branches.map((p) => ({ ...p })),
    legs: [...w.legs],
    tans: w.legs.map((l) => ({ angA: l.angA, angB: l.angB })),
  }))
  const paramSnap = params.map((p) => ({ root: { ...p.root }, edges: p.edges.map((ed) => ({ ...ed })) }))
  const restore = (): void => {
    for (const b of e.bodies.values()) { const s = bodySnap.get(b.id)!; b.pos = { ...s.pos }; b.theta = s.theta }
    for (const ws of wireSnap) {
      ws.w.branches.length = 0; for (const p of ws.branches) ws.w.branches.push({ ...p })
      ws.w.legs.length = 0; for (const l of ws.legs) ws.w.legs.push(l)
      ws.legs.forEach((l, i) => { l.angA = ws.tans[i]!.angA; l.angB = ws.tans[i]!.angB })
    }
    params.forEach((p, i) => {
      p.root = { ...paramSnap[i]!.root }
      p.edges.forEach((ed, j) => { ed.l = paramSnap[i]!.edges[j]!.l; ed.th = paramSnap[i]!.edges[j]!.th })
    })
  }

  const E0 = totalEnergy(e)
  const EPS = 1e-9 * (Math.abs(E0) + 1)
  const deltaMax = WIREP.travelCap * sc
  for (let k = 0; k <= DELTA_HALVINGS; k++) {
    const delta = deltaMax / (1 << k)
    // gate-resolution floor: below this Δ even the full linear descent −Δ·‖g‖
    // is smaller than the strict gate's EPS, so no trial can measurably pass —
    // the ladder's own resolution, not a tuning.
    if (delta * gnorm < EPS) break
    // one simultaneous trial: steepest descent in the M-metric, ‖trial‖_M = delta
    for (let i = 0; i < coords.length; i++) {
      const c = coords[i]!
      c.set(c.get() - delta * (g[i]! / (c.m * c.m)) / gnorm)
    }
    // a trial that drove an internal edge through its face is expressed in the
    // steepest incident chart (tangent-cone descent) — part of the same trial
    for (const param of params) {
      const crossed = param.edges.filter((ed) => ed.l < 0)
      if (crossed.length > 0) resolveCharts(e, param.w, param.nBind, param.nT, crossed)
    }
    // legality projection, then the one accept test on the true total E
    for (const b of movedBodies) b.pos = projectBodyPos(e, b, b.pos)
    recomputeRegions(e)
    const E1 = totalEnergy(e)
    if (E1 < E0 - EPS) return true
    restore()
    recomputeRegions(e)
  }
  // ── FACE-CROSSING TRIALS: for every internal edge short enough that passing
  // through its face fits the drawn-displacement budget (ℓ ≤ Δmax), propose
  // the φ-image directly: re-expand at the SAME amplitude in each NNI chart
  // along its canonical split (each branch toward the centroid of its non-edge
  // neighbours — φ-doc §4). These are ordinary bounded members of the proposal
  // set under the same strict gate — the passage a chart-local coordinate
  // cannot express (the tangent cone at the face fans into the incident
  // charts; a state resting in its own chart's flat bottom beside the face
  // needs exactly this proposal and no other mechanism). Deterministic order;
  // measured repro: a collapsed 4-star in the wrong pairing at ℓ=0.04 with the
  // orthogonal chart strictly lower (−0.023 at the same amplitude). ──
  for (const param of params) {
    const w2 = param.w
    const nBind = param.nBind, nT = param.nT
    for (const ed of param.edges) {
      const amp = Math.abs(ed.l)
      if (amp > deltaMax) continue
      const edges0 = wireEdges(w2, nBind, nT)
      const ei = edges0.findIndex(([a2, b2]) =>
        (a2 === nT + ed.child && b2 === nT + ed.parent) || (a2 === nT + ed.parent && b2 === nT + ed.child))
      if (ei < 0) continue
      const bi = nT + ed.parent, bj = nT + ed.child
      const pb = { ...w2.branches[ed.parent]! }, cb = { ...w2.branches[ed.child]! }
      const m0 = { x: (pb.x + cb.x) / 2, y: (pb.y + cb.y) / 2 }
      const termPos0 = wireTerminals(e, w2)
      const posOf0 = (node: number): Vec2 => {
        if (node >= nT) return node === bi ? pb : node === bj ? cb : w2.branches[node - nT]!
        if (node < termPos0.length) return termPos0[node]!
        return e.bodies.get(w2.endBodyId!)!.pos
      }
      const splitDir = (adj: readonly TreeEdge[], v: number, other: number): Vec2 => {
        const ns = adj.flatMap(([a2, b2]) => (a2 === v ? [b2] : b2 === v ? [a2] : [])).filter((x) => x !== other)
        let cx = 0, cy = 0
        for (const n of ns) { const p2 = posOf0(n); cx += p2.x; cy += p2.y }
        const dx = cx / Math.max(1, ns.length) - m0.x, dy = cy / Math.max(1, ns.length) - m0.y
        const d = Math.hypot(dx, dy)
        return d < 1e-9 ? { x: 1, y: 0 } : { x: dx / d, y: dy / d }
      }
      for (const alt of nniAlternatives(edges0, nT, ei)) {
        const ui = splitDir(alt, bi, bj), uj = splitDir(alt, bj, bi)
        const half = Math.max(amp, 0.01) / 2
        w2.branches[ed.parent] = { x: m0.x + ui.x * half, y: m0.y + ui.y * half }
        w2.branches[ed.child] = { x: m0.x + uj.x * half, y: m0.y + uj.y * half }
        const legs = buildChartLegs(e, w2, nBind, nT, alt, w2.legs)
        w2.legs.length = 0; for (const l of legs) w2.legs.push(l)
        recomputeRegions(e)
        const E1 = totalEnergy(e)
        if (E1 < E0 - EPS) return true
        restore()
        recomputeRegions(e)
      }
    }
  }
  // ── COORDINATE FALLBACK: the single joint direction can be blocked by a
  // crease arising from coordinate INTERACTIONS while individual coordinates
  // still strictly descend (measured: a collapsed 4-star resting at ℓ=0.036
  // with pure-ℓ descent available; branch/tangent descents visible only along
  // single axes). When the joint ladder rejects everything, try single
  // coordinates in steepest order under the SAME strict gate and drawn-
  // displacement budget — no line search to an optimum, just the other
  // one-sided-descending directions the gradient already found. Deterministic
  // (stable sort by index on ties). A frame that rejects ALL of these is the
  // proven rest. ──
  const order = coords.map((_, i) => i).filter((i) => g[i] !== 0)
  order.sort((a, d) => Math.abs(g[d]! / coords[d]!.m) - Math.abs(g[a]! / coords[a]!.m) || a - d)
  for (const i of order) {
    const c = coords[i]!
    const dir = -Math.sign(g[i]!)
    for (let k = 0; k <= DELTA_HALVINGS; k++) {
      const delta = deltaMax / (1 << k)
      if ((delta * Math.abs(g[i]!)) / c.m < EPS) break
      c.set(c.get() + (dir * delta) / c.m)
      for (const param of params) {
        const crossed = param.edges.filter((ed) => ed.l < 0)
        if (crossed.length > 0) resolveCharts(e, param.w, param.nBind, param.nT, crossed)
      }
      for (const b of movedBodies) b.pos = projectBodyPos(e, b, b.pos)
      recomputeRegions(e)
      const E1 = totalEnergy(e)
      if (E1 < E0 - EPS) return true
      restore()
      recomputeRegions(e)
    }
  }
  return false
}

/** One relaxation tick — STRICT TOTAL-ENERGY DESCENT (plan 23), the USER's
    ruling made structural: the system changes only when the change lowers the
    one total energy. Every DOF is a strictly E-gated candidate step; there is no
    velocity integration, no independent overlap mover, no zero-mode quotient, and
    (plan 24) no global-rotation operator — port-to-slot facing happens through
    each node's OWN rotation DOF responding to its OWN boundary leg's tension
    (local, wire-mediated), never a rigid whole-scene spin about a computed
    centroid (action at a distance, banned). Total E is monotone non-increasing
    across the whole tick. Deterministic: no randomness, seed from mkEngine's
    spiral. `pinned` bodies are held by the caller and skipped by every gate; the
    layout relaxes around them. The app frame loop calls this once per frame (a
    full sweep every frame — plan 24 motion policy). Returns whether the sweep
    changed any DOF; `false` means the layout reached a proven fixed point (see
    descentSweep) and further ticks are no-ops. */
export function settleStep(e: Engine, pinned: ReadonlySet<string> | null = null): boolean {
  recomputeRegions(e)
  // establish the fixed frame once, on first display (a raw settleStep loop with
  // no construction projection); the app/settle paths establish it from the LEGAL
  // seed beforehand (seedProject / settle's leading projection), so this is a
  // no-op there. Never re-established during settling — the frame is constant.
  if (e.frame === null) establishFrame(e)
  const moved = operatorStep(e, pinned)
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
