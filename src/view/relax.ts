import type { RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, FrameSlot, LegShape, WireLeg, WireView } from './engine'
import { frameBounds, frameSlots, subtreeCarriers, worldBindAnchor, resolveLeg, traceLeg } from './engine'
import { ELASTICA, QN } from './elastica'

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
  /** junction angular-spacing weight (Plateau 120° at rest, finite height so
      legs can swap by passing through) */
  junctionSpread: 10,
  /** ∃-tip standoff radius (the dot never sinks into its own wire) */
  standoffR: 8,
  /** boundary-exit pull: the constant force drawing a boundary wire's exit hub
      toward its frame slot. The global-rotation DOF (relax.ts) turns the content
      so each boundary port faces its slot, so a SOFT pull (12) lands the exit hub
      at the slot without re-exciting a coil: a briefly-misaligned port can relax
      instead of being forced into a blind cone. Measured sweet spot — at 30 the
      hard pinning re-coils and the layout oscillates (drift 10.8); at 12
      succShiftS@24 rests at drift 0.65, exit residual 0.89, stable E. Never pulls
      the NODE (a rigid slot pulling the node to the moving frame is a runaway). */
  exitPull: 12,
  /** trust region: max per-tick motion of any wire DOF (continuity law) */
  travelCap: 0.55,
}

/**
 * Rotation-aware relaxation for the render engine. Bodies (nodes + junctions)
 * carry a position AND an orientation DOF, both relaxed jointly: disc repulsion
 * within each region, leg springs with one rest length, per-region cohesion,
 * rotation toward the circular mean of leg-direction mismatches, boundary-exit
 * torque, and hard sibling-overlap projection. Regions are true minimal
 * enclosing circles recomputed every tick, so containment is an invariant of
 * the layout rather than an aesthetic. `settleStep` advances one tick (live
 * app use); `settle` runs a budget then projects to a fully legal drawing.
 */

/** Region padding beyond the minimal enclosing circle of its contents. */
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
const REST_LO = (): number => 2 * PACE.sibGap
const REST_HI = (): number => 4 * PACE.sibGap
/** The barrier SATURATES: it must hold a realistic crowd of saturated
    attractions (a few × SOFT_MAX()) but LOSE to a bundle of leg springs —
    a region circle spanning split content legitimately overlaps its
    siblings during transit, and an unbounded barrier exiles such content
    forever (observed: a sub-cluster slung 2000+ units from its hub
    junction, five springs pulling home at 60 against a barrier in the
    thousands). The projection, not the barrier, owns hard legality. */
const BARRIER_MAX = (): number => 3 * SOFT_MAX()
/** Per-call sweep budget for the overlap projection (work bound per tick;
    projection runs every tick, so any residual finishes on later ticks). */
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
      // a boundary exit hub (`e:<wid>`) rides ON the frame, which the CONTENT
      // defines — counting it in the enclosing circle would make the frame
      // chase the very slot the hub is drawn to (a runaway). It is a boundary
      // terminal, not content, so it is excluded from region geometry.
      if (mid.startsWith('e:')) continue
      discs.push({ c: b.pos, r: b.discR, mid })
    }
    for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius + REGION_PAD * 0.8, sub: c })
    if (discs.length === 0) {
      // only a contentless sheet reaches here (empty leaf regions carry an
      // anchor body)
      e.regions.set(rid, { center: { x: 0, y: 0 }, radius: 10, support: [] })
      continue
    }
    const mec = minimalEnclosingCircle(discs)
    e.regions.set(rid, {
      center: mec.center,
      radius: Math.max(mec.radius + REGION_PAD, 10),
      support: mec.support.map((m) => (m.mid !== undefined ? { mid: m.mid } : { sub: m.sub! })),
    })
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

function subtreeMembers(e: Engine, rid: RegionId): string[] {
  const out = [...e.membersOf.get(rid)!]
  for (const c of e.childrenOf.get(rid)!) out.push(...subtreeMembers(e, c))
  return out
}

export function resolveOverlaps(e: Engine): boolean {
  // Iterative projection to a legal drawing. Every violated sibling pair is
  // separated by a MASS-WEIGHTED positional split (the pair's mutual centroid
  // stays fixed) and given a perfectly inelastic normal impulse (both sides
  // leave the contact with the common normal velocity), then region geometry
  // is recomputed and the sweep repeats until legal or the pass budget is
  // spent — any residual is finished by the following ticks. Both properties
  // are conservation requirements, not tuning: an equal split between unequal
  // masses displaces the centroid every contact, and a one-sided velocity
  // clip injects net momentum — either one, repeated each tick, drives the
  // whole drawing off the sheet at a damping-limited terminal velocity.
  let any = false
  // Wire-owned bodies (homed ∃ ends / ∀ tips): hard legality is SEMANTIC
  // for REGIONS — a root-scoped ∃ inside a cut circle reads as the wrong
  // quantifier scope, so region pairs keep projecting them. Disc-vs-disc
  // spacing is NOT semantic for a wire-end dot: the wire's own barrier
  // handles disc clearance, and a hard PACE.sibGap projection against soft
  // wire tension parks the dot 15 wu out and cycles forever (measured).
  const wireOwnedP = new Set<string>()
  for (const b of e.bodies.values()) if (b.kind === 'junction') wireOwnedP.add(b.id)
  for (let pass = 0; pass < PROJECTION_PASSES; pass++) {
    let moved = false
    const dirty = new Set<RegionId>()
    for (const rid of e.regions.keys()) {
      const items: { sub: RegionId | null; id: string; r: number }[] = []
      for (const mid of e.membersOf.get(rid)!) {
        items.push({ sub: null, id: mid, r: e.bodies.get(mid)!.discR })
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
          : A.r + B.r + PACE.sibGap
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
        const bodiesOf = (it: typeof A): Body[] =>
          it.sub === null ? [e.bodies.get(it.id)!] : subtreeMembers(e, it.sub).map((m) => e.bodies.get(m)!)
        const bodiesA = bodiesOf(A), bodiesB = bodiesOf(B)
        if (bodiesA.length > 0 && bodiesB.length > 0) {
          const meanN = (bs: readonly Body[]): number =>
            bs.reduce((s, b) => s + b.vel.x * ux + b.vel.y * uy, 0) / bs.length
          const vrel = meanN(bodiesB) - meanN(bodiesA)
          if (vrel < 0) { // closing: inelastic — both sides take the common normal velocity
            const dA = wA * vrel, dB = -wB * vrel
            for (const b of bodiesA) b.vel = { x: b.vel.x + dA * ux, y: b.vel.y + dA * uy }
            for (const b of bodiesB) b.vel = { x: b.vel.x + dB * ux, y: b.vel.y + dB * uy }
          }
        }
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
function standoffU(d: number): number {
  const R = WIREP.standoffR
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
function legClearance(samples: readonly Vec2[], L: number, ownA: string | null, ownB: string | null, near: readonly DiscRec[]): number {
  if (near.length === 0) return 0
  const ds = L / QN
  let E = 0
  for (let k = 1; k < samples.length; k++) {
    const s = samples[k]!
    for (const D of near) {
      const R = D.r + WIREP.clearMargin
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

/** A leg's own energy: tension·L + bend closed form + arrival well (all inside
    the solve) + its clearance line integral. Every leg is the true θ-quadratic
    (the free-end candidate grid keeps free-end legs representable up to ~144°
    behind; the only bound is the numerical L-cap in resolveLeg). NO blend/second
    shape family — the demo shipped without one and it is strictly preferable. */
function legIntrinsicE(shape: LegShape, samples: readonly Vec2[], near: readonly DiscRec[]): number {
  const { c1, c2, L, well } = shape.sol
  return ELASTICA.tension * L
    + (ELASTICA.bend * (c1 * c1 + 2 * c1 * c2 + (4 / 3) * c2 * c2)) / L
    + well
    + legClearance(samples, L, shape.ownA, shape.ownB, near)
}

/** Wire↔wire separation between two legs' samples (every 3rd point: transverse
    crossings spend almost no arc in the band, co-running legs pay). */
function sepPair(sa: readonly Vec2[], sb: readonly Vec2[]): number {
  let E = 0
  for (let k = 0; k < sa.length; k += 3) for (let l = 0; l < sb.length; l += 3) {
    const dx = sa[k]!.x - sb[l]!.x, dy = sa[k]!.y - sb[l]!.y
    const d = Math.hypot(dx, dy)
    if (d < WIREP.sepR) E += (WIREP.sepSlope * (WIREP.sepR - d) * (WIREP.sepR - d)) / WIREP.sepR
  }
  return E
}

/** Junction angular-spacing (Plateau): pairwise, minimum when arrival
    directions are opposite (three legs → 120° apart), FINITE height so legs
    can swap by passing through. */
function spreadE(angles: readonly number[]): number {
  let E = 0
  for (let i = 0; i < angles.length; i++) for (let j = i + 1; j < angles.length; j++) {
    E += (WIREP.junctionSpread * (1 + Math.cos(angles[i]! - angles[j]!))) / 2
  }
  return E
}

/** Boundary-exit attraction: a Huber pull (constant force exitPull, softened to
    a quadratic within the core) drawing a boundary wire's exit point to its
    frame slot. Bounded so it never destabilizes; on the FREE exit point so the
    node stays put (a rigid slot pulling the node is a runaway). */
function exitAttractE(exit: Vec2, slot: Vec2): number {
  const d = Math.hypot(exit.x - slot.x, exit.y - slot.y)
  const core = 2
  return d > core ? WIREP.exitPull * (d - core / 2) : (WIREP.exitPull * d * d) / (2 * core)
}

/** The homed-body position of a leg terminal, or null (a bind has no body of
    its own; a hub POINT is wire-owned, not a body). */
function tipStandoffE(e: Engine, w: WireView): number {
  if (w.tipBodyId === null) return 0
  const tip = e.bodies.get(w.tipBodyId)!
  // the standoff is measured from the tip to its wire's port anchor (the
  // first — and only — bind of a dangling ∃)
  const bd = w.binds[0]
  if (bd === undefined) return 0
  const a = worldBindAnchor(e.bodies.get(bd.body)!, bd.key)
  return standoffU(Math.hypot(tip.pos.x - a.x, tip.pos.y - a.y))
}

/** Total wire energy of the engine — the monotonicity pin's observable and the
    demo's energy() (bodies-clearance/spacing excepted: that is the content
    integrator's job, kept separate).

    `warmInterior` is the global-rotation gate's OPTIONAL fast path (default OFF —
    the shipped gate uses the full memoryless grid). When on, every NON-boundary
    leg is WARM-solved from its cached solution (one Newton at the base turning)
    instead of the full grid scan: a rigid content rotation leaves an interior
    leg's relative geometry unchanged, so its solution transforms rigidly and the
    warm solve is exact — EXCEPT at a near-tie, where the full grid would FLIP the
    interior leg to a lower-E branch and warm holds the old one. That flip is what
    lets a strained scene REST (plusComm@20: full-grid drift 0.44 vs warm 3.13, E
    swinging), so warm is NOT the default; it is ~2× faster and bit-identical on
    non-near-tie scenes, kept for iteration (see `ROT_GATE_WARM`). */
export function wireEnergy(e: Engine, warmInterior = false): number {
  const discs: DiscRec[] = [...e.bodies.values()]
    .filter((b) => b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom')
    .map((b) => ({ id: b.id, body: b, r: b.discR }))
  const fb = frameBounds(e)
  const slots = fb === null ? null : frameSlots(fb, e.boundary.length)
  // resolve + trace every leg once
  const legSamples: { wid: string; samples: Vec2[] }[] = []
  let E = 0
  for (const [wid, w] of e.wires) {
    for (const leg of w.legs) {
      const warm = warmInterior && w.slot === null ? leg.cache.s : null
      const shape = resolveLeg(e, w, leg, leg.cache, warm)
      const samples: Vec2[] = []
      traceLeg(shape, samples, QN)
      const near = discs.filter((D) => bboxNear(samples, D.body.pos, D.r + WIREP.clearMargin))
      E += legIntrinsicE(shape, samples, near)
      legSamples.push({ wid, samples })
    }
    // junction spread over this wire's hub arrival angles
    if (w.hub !== null) E += spreadE(w.legs.filter((l) => l.b.kind === 'hub').map((l) => l.hubAngle))
    // boundary exit hub (the slot-attracted junction body) drawn to its slot
    if (w.slot !== null && w.hub !== null && w.hub.kind === 'body' && slots !== null && slots[w.slot] !== undefined) {
      E += exitAttractE(e.bodies.get(w.hub.bodyId)!.pos, slots[w.slot]!.point)
    }
    E += tipStandoffE(e, w)
  }
  // wire↔wire separation (different wires only)
  for (let a = 0; a < legSamples.length; a++) {
    for (let b = a + 1; b < legSamples.length; b++) {
      if (legSamples[a]!.wid === legSamples[b]!.wid) continue
      E += sepPair(legSamples[a]!.samples, legSamples[b]!.samples)
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
  let E = 0
  for (const child of e.childrenOf.get(body.region) ?? []) {
    const g = e.regions.get(child)
    if (g === undefined) continue
    const rr = g.radius + body.discR
    const dd = Math.hypot(body.pos.x - g.center.x, body.pos.y - g.center.y)
    if (dd >= rr + PACE.ringBand) continue
    const pen = rr + PACE.ringBand - dd
    E += (PACE.ringSlope / 2) * Math.min(pen, PACE.ringBand) * pen
  }
  return E
}

/** One resolved leg at its base (warm-cache) state, plus what it needs for the
    localized gradient: its samples, the discs near it, and its wire. */
type LegRec = { readonly wid: string; readonly w: WireView; readonly leg: WireLeg; readonly gi: number; readonly shape: LegShape; readonly samples: Vec2[]; readonly near: DiscRec[] }

/** Finite-difference steps + descent mobilities/caps (the demo's dimensional
    values per DOF kind). Translation DOF descend by GATED coordinate descent
    (the demo's user-accepted mechanism); node ROTATION alone keeps momentum
    (the wrench-ridge case — a measured non-monotonic damping sweep, 4→15,
    12→28, 30→3.9, showed damping tuning cannot settle rotation, but a torque
    ridge is crossed by momentum). */
const HX = 0.02
const MU = 0.1
/** Global-rotation gate fast path: OFF ships (full memoryless grid — correct
    minima on strained near-tie scenes, ~40 ms/tick on a 16-node framed scene
    during free settling). Flip to true for ~2× faster iteration (warm-solve the
    rotation-invariant interior legs); bit-identical except at near-ties, where it
    fails to rest — see wireEnergy's `warmInterior`. */
const ROT_GATE_WARM = false
/** Descent step of the demo (backtracking line search + long-shot ladder +
    expanding search): capped, strictly E-gated per visit, so every move lowers
    the DOF's local energy — the guarantee pure momentum lacked (it conveyored
    and converged slowly at theorem scale). */
function gatedStep(get: () => number, set: (v: number) => void, energy: () => number, h: number, mob: number, cap: number): void {
  const v0 = get()
  set(v0 + h); const ep = energy()
  set(v0 - h); const em = energy()
  set(v0); let Ecur = energy()
  const g = (ep - em) / (2 * h)
  if (g === 0) { set(v0); return }
  let mv = Math.max(-cap, Math.min(cap, -g * mob))
  let acc = 0
  for (let k = 0; k < 3; k++) { set(v0 + mv); const E1 = energy(); if (E1 < Ecur) { Ecur = E1; acc = mv; break } set(v0); mv /= 4 }
  if (acc === 0) {
    // smooth step rejected: long-shot ladder from the cap down (crosses a
    // local hill narrower than the cap, e.g. a branch-switch ridge)
    const dir = g > 0 ? -1 : 1
    for (const frac of [1, 1 / 3, 1 / 9]) { set(v0 + dir * cap * frac); const E1 = energy(); if (E1 < Ecur) { Ecur = E1; acc = dir * cap * frac; break } set(v0) }
  }
  // expanding search: a DOF far from rest covers distance in one visit
  while (acc !== 0 && Math.abs(acc) < cap) {
    const next = Math.max(-cap, Math.min(cap, acc * 3))
    set(v0 + next); const E2 = energy()
    if (E2 < Ecur) { Ecur = E2; acc = next } else break
  }
  set(v0 + acc)
}
/** Gated descent of a wire-owned POINT (x then y — coordinate descent). */
function gatedPoint(pt: { pos: Vec2 }, energy: () => number, mob: number, cap: number): void {
  gatedStep(() => pt.pos.x, (v) => { pt.pos = { x: v, y: pt.pos.y } }, energy, HX, mob, cap)
  gatedStep(() => pt.pos.y, (v) => { pt.pos = { x: pt.pos.x, y: v } }, energy, HX, mob, cap)
}

/**
 * The PLAN-22 wire force pass. Bodies (nodes, ∃ tips, ∀ hubs), wire hub points,
 * and per-leg arrival angles descend the wire energy by MOMENTUM: forces are
 * −∇E via localized central differences (only the legs a DOF touches are
 * re-solved with a scratch cache; everything else reads its base shape). Node
 * and homed-body forces/torques are ADDED to the shared accumulators (the
 * engine's existing damped velocity integration moves them); hub points and
 * arrival angles — wire-owned DOF — are integrated here from the same base
 * state (Jacobi: every force is read before any DOF moves).
 */
function wireForcePass(e: Engine, slots: FrameSlot[] | null, force: Map<string, { x: number; y: number }>): void {
  const discs: DiscRec[] = []
  for (const b of e.bodies.values()) if (b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom') discs.push({ id: b.id, body: b, r: b.discR })

  const legRecs: LegRec[] = []
  const legsOfWire = new Map<string, LegRec[]>()
  const cullR = WIREP.clearMargin + WIREP.travelCap
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
  const discNearLegs = new Map<string, LegRec[]>()
  for (const D of discs) discNearLegs.set(D.id, legRecs.filter((r) => bboxNear(r.samples, D.body.pos, D.r + cullR)))
  const crossNear = new Map<number, LegRec[]>()
  for (const r of legRecs) crossNear.set(r.gi, legRecs.filter((o) => o.wid !== r.wid && bboxOverlap(r.samples, o.samples, WIREP.sepR)))

  const scratchSamples: Vec2[][] = []
  const localE = (touched: readonly LegRec[], farBody: Body | null, spreadWire: WireView | null, tipWire: WireView | null, scopeBody: Body | null, exitWire: WireView | null): number => {
    let E = 0
    const touchedSet = new Set(touched.map((r) => r.gi))
    const probeSamples = new Map<number, Vec2[]>()
    touched.forEach((r, idx) => {
      // WARM solve at the base turning (envelope theorem — see resolveLeg):
      // correct DOF gradient, no per-probe grid scan
      const shape = resolveLeg(e, r.w, r.leg, r.leg.cache, r.shape.sol)
      const samp = scratchSamples[idx] ?? (scratchSamples[idx] = [])
      traceLeg(shape, samp, QN)
      probeSamples.set(r.gi, samp)
      E += legIntrinsicE(shape, samp, r.near)
    })
    for (const r of touched) {
      const samp = probeSamples.get(r.gi)!
      for (const o of crossNear.get(r.gi)!) {
        if (touchedSet.has(o.gi) && r.gi >= o.gi) continue
        E += sepPair(samp, touchedSet.has(o.gi) ? probeSamples.get(o.gi)! : o.samples)
      }
    }
    if (farBody !== null) {
      const near1: DiscRec[] = [{ id: farBody.id, body: farBody, r: farBody.discR }]
      for (const r of discNearLegs.get(farBody.id)!) {
        if (touchedSet.has(r.gi)) continue
        E += legClearance(r.samples, r.shape.sol.L, r.shape.ownA, r.shape.ownB, near1)
      }
    }
    if (spreadWire !== null) E += spreadE(spreadWire.legs.filter((l) => l.b.kind === 'hub').map((l) => l.hubAngle))
    if (tipWire !== null) E += tipStandoffE(e, tipWire)
    if (scopeBody !== null) E += homedScopeE(e, scopeBody)
    if (exitWire !== null && exitWire.hub !== null && exitWire.hub.kind === 'body' && slots !== null && exitWire.slot !== null && slots[exitWire.slot] !== undefined) {
      E += exitAttractE(e.bodies.get(exitWire.hub.bodyId)!.pos, slots[exitWire.slot]!.point)
    }
    return E
  }

  // ---- NODE-body DOF: the wire force on a node's TRANSLATION adds to the
  // shared accumulator (content-dominated, integrated by the engine's damped
  // velocity step); the node's ROTATION torque is accumulated here for its
  // momentum integrator (the wrench-ridge case). ----
  for (const b of e.bodies.values()) {
    if (b.kind !== 'ref' && b.kind !== 'term' && b.kind !== 'atom') continue
    const touched = bindLegs.get(b.id) ?? []
    let tipWire: WireView | null = null
    for (const r of touched) if (r.leg.b.kind === 'tip') tipWire = r.w
    const near = discNearLegs.get(b.id)!
    if (touched.length === 0 && near.length === 0) continue
    const F = force.get(b.id)!
    const s0 = b.pos
    b.pos = { x: s0.x + HX, y: s0.y }; const exP = localE(touched, b, null, tipWire, null, null)
    b.pos = { x: s0.x - HX, y: s0.y }; const exM = localE(touched, b, null, tipWire, null, null)
    b.pos = { x: s0.x, y: s0.y + HX }; const eyP = localE(touched, b, null, tipWire, null, null)
    b.pos = { x: s0.x, y: s0.y - HX }; const eyM = localE(touched, b, null, tipWire, null, null)
    b.pos = s0
    F.x += -(exP - exM) / (2 * HX)
    F.y += -(eyP - eyM) / (2 * HX)
    if (touched.length > 0) {
      // rotation by GATED descent (coordinate descent + long-shot ladder — the
      // demo's actual mechanism). The plan called for momentum here, but
      // momentum was measured OSCILLATING: a single-port node overshot its
      // facing orientation and spun (θ swinging, ω to −1.46, target angle
      // bouncing 9°↔156°). The ladder crosses the wrench ridge the plan cited
      // AND the strict E-gate settles it; rotational mobility scales with 1/area.
      gatedStep(() => b.theta, (v) => { b.theta = v }, () => localE(touched, null, null, tipWire, null, null), HX / b.discR, (4 * MU) / (b.discR * b.discR), 0.28)
    }
  }
  // ---- wire-owned TRANSLATION DOF: GATED coordinate descent (the demo's
  // user-accepted mechanism; strictly E-monotone so no conveyor). ----
  // ∃ tips (light, 3·MU) and ∀ hubs (junction bodies)
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    const w = e.wires.get(b.id.slice(2))
    if (w === undefined) continue // a bare ∃ dot — no legs
    const wLegs = legsOfWire.get(b.id.slice(2))!
    let touched: LegRec[]
    let tipWire: WireView | null = null
    let exitWire: WireView | null = null
    if (w.tipBodyId === b.id) { touched = wLegs.filter((r) => r.leg.b.kind === 'tip'); tipWire = w }
    else if (w.hub !== null && w.hub.kind === 'body' && w.hub.bodyId === b.id) {
      touched = wLegs.filter((r) => r.leg.b.kind === 'hub')
      // a BOUNDARY exit hub is the same body: it carries the slot attraction
      if (w.slot !== null) exitWire = w
    }
    else continue
    const en = (): number => localE(touched, null, null, tipWire, b, exitWire)
    // ∃ tips and boundary exit hubs are light + mobile — they float to a rest
    // (a scope standoff, a frame slot); a ∀ via-body is heavier and slower
    const light = w.tipBodyId === b.id || exitWire !== null
    gatedPoint(b, en, light ? 3 * MU : MU, light ? 0.55 : 0.28)
    b.vel = { x: 0, y: 0 }
  }
  // hub points (branch junctions)
  for (const [wid, w] of e.wires) {
    if (w.hub === null || w.hub.kind !== 'point') continue
    const touched = legsOfWire.get(wid)!.filter((r) => r.leg.b.kind === 'hub')
    gatedPoint(w.hub, () => localE(touched, null, null, null, null, null), MU, 0.28)
  }
  // per-leg arrival angles (stiff/slow: MU/64, cap 0.06)
  for (const [wid, w] of e.wires) {
    if (w.hub === null) continue
    for (const rec of legsOfWire.get(wid)!) {
      if (rec.leg.b.kind !== 'hub') continue
      const leg = rec.leg
      gatedStep(() => leg.hubAngle, (v) => { leg.hubAngle = v }, () => localE([rec], null, w, null, null, null), HX / 8, MU / 64, 0.06)
    }
  }
}

/** One relaxation tick — force integration + rotation + projection.
    Deterministic: no randomness, seed comes from mkEngine's spiral. `pinned`
    bodies take no sibling attraction so a drag holding them at the cursor
    feels direct (the caller overrides their positions each tick). */
export function settleStep(e: Engine, pinned: ReadonlySet<string> | null = null): void {
  recomputeRegions(e)
  // snapshot every body position: the end-of-tick quotient of the global
  // rotation zero mode is fitted against this
  const carrierStart: { get(): Vec2; set(p: Vec2): void; p0: Vec2; content: boolean }[] = []
  for (const b of e.bodies.values()) {
    // CONTENT bodies (nodes + region anchors) move rigidly under the layout's
    // translation/rotation zero modes; wire-owned junctions (∃ tips, ∀/boundary
    // hubs) creep relative to them, so they are not part of the zero-mode fit
    carrierStart.push({ get: () => b.pos, set: (p) => { b.pos = p }, p0: b.pos, content: b.kind !== 'junction' })
  }
  // force accumulator: mutable points, not the readonly Vec2 used for state
  const force = new Map<string, { x: number; y: number }>()
  for (const id of e.bodies.keys()) force.set(id, { x: 0, y: 0 })

  // Wire-owned ends (∃ free ends, ∀ via-body hubs, bare ∃ dots) are junction
  // bodies driven ONLY by their wire's energy — no zero mode, so the content
  // anchoring must not park them (USER: dangles must be pulled by their
  // edges). Their sibling pairs are skipped entirely; scope legality is the
  // projection's job, clearance the wire barrier's.
  const wireOwned = new Set<string>()
  for (const b of e.bodies.values()) if (b.kind === 'junction') wireOwned.add(b.id)

  // Sibling pair force on the REAL circle gap, with PACE.softScale AS AN INTERVAL:
  // a barrier repulsion below the target gap (unbounded toward contact, so
  // no bounded crowd of attractions can press a pair into the projection),
  // then a WIDE zero-force dead zone, then saturated constant attraction
  // ramping in beyond it. Every standing cycle this layout has ever had was
  // a POINT equilibrium re-excited by noise in the derived geometry (region
  // circles breathe as their content micro-moves) or by disagreement
  // between the soft field and the hard projection; an equilibrium
  // INTERVAL of exactly zero force absorbs both — content coasts into the
  // zone under damping and nothing acts on it again. The attraction stays
  // above the leg-spring cap so no spring can outpull the anchoring and
  // drive a conveyor across the sheet.
  for (const rid of e.regions.keys()) {
    const discs: { r: number; mid?: string; sub?: RegionId }[] = []
    for (const mid of e.membersOf.get(rid)!) discs.push({ r: e.bodies.get(mid)!.discR, mid })
    for (const c of e.childrenOf.get(rid)!) discs.push({ r: e.regions.get(c)!.radius, sub: c })
    const centerOf = (D: { mid?: string; sub?: RegionId }): Vec2 =>
      D.mid !== undefined ? e.bodies.get(D.mid)!.pos : e.regions.get(D.sub!)!.center
    for (let i = 0; i < discs.length; i++) for (let j = i + 1; j < discs.length; j++) {
      const A = discs[i]!, B = discs[j]!
      const ca = centerOf(A), cb = centerOf(B)
      const dx = cb.x - ca.x, dy = cb.y - ca.y
      const dist = Math.max(Math.hypot(dx, dy), 1)
      const gap = dist - A.r - B.r
      // wire-owned bodies (homed ∃/∀ ends) take no content PAIR FORCES:
      // the content spacing rules are sized for content discs and would
      // park a wire-end dot 20+ wu out against its own wire's tension (the
      // original user complaint). Scope legality is the projection's job;
      // clearance is the wire barrier's.
      if ((A.mid !== undefined && wireOwned.has(A.mid)) || (B.mid !== undefined && wireOwned.has(B.mid))) continue
      const f = gap < REST_LO()
        ? -Math.min(PACE.rep * ((REST_LO() + 8) / Math.max(gap + 8, 0.5) - 1), BARRIER_MAX())
        : gap <= REST_HI()
          ? 0
          : SOFT_MAX() * Math.min(1, (gap - REST_HI()) / PACE.sibGap)
      if (f === 0) continue
      const ux = dx / dist, uy = dy / dist
      // each side receives a TOTAL of ±f shared over its subtree bodies
      // (equal-and-opposite — unshared application injects net momentum);
      // a pinned (dragged) side takes no attraction, but the barrier still
      // applies so a drag cannot tunnel through things
      const apply = (D: typeof A, sx: number, sy: number): void => {
        const targets = D.mid !== undefined ? [D.mid] : subtreeMembers(e, D.sub!)
        const per = 1 / targets.length
        for (const mid of targets) {
          if (f > 0 && pinned !== null && pinned.has(mid)) continue
          const F = force.get(mid)!
          F.x += sx * per
          F.y += sy * per
        }
      }
      apply(A, ux * f, uy * f)
      apply(B, -ux * f, -uy * f)
    }
  }

  // PLAN 22 — the massless-elastica wire forces. Every DOF (node bodies, ∃
  // tips, ∀ hubs, wire hub points, per-leg arrival angles) descends the wire
  // energy by MOMENTUM: forces are −∇E via localized central differences.
  // Node/homed-body forces + torques ADD to the accumulators (the shared
  // damped integration below moves them); the wire-owned hub points and
  // arrival angles are integrated inside the pass from the same base state.
  const fb0 = frameBounds(e)
  const slotPts = fb0 === null ? null : frameSlots(fb0, e.boundary.length)
  wireForcePass(e, slotPts, force)

  // Damped momentum integration. NOTE (plan 21, measured): the velocity
  // state is load-bearing for the overlap projection (its inelastic normal
  // impulses are what stop projected pairs re-colliding every tick — pure
  // position descent was tried and the projection ping-pong is 100× worse),
  // and it carries a KNOWN RESIDUAL: the explicit wire↔body coupling lag
  // sustains a marginal standing cycle of ~0.02 wu amplitude (invisible at
  // any zoom; net energy non-creeping — pinned in wirephys.test.ts). Full
  // elimination needs a projection-free descent redesign of containment —
  // recorded in the plan as future work, out of plan-21 scope.
  for (const b of e.bodies.values()) {
    const F = force.get(b.id)!
    b.vel = { x: (b.vel.x + F.x * PACE.dt) / (1 + PACE.damp * PACE.dt), y: (b.vel.y + F.y * PACE.dt) / (1 + PACE.damp * PACE.dt) }
    b.pos = { x: b.pos.x + b.vel.x * PACE.dt, y: b.pos.y + b.vel.y * PACE.dt }
  }

  // (rotation is descended by the gated coordinate step in wireForcePass, not
  // integrated here — momentum was measured oscillating on a single-port node.)

  // project to feasibility every tick: per-tick motion is small, so the
  // sweeps converge in a few passes; partial projection (one sweep, or a
  // sparser cadence) leaves standing violations that the forces feed on —
  // observed as a persistent conveyor limit cycle that never rests
  resolveOverlaps(e)

  // Quotient the global-rotation zero mode. Nothing anchors the layout's
  // absolute orientation, and the overlap projection separates pairs along
  // circle-center lines while applying the shifts at member positions — the
  // mismatch injects a small rigid rotation at every contact, which
  // accumulates as a visible constant-rate spin of the whole drawing
  // (observed: ~26°/100 ticks). A rigid rotation preserves every pairwise
  // distance, so removing the tick's best-fit rotation about the centroid
  // keeps all constraints satisfied and all relative geometry untouched.
  if (carrierStart.length > 1) {
    let c0x = 0, c0y = 0, c1x = 0, c1y = 0
    for (const c of carrierStart) {
      c0x += c.p0.x; c0y += c.p0.y
      const p = c.get(); c1x += p.x; c1y += p.y
    }
    const n = carrierStart.length
    c0x /= n; c0y /= n; c1x /= n; c1y /= n
    let cross = 0, dot = 0
    for (const c of carrierStart) {
      const ax = c.p0.x - c0x, ay = c.p0.y - c0y
      const p = c.get()
      const bx = p.x - c1x, by = p.y - c1y
      cross += ax * by - ay * bx
      dot += ax * bx + ay * by
    }
    const dth = Math.atan2(cross, dot)
    if (Math.abs(dth) > 1e-12) {
      const cs = Math.cos(-dth), sn = Math.sin(-dth)
      for (const c of carrierStart) {
        const p = c.get()
        const rx = p.x - c1x, ry = p.y - c1y
        c.set({ x: c1x + rx * cs - ry * sn, y: c1y + rx * sn + ry * cs })
      }
      for (const b of e.bodies.values()) {
        b.vel = { x: b.vel.x * cs - b.vel.y * sn, y: b.vel.x * sn + b.vel.y * cs }
        b.theta -= dth
      }
      // the quotient is a rigid transform of the WHOLE state: a wire-owned hub
      // POINT (and its velocity) rotates with the bodies, and the world-frame
      // arrival angles shift by dθ. (A boundary exit HUB is a body, already
      // rotated by the body loop above.) Rotating bodies alone would twist every
      // leg against its hub each tick — a slow self-propelled conveyor.
      const rot = (pt: { pos: Vec2; vel: Vec2 }): void => {
        const rx = pt.pos.x - c1x, ry = pt.pos.y - c1y
        pt.pos = { x: c1x + rx * cs - ry * sn, y: c1y + rx * sn + ry * cs }
        pt.vel = { x: pt.vel.x * cs - pt.vel.y * sn, y: pt.vel.x * sn + pt.vel.y * cs }
      }
      for (const w of e.wires.values()) {
        if (w.hub !== null && w.hub.kind === 'point') rot(w.hub)
        for (const leg of w.legs) if (leg.b.kind === 'hub') leg.hubAngle -= dth
      }
      recomputeRegions(e)
    }
  }

  // Quotient the global-TRANSLATION zero mode. A boundary exit's slot attraction
  // is an EXTERNAL force (a frame slot is a fixed point, not a body), so the sum
  // over the boundary wires is a small NET force that slowly conveys the whole
  // layout across the sheet (measured ~0.026 wu/tick on plusComm step 0 — every
  // body drifting rigidly, centroid included). A rigid translation preserves
  // every pairwise distance and every constraint, so removing the tick's net
  // CONTENT-centroid shift restores the anchor without touching the relative
  // geometry. A dragged pin already anchors translation, so this runs only in
  // free relaxation.
  if (pinned === null && carrierStart.length > 1) {
    let s0x = 0, s0y = 0, s1x = 0, s1y = 0, cn = 0
    for (const c of carrierStart) {
      if (!c.content) continue
      s0x += c.p0.x; s0y += c.p0.y
      const p = c.get(); s1x += p.x; s1y += p.y; cn++
    }
    if (cn > 0) {
      const dx = (s1x - s0x) / cn, dy = (s1y - s0y) / cn
      if (Math.abs(dx) > 1e-12 || Math.abs(dy) > 1e-12) {
        for (const b of e.bodies.values()) b.pos = { x: b.pos.x - dx, y: b.pos.y - dy }
        for (const w of e.wires.values()) if (w.hub !== null && w.hub.kind === 'point') w.hub.pos = { x: w.hub.pos.x - dx, y: w.hub.pos.y - dy }
        recomputeRegions(e)
      }
    }
  }

  // GATED GLOBAL-ROTATION DOF (framed alignment). The rotation quotient above
  // removes the overlap projection's spurious injected spin (a genuine zero-mode
  // artifact); this then spins the content — every body EXCEPT the boundary exit
  // hubs (pos + theta + vel), plus wire hub points and world-frame arrival angles
  // — about the content centroid by the angle that most lowers the BOUNDARY LEG
  // energy. The boundary exit hubs are held fixed (they belong to the frame, not
  // the content), so rotating a node turns its port RELATIVE to its exit hub:
  // when the port faces away, the port→hub leg is a blind-cone coil with an
  // enormous tension·L, and rotating the port to face the hub dissolves it. That
  // is exactly the coherent motion the unconditional quotient was erasing — on a
  // FRAMED diagram the fixed slots make it a real gradient; on a frameless layout
  // there are no boundary legs, so this is skipped. Interior/∃/∀ legs rotate with
  // both their ends (rigid ⇒ invariant), so only the boundary legs move the gate.
  // It runs AFTER the quotient so its INTENTIONAL rotation becomes next tick's
  // snapshot baseline rather than being removed as net spin — the two never fight.
  if (pinned === null && e.boundary.length > 0 && carrierStart.length > 1) {
    let gcx = 0, gcy = 0, gn = 0
    for (const b of e.bodies.values()) if (b.kind !== 'junction') { gcx += b.pos.x; gcy += b.pos.y; gn++ }
    if (gn > 0) {
      gcx /= gn; gcy /= gn
      // snapshot every rotatable piece (boundary exit hubs `e:` excluded — they
      // are the fixed frame terminals) so each probe rotates from one base
      const bodySnap = [...e.bodies.values()].filter((b) => !b.id.startsWith('e:')).map((b) => ({ b, pos: b.pos, vel: b.vel, theta: b.theta }))
      const hubSnap = [...e.wires.values()].filter((w) => w.hub !== null && w.hub.kind === 'point').map((w) => { const h = w.hub as { pos: Vec2; vel: Vec2 }; return { h, pos: h.pos, vel: h.vel } })
      const angSnap: { leg: WireLeg; a: number }[] = []
      for (const w of e.wires.values()) for (const leg of w.legs) if (leg.b.kind === 'hub') angSnap.push({ leg, a: leg.hubAngle })
      const applyRot = (d: number): void => {
        const cs = Math.cos(d), sn = Math.sin(d)
        for (const s of bodySnap) {
          const rx = s.pos.x - gcx, ry = s.pos.y - gcy
          s.b.pos = { x: gcx + rx * cs - ry * sn, y: gcy + rx * sn + ry * cs }
          s.b.vel = { x: s.vel.x * cs - s.vel.y * sn, y: s.vel.x * sn + s.vel.y * cs }
          s.b.theta = s.theta + d
        }
        for (const s of hubSnap) {
          const rx = s.pos.x - gcx, ry = s.pos.y - gcy
          s.h.pos = { x: gcx + rx * cs - ry * sn, y: gcy + rx * sn + ry * cs }
          s.h.vel = { x: s.vel.x * cs - s.vel.y * sn, y: s.vel.x * sn + s.vel.y * cs }
        }
        for (const s of angSnap) s.leg.hubAngle = s.a + d
      }
      // gate: the whole wire energy (frame recomputed each probe). It MUST be the
      // full functional — a rigid content rotation with the exit hubs held changes
      // only the boundary legs and the slot terms, but a gate that drops the
      // "invariant" interior terms was measured to leak a small non-constant amount
      // (~32 on succShiftS@24) — a spurious gradient that pumps the total to drift
      // 11.6. It uses the FULL memoryless grid solve for every leg, not the warm
      // fast path: on a near-tie scene (plusComm@20) the grid FLIPS an interior
      // leg's branch under the probe rotation and reaches a lower-E, aligned rest
      // (drift 0.44), where the warm solve holds the old branch and does NOT rest
      // (drift 3.13, E swinging) — the corpus settles-and-stays law needs the flip.
      const totalE = (): number => { recomputeRegions(e); return wireEnergy(e, ROT_GATE_WARM) }
      let applied = 0
      gatedStep(() => applied, (v) => { applyRot(v); applied = v }, totalE, HX, MU, 0.28)
      recomputeRegions(e)
    }
  }
  e.tick++
}

/** Run a tick budget, then project to a fully legal (overlap-free) drawing. */
export function settle(e: Engine, ticks: number): void {
  for (let t = 0; t < ticks; t++) settleStep(e)
  recomputeRegions(e)
  resolveOverlaps(e)
}
