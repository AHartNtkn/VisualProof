import type { RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, LegShape, WireLeg, WireView } from './engine'
import { frameBounds, frameSlots, subtreeCarriers, worldBindAnchor, resolveLeg, traceLeg } from './engine'
import { ELASTICA, QN, mkLegCache } from './elastica'
import type { LegCache } from './elastica'

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
  /** junction TRUNK-alignment weight: pulls each hub leg's arrival direction to
      its trunk-tangent target (the two most-opposite legs flow through the hub
      as one continuous trunk, side legs merge tangentially — the tributary look,
      USER LAW). Finite height so the elastica bend can shade the merge angle. */
  junctionTrunk: 10,
  /** trunk-axis nematic weight: how strongly a hub's trunk axis `phi` aligns to
      its leg chord directions (the anchor that keeps `phi` tracking the geometry
      rather than drifting; its travel cap gives the no-flip inertia). */
  trunkAxis: 8,
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
  for (const b of e.bodies.values()) if (b.kind === 'junction') wireOwnedP.add(b.id)
  for (let pass = 0; pass < PROJECTION_PASSES; pass++) {
    let moved = false
    const dirty = new Set<RegionId>()
    for (const rid of e.regions.keys()) {
      const items: { sub: RegionId | null; id: string; r: number }[] = []
      for (const mid of e.membersOf.get(rid)!) {
        // boundary exit hubs (`e:`) are FRAME terminals, not content: they are
        // excluded from region circles and positioned solely by their slot
        // attraction, so region legality never applies (projecting one — e.g. out
        // of a cut its slot sits behind — shoves it 166 wu and wrecks the layout).
        if (mid.startsWith('e:')) continue
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

/** Shortest signed angle to `x` (radians, in (−π, π]). */
function wrapAngle(x: number): number { return Math.atan2(Math.sin(x), Math.cos(x)) }

/** The TRUNK-TANGENT target for a hub leg (USER LAW — the round-8-D tributary
    rule): given the leg's chord direction `dir` (hub → its port) and the hub's
    trunk axis `phi`, the leg's arrival TRAVEL direction at the hub. Each leg is
    pulled from its own radial direction toward the nearer end of the trunk axis
    (`phi` or `phi+π`) by weight |cos(dir−phi)| — which is 1 for a leg lying along
    the axis (it becomes the trunk, arriving antiparallel to the leg on the far
    side) and 0 for a leg perpendicular to it (it stays radial). The weight
    vanishing exactly at the perpendicular is what makes the merge CONTINUOUS: no
    side leg can jump between axis ends. The returned value is the travel
    direction INTO the hub (port→hub→beyond), i.e. the outgoing tangent + π. */
export function trunkTarget(dir: number, phi: number): number {
  const axisSide = Math.abs(wrapAngle(phi - dir)) <= Math.PI / 2 ? phi : phi + Math.PI
  const wgt = Math.abs(Math.cos(dir - phi))
  const outward = dir + wrapAngle(axisSide - dir) * wgt // tangent leaving the hub toward the port
  return wrapAngle(outward + Math.PI)
}

/** The world hub point of a wire with a hub. */
function hubPoint(e: Engine, w: WireView): Vec2 {
  const h = w.hub!
  return h.kind === 'point' ? h.pos : e.bodies.get(h.bodyId)!.pos
}

/** Chord direction (hub → port) of one hub leg. */
function legChordDir(e: Engine, w: WireView, leg: WireLeg, hp: Vec2): number {
  const bd = w.binds[leg.a.kind === 'bind' ? leg.a.i : 0]!
  const p = worldBindAnchor(e.bodies.get(bd.body)!, bd.key)
  return Math.atan2(p.y - hp.y, p.x - hp.x)
}

/** Junction TRUNK alignment (replaces the symmetric 120° spread): each hub leg's
    arrival direction `hubAngle` is pulled to its `trunkTarget`, so the two
    most-opposite legs arrive antiparallel (one continuous trunk through the hub)
    and the rest merge tangentially. Interior hubs only — a boundary exit leg is a
    free end (its arrival tangent is solved, not a DOF), so it takes no trunk term. */
function trunkAlignE(e: Engine, w: WireView): number {
  if (w.hub === null || w.slot !== null) return 0
  const hp = hubPoint(e, w)
  let E = 0
  for (const leg of w.legs) {
    if (leg.b.kind !== 'hub') continue
    const target = trunkTarget(legChordDir(e, w, leg, hp), w.phi)
    E += (WIREP.junctionTrunk * (1 - Math.cos(leg.hubAngle - target))) / 2
  }
  return E
}

/** Trunk-AXIS nematic alignment: the hub axis `phi` is pulled to the nematic
    director of its leg chord directions. This is the ONLY term `phi` appears in
    besides `trunkAlignE`, and it is what anchors `phi` to the geometry (so it
    tracks the layout instead of drifting); its gated travel cap gives the
    no-flip inertia. Interior hubs only. */
function trunkAxisE(e: Engine, w: WireView): number {
  if (w.hub === null || w.slot !== null) return 0
  const hp = hubPoint(e, w)
  let E = 0
  for (const leg of w.legs) {
    if (leg.b.kind !== 'hub') continue
    const dir = legChordDir(e, w, leg, hp)
    E += (WIREP.trunkAxis * (1 - Math.cos(2 * (dir - w.phi)))) / 2
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

/** Total WIRE energy of the engine (leg intrinsic + clearance, junction spread,
    boundary exit→slot attraction, ∃-tip standoff, wire↔wire separation) — one
    half of `totalEnergy`; `contentEnergy` is the other. Uses the full memoryless
    grid solve for every leg (a near-tie scene needs the branch flip it finds). */
export function wireEnergy(e: Engine): number {
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
      const shape = resolveLeg(e, w, leg, leg.cache)
      const samples: Vec2[] = []
      traceLeg(shape, samples, QN)
      const near = discs.filter((D) => bboxNear(samples, D.body.pos, D.r + WIREP.clearMargin))
      E += legIntrinsicE(shape, samples, near)
      legSamples.push({ wid, samples })
    }
    // junction trunk alignment + trunk-axis anchoring over this wire's hub
    E += trunkAlignE(e, w) + trunkAxisE(e, w)
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
function sibU(gap: number): number {
  const LO = REST_LO(), HI = REST_HI(), g = PACE.sibGap
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

/** Total CONTENT energy: sibling spacing over every region's sibling pairs
    (content discs + child region circles; wire-owned dots take no sibling term —
    the wire barrier owns their clearance) plus the scope-ring containment of
    every wire-owned dot. Region circles are read live, so a probe that moved a
    body must `recomputeRegions` first (the gates do). */
export function contentEnergy(e: Engine): number {
  let E = 0
  for (const rid of e.regions.keys()) {
    const items: { r: number; c: Vec2 }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      if (b.kind === 'junction') continue
      items.push({ r: b.discR, c: b.pos })
    }
    for (const cId of e.childrenOf.get(rid)!) { const g = e.regions.get(cId)!; items.push({ r: g.radius, c: g.center }) }
    for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
      const A = items[i]!, B = items[j]!
      const dist = Math.max(Math.hypot(A.c.x - B.c.x, A.c.y - B.c.y), 1)
      E += sibU(dist - A.r - B.r)
    }
  }
  // scope-ring confines ∃ tips / ∀ hubs to their scope; boundary exit hubs (`e:`)
  // are frame terminals (drawn to a slot outside the content), so they take no
  // scope-ring — it would fight the slot attraction and trap them inside a cut.
  for (const b of e.bodies.values()) if (b.kind === 'junction' && !b.id.startsWith('e:')) E += homedScopeE(e, b)
  return E
}

/** The sum of every boundary wire's exit-hub→slot attraction. Isolated as a
    LOCALIZATION helper for the per-body gates: moving ANY content body changes
    the derived sheet circle → the frame → every slot, so this whole term must be
    added to a translation gate's local energy (localE omits it). It is NOT added
    to `totalEnergy` — `wireEnergy` already contains it. */
function boundaryExitE(e: Engine): number {
  const fb = frameBounds(e)
  if (fb === null) return 0
  const slots = frameSlots(fb, e.boundary.length)
  let E = 0
  for (const w of e.wires.values()) {
    if (w.slot !== null && w.hub !== null && w.hub.kind === 'body' && slots[w.slot] !== undefined)
      E += exitAttractE(e.bodies.get(w.hub.bodyId)!.pos, slots[w.slot]!.point)
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
  if (b.id.startsWith('e:')) return p // frame terminal — no region legality
  const owned = b.kind === 'junction'
  let x = p.x, y = p.y
  const push = (cx: number, cy: number, need: number): void => {
    const dx = x - cx, dy = y - cy, d = Math.hypot(dx, dy)
    if (d >= need) return
    const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
    x = cx + ux * need; y = cy + uy * need
  }
  for (const mid of e.membersOf.get(b.region)!) {
    if (mid === b.id) continue
    const o = e.bodies.get(mid)!
    if (owned || o.kind === 'junction') continue // disc-vs-dot pairs: wire barrier's job
    push(o.pos.x, o.pos.y, b.discR + o.discR + PACE.sibGap)
  }
  for (const cId of e.childrenOf.get(b.region)!) {
    const g = e.regions.get(cId)!
    push(g.center.x, g.center.y, owned ? g.radius : b.discR + g.radius + PACE.sibGap)
  }
  return { x, y }
}

/** Project a DRAGGED body's target position onto the SEMANTIC-feasible set: the
    body must stay OUTSIDE every region circle it is not a member of. This is HARD
    SEMANTIC CONTAINMENT (USER LAW): a node crossing into a cut it isn't part of
    CHANGES WHAT THE DIAGRAM MEANS, so it must not happen even transiently during a
    drag. The body is already inside its OWN region by construction — region circles
    are DERIVED to contain their members, so the region follows the dragged body —
    hence only the "outside non-member circles" half needs projecting. `p` is the
    unguarded cursor target; every non-ancestor cut/bubble circle pushes the body's
    disc fully clear with the sibling gap (the same bound the settling projection
    uses, so releasing the drag adds no jump). Ancestors of the body's region (the
    cuts it IS inside) are exempt, as is a wire-owned dot's disc clearance (the wire
    barrier owns that) — a dot only clears the circle itself. */
export function clampDragToFeasible(e: Engine, b: Body, p: Vec2): Vec2 {
  if (b.id.startsWith('e:')) return p // frame terminal — no region legality
  const ancestors = new Set<RegionId>()
  for (let r = b.region; ;) {
    ancestors.add(r)
    const reg = e.d.regions[r]!
    if (reg.kind === 'sheet') break
    r = reg.parent
  }
  const owned = b.kind === 'junction'
  let x = p.x, y = p.y
  for (const [rid, g] of e.regions) {
    if (ancestors.has(rid) || e.d.regions[rid]!.kind === 'sheet') continue
    const need = owned ? g.radius : b.discR + g.radius + PACE.sibGap
    const dx = x - g.center.x, dy = y - g.center.y, d = Math.hypot(dx, dy)
    if (d >= need) continue
    const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
    x = g.center.x + ux * need; y = g.center.y + uy * need
  }
  return { x, y }
}

/** One resolved leg at its base (warm-cache) state, plus what it needs for the
    localized gradient: its samples, the discs near it, and its wire. */
type LegRec = { readonly wid: string; readonly w: WireView; readonly leg: WireLeg; readonly gi: number; readonly shape: LegShape; readonly samples: Vec2[]; readonly near: DiscRec[] }

/** Finite-difference step and base descent mobility (the demo's dimensional
    values); every DOF descends by the strictly E-gated coordinate step below. */
const HX = 0.02
const MU = 0.1
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
/** Gated 2D descent of a BODY position with the legality projection folded into
    candidate evaluation (plan 23): the ±HX gradient probes (tiny, always feasible)
    give the descent direction via `gradEnergy` (the envelope-theorem warm fast
    path — correct to first order at the base); each trial along −∇E is PROJECTED
    onto the feasible set (`project`) and measured with the true grid `energy`,
    accepted only if strictly lower — so every accepted state is feasible AND lower
    in the true total (strict descent inside the feasible set). */
function gatedMove(get: () => Vec2, set: (p: Vec2) => void, project: (p: Vec2) => Vec2, gradEnergy: () => number, energy: () => number, mob: number, cap: number): void {
  const p0 = get()
  set({ x: p0.x + HX, y: p0.y }); const exP = gradEnergy()
  set({ x: p0.x - HX, y: p0.y }); const exM = gradEnergy()
  set({ x: p0.x, y: p0.y + HX }); const eyP = gradEnergy()
  set({ x: p0.x, y: p0.y - HX }); const eyM = gradEnergy()
  set(p0); let Ecur = energy()
  const gx = (exP - exM) / (2 * HX), gy = (eyP - eyM) / (2 * HX)
  const gm = Math.hypot(gx, gy)
  if (gm === 0) { set(p0); return }
  const ux = -gx / gm, uy = -gy / gm
  const step = Math.min(cap, gm * mob)
  let acc = 0, accP = p0
  // backtracking line search along −∇E
  for (const frac of [1, 1 / 4, 1 / 16]) {
    const mv = step * frac
    const trial = project({ x: p0.x + ux * mv, y: p0.y + uy * mv })
    set(trial); const E1 = energy()
    if (E1 < Ecur) { Ecur = E1; acc = mv; accP = trial; break }
    set(p0)
  }
  // expanding search: a body far from rest covers distance in one visit
  while (acc > 0 && acc < cap) {
    const next = Math.min(cap, acc * 3)
    const trial = project({ x: p0.x + ux * next, y: p0.y + uy * next })
    set(trial); const E2 = energy()
    if (E2 < Ecur) { Ecur = E2; acc = next; accP = trial } else break
  }
  // leave the state AND the derived geometry at the accepted position: a
  // rejected trial's energy() left the region circles recomputed at that trial,
  // so re-evaluate at accP to re-sync them for the next body in the sweep.
  set(accP); energy()
}

/**
 * The PLAN-23 strict-descent pass, as a WORKLIST: one thunk per DOF — node
 * translation and rotation, ∃-tip / ∀-hub / boundary-exit-hub translation, wire
 * hub points, per-leg arrival angles — each a strictly E-GATED coordinate step
 * (backtracking + expanding search; a move is taken only when it strictly lowers
 * the localized total) over the ONE total energy (wires + content). There is no
 * velocity, no force accumulator, no independent overlap mover: cycles are
 * impossible by theorem, wander impossible by theorem — the USER's ruling as a
 * structural property. TRANSLATION gates fold in the legality projection (propose
 * → project the moved body onto the feasible set → evaluate → accept only if
 * lower) and the full content + frame-coupling energy the per-leg localization
 * omits. `pinned` bodies are hard CONSTRAINTS: all their DOF are skipped (the
 * caller holds them at the cursor), and everything relaxes around them.
 *
 * Returning the DOFs as a worklist (rather than running them inline) lets the app
 * frame loop TIME-SLICE one sweep across frames (the anytime budget): the snapshot
 * this builds is cheap (~5 ms at 28 bodies) versus the gate loop (~230 ms), and
 * each thunk's move is applied in place, so resuming a sliced sweep against a
 * freshly rebuilt snapshot is equivalent to one continuous sweep. The DOF order is
 * deterministic (Map insertion order over bodies/wires) and stable across frames
 * for a fixed diagram, so a persistent integer cursor resumes correctly.
 */
function descentDofs(e: Engine, pinned: ReadonlySet<string> | null): (() => void)[] {
  const dofs: (() => void)[] = []
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
  // separation neighbourhood, widened by the per-tick travel of BOTH legs' ends
  // (2·travelCap) so a leg that swings INTO range mid-sweep is already listed —
  // otherwise its rising sep term is invisible to the gate and pumps a limit
  // cycle (the same reason clearance uses cullR).
  const sepCull = WIREP.sepR + 2 * WIREP.travelCap
  const crossNear = new Map<number, LegRec[]>()
  for (const r of legRecs) crossNear.set(r.gi, legRecs.filter((o) => o.wid !== r.wid && bboxOverlap(r.samples, o.samples, sepCull)))

  const scratchSamples: Vec2[][] = []
  // Per-leg MEMORYLESS probe cache (keyed on the exact boundary tuple, separate
  // from the committed leg.cache so probing never clobbers it): plan 23 gates
  // ACCEPT a move on the energy VALUE, so the probe MUST evaluate the true
  // memoryless grid solve. The warm fixed-turn energy (plan 22, envelope theorem)
  // has the same first-order gradient but a different value: warm can UNDERCUT
  // the grid min (the grid scan is not a guaranteed global optimizer, and a
  // far-moved warm closeAt need not close), so a warm-lowering move can raise the
  // true grid total (measured: pc0 drift 0→37, pc16 monotonicity spike →243).
  const probeCache = new Map<number, LegCache>()
  const cacheOf = (gi: number): LegCache => { let c = probeCache.get(gi); if (c === undefined) { c = mkLegCache(); probeCache.set(gi, c) } return c }
  // A touched leg's shape under a probe. `warm` = the envelope-theorem fast path
  // (fixed-turn Newton from the tick base, plan 22): CORRECT for the FIRST-ORDER
  // gradient at the base, so it is used ONLY for the ±HX central-difference
  // gradient probes (a 0.02 move always closes). It is NOT valid for the accept
  // test — warm can undercut the grid min (the scan is not a guaranteed global
  // optimizer; a far-moved warm closeAt need not close), so a warm-lowering ACCEPT
  // can raise the true grid total (measured: pc0 drift 0→37). Every accept/reject
  // uses the true memoryless GRID solve, keeping the grid total monotone.
  const solveTouched = (r: LegRec, warm: boolean): LegShape =>
    warm ? resolveLeg(e, r.w, r.leg, r.leg.cache, r.shape.sol) : resolveLeg(e, r.w, r.leg, cacheOf(r.gi))
  // Refresh a moved body's touched-leg SAMPLES in the shared snapshot: coordinate
  // descent moves bodies one at a time, so a leg another body's gate reads for the
  // wire↔wire separation / clearance terms must reflect this tick's earlier moves,
  // not the tick-start trace. Skipping this leaves those terms STALE and a gate
  // lowers a wrong local proxy while the true total rises — a small limit cycle
  // that net-drifts wire-owned dots (measured: threeWay's clustered ∃ tips
  // conveyor 24 wu at oscillating E; refreshing makes them rest, E monotone).
  const refresh = (r: LegRec): void => {
    const shape = resolveLeg(e, r.w, r.leg, cacheOf(r.gi))
    r.samples.length = 0
    traceLeg(shape, r.samples, QN)
  }
  // The localized WIRE energy of a set of touched legs (leg intrinsic +
  // clearance, cross-wire separation, optional junction trunk alignment + ∃-tip
  // standoff).
  // Content (sibling + scope-ring) and the boundary exit→slot terms are added by
  // the translation gates via contentEnergy + boundaryExitE, never here.
  const localE = (touched: readonly LegRec[], farBody: Body | null, hubWire: WireView | null, warm = false): number => {
    let E = 0
    const touchedSet = new Set(touched.map((r) => r.gi))
    const probeSamples = new Map<number, Vec2[]>()
    touched.forEach((r, idx) => {
      const shape = solveTouched(r, warm)
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
    if (hubWire !== null) E += trunkAlignE(e, hubWire)
    // ∃-tip standoff for EVERY touched tip leg: a node with several dangling ∃
    // ports moves ALL their port anchors at once, so its gate must see all their
    // standoffs — accounting for only one lowers a wrong proxy and orbits the
    // omitted tips (measured: threeWay's multi-dangle refs conveyor an ∃ dot).
    for (const r of touched) if (r.leg.b.kind === 'tip') E += tipStandoffE(e, r.w)
    return E
  }

  // The full content + frame-coupling energy a TRANSLATION gate must add to its
  // local wire energy: moving any body changes the derived region circles (its
  // sibling gaps) and the derived sheet frame (every boundary slot), so the whole
  // content functional and every exit-hub→slot term are re-evaluated per probe.
  const contentFrame = (): number => contentEnergy(e) + boundaryExitE(e)

  // ---- NODE-body DOF (nodes + empty-region anchors): TRANSLATION by the
  // strict gated candidate step (with legality projection + content/frame
  // energy); ROTATION by the same gated step over the wire legs alone (the
  // centre is fixed, so content and frame are rotation-invariant). ----
  for (const b of e.bodies.values()) {
    if (b.kind !== 'ref' && b.kind !== 'term' && b.kind !== 'atom' && b.kind !== 'anchor') continue
    if (pinned !== null && pinned.has(b.id)) continue
    const touched = bindLegs.get(b.id) ?? []
    // anchors carry no disc in the clearance integral (invisible carriers), so
    // they pass no farBody; their only energy is the sibling term via contentFrame
    const far = b.kind === 'anchor' ? null : b
    const dirty = new Set<RegionId>([b.region])
    const gradE = (): number => { recomputeRegions(e, dirty); return localE(touched, far, null, true) + contentFrame() }
    const energy = (): number => { recomputeRegions(e, dirty); return localE(touched, far, null) + contentFrame() }
    dofs.push(() => {
      gatedMove(() => b.pos, (p) => { b.pos = p }, (p) => projectBodyPos(e, b, p), gradE, energy, MU, WIREP.travelCap)
      if (touched.length > 0) {
        // rotation crosses the wrench ridge via the long-shot ladder and settles on
        // the strict gate; rotational mobility scales with 1/area.
        gatedStep(() => b.theta, (v) => { b.theta = v }, () => localE(touched, null, null), HX / b.discR, (4 * MU) / (b.discR * b.discR), 0.28)
      }
      for (const r of touched) refresh(r)
    })
  }
  // ---- wire-owned TRANSLATION DOF: ∃ tips, ∀ via-body hubs, boundary exit hubs.
  // Same strict gated candidate step; ∃ tips + exit hubs are light and mobile
  // (float to a scope standoff / frame slot), a ∀ via-body is heavier/slower. ----
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    if (pinned !== null && pinned.has(b.id)) continue
    const w = e.wires.get(b.id.slice(2))
    if (w === undefined) continue // a bare ∃ dot — no legs
    const wLegs = legsOfWire.get(b.id.slice(2))!
    let touched: LegRec[]
    let light: boolean
    if (w.tipBodyId === b.id) { touched = wLegs.filter((r) => r.leg.b.kind === 'tip'); light = true }
    else if (w.hub !== null && w.hub.kind === 'body' && w.hub.bodyId === b.id) {
      touched = wLegs.filter((r) => r.leg.b.kind === 'hub')
      light = w.slot !== null // a boundary exit hub is light + slot-drawn; a ∀ via-body is heavy
    }
    else continue
    const dirty = new Set<RegionId>([b.region])
    // ∃ tips / ∀ hubs are FEW, so their gate uses the exact grid solve for the
    // gradient too: their legs are free-end (arrival tangent is a scanned dummy),
    // where the fixed-turn warm gradient points wrong and fights the grid accept
    // into a small limit cycle (measured: an ∃ tip cycling E ±0.4 forever).
    const energy = (): number => { recomputeRegions(e, dirty); return localE(touched, null, null) + contentFrame() }
    dofs.push(() => {
      gatedMove(() => b.pos, (p) => { b.pos = p }, (p) => projectBodyPos(e, b, p), energy, energy, light ? 3 * MU : MU, light ? 0.55 : 0.28)
      for (const r of touched) refresh(r)
    })
  }
  // trunk-AXIS DOF (interior hubs): the hub orientation `phi` is a stiff/slow
  // gated angle (cap 0.06 = the no-flip inertia) over the ONLY terms it enters —
  // trunk-axis nematic anchoring + trunk alignment. Cheap: no leg re-solve, since
  // `phi` shapes no leg directly (it only moves each leg's arrival TARGET, which
  // the per-leg angle DOF then chases).
  for (const [wid, w] of e.wires) {
    void wid
    if (w.hub === null || w.slot !== null) continue
    dofs.push(() => {
      gatedStep(() => w.phi, (v) => { w.phi = v }, () => trunkAxisE(e, w) + trunkAlignE(e, w), HX / 8, MU / 64, 0.06)
    })
  }
  // hub points (branch junctions)
  for (const [wid, w] of e.wires) {
    if (w.hub === null || w.hub.kind !== 'point') continue
    const hub = w.hub
    const touched = legsOfWire.get(wid)!.filter((r) => r.leg.b.kind === 'hub')
    dofs.push(() => {
      gatedPoint(hub, () => localE(touched, null, null), MU, 0.28)
      for (const r of touched) refresh(r)
    })
  }
  // per-leg arrival angles (stiff/slow: MU/64, cap 0.06)
  for (const [wid, w] of e.wires) {
    if (w.hub === null) continue
    for (const rec of legsOfWire.get(wid)!) {
      if (rec.leg.b.kind !== 'hub') continue
      const leg = rec.leg
      dofs.push(() => {
        gatedStep(() => leg.hubAngle, (v) => { leg.hubAngle = v }, () => localE([rec], null, w), HX / 8, MU / 64, 0.06)
        refresh(rec)
      })
    }
  }
  return dofs
}

// GATED GLOBAL-ROTATION DOF (framed alignment). Absolute orientation IS
// observable on a framed diagram (the slots are world-anchored compass points),
// so it is a live DOF, not a zero mode: rotate the content — every body EXCEPT
// the boundary exit hubs (`e:`, the fixed frame terminals), plus wire hub points
// and world-frame arrival angles — about the content centroid by the strictly
// E-lowering angle. Holding the exit hubs fixed turns each port RELATIVE to its
// hub, dissolving a blind-cone coil when a port faces away from its slot. On a
// frameless layout there are no boundary legs, so the gate is a no-op and skips.
// It gates on the FULL total energy with the memoryless grid solve (a near-tie
// scene needs the interior branch flip the grid finds; content energy is
// rotation-invariant about the centroid, so it only sharpens the same argmin).
// Runs once per completed sweep (a full tick), never mid-slice.
function globalRotationDof(e: Engine, pinned: ReadonlySet<string> | null): void {
  if (pinned === null && e.boundary.length > 0 && e.bodies.size > 1) {
    let gcx = 0, gcy = 0, gn = 0
    for (const b of e.bodies.values()) if (b.kind !== 'junction') { gcx += b.pos.x; gcy += b.pos.y; gn++ }
    if (gn > 0) {
      gcx /= gn; gcy /= gn
      const bodySnap = [...e.bodies.values()].filter((b) => !b.id.startsWith('e:')).map((b) => ({ b, pos: b.pos, theta: b.theta }))
      const hubSnap = [...e.wires.values()].filter((w) => w.hub !== null && w.hub.kind === 'point').map((w) => { const h = w.hub as { pos: Vec2 }; return { h, pos: h.pos } })
      const angSnap: { leg: WireLeg; a: number }[] = []
      for (const w of e.wires.values()) for (const leg of w.legs) if (leg.b.kind === 'hub') angSnap.push({ leg, a: leg.hubAngle })
      const applyRot = (d: number): void => {
        const cs = Math.cos(d), sn = Math.sin(d)
        for (const s of bodySnap) {
          const rx = s.pos.x - gcx, ry = s.pos.y - gcy
          s.b.pos = { x: gcx + rx * cs - ry * sn, y: gcy + rx * sn + ry * cs }
          s.b.theta = s.theta + d
        }
        for (const s of hubSnap) {
          const rx = s.pos.x - gcx, ry = s.pos.y - gcy
          s.h.pos = { x: gcx + rx * cs - ry * sn, y: gcy + rx * sn + ry * cs }
        }
        for (const s of angSnap) s.leg.hubAngle = s.a + d
      }
      const gateE = (): number => { recomputeRegions(e); return totalEnergy(e) }
      let applied = 0
      gatedStep(() => applied, (v) => { applyRot(v); applied = v }, gateE, HX, MU, 0.28)
      recomputeRegions(e)
    }
  }
}

/** Advance one strict-descent SWEEP over the DOF worklist, optionally time-sliced.
    Resumes at `e.descentCursor` and stops when `deadline` (a performance.now() ms
    stamp) is reached; `deadline === null` runs the sweep to completion. Returns
    true iff the sweep COMPLETED this call (the caller's cue to run the
    once-per-tick global-rotation DOF and count the tick). */
function descentSweep(e: Engine, pinned: ReadonlySet<string> | null, deadline: number | null): boolean {
  const dofs = descentDofs(e, pinned)
  let i = e.descentCursor
  if (i >= dofs.length) i = 0 // DOF count shrank (a pin toggled) — restart the sweep
  for (; i < dofs.length; i++) {
    dofs[i]!()
    if (deadline !== null && i + 1 < dofs.length && performance.now() >= deadline) {
      e.descentCursor = i + 1
      return false
    }
  }
  e.descentCursor = 0
  return true
}

/** One relaxation tick — STRICT TOTAL-ENERGY DESCENT (plan 23), the USER's
    ruling made structural: the system changes only when the change lowers the
    one total energy. Every DOF is a strictly E-gated candidate step (the descent
    sweep + the global-rotation DOF); there is no velocity integration, no
    independent overlap mover, and no zero-mode quotient — the injectors those
    quotients corrected (the per-tick projection's spurious spin, the slot pull's
    net thrust) are gone with the un-gated movers, so total E is monotone
    non-increasing across the whole tick. Deterministic: no randomness, seed from
    mkEngine's spiral. `pinned` bodies are held by the caller and skipped by every
    gate; the layout relaxes around them. Runs a COMPLETE sweep every call (the
    headless/settle/test contract); the app uses `settleStepBudget` to time-slice. */
export function settleStep(e: Engine, pinned: ReadonlySet<string> | null = null): void {
  e.descentCursor = 0 // a full tick is always a fresh complete sweep
  recomputeRegions(e)
  descentSweep(e, pinned, null)
  recomputeRegions(e)
  globalRotationDof(e, pinned)
  e.tick++
}

/** One BUDGETED relaxation step for the app frame loop (the anytime frame budget):
    advance the descent sweep only until `deadline` (performance.now() ms), resuming
    across frames via `e.descentCursor`, so an interactive frame pays a bounded slice
    of a sweep instead of the whole 200–450 ms tick. When a sweep COMPLETES, run the
    global-rotation DOF and count the tick; a mid-sweep frame defers both to the frame
    the sweep finishes on. Every accepted move still strictly lowers total E, so
    slicing changes only WHEN work happens, never the monotone-descent law. */
export function settleStepBudget(e: Engine, pinned: ReadonlySet<string> | null, deadline: number): void {
  recomputeRegions(e)
  const done = descentSweep(e, pinned, deadline)
  recomputeRegions(e)
  if (done) {
    globalRotationDof(e, pinned)
    e.tick++
  }
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
    rewrite constructs overlapping after the descent has run. */
export function settle(e: Engine, ticks: number): void {
  recomputeRegions(e)
  resolveOverlaps(e)
  for (let t = 0; t < ticks; t++) settleStep(e)
  recomputeRegions(e)
  resolveOverlaps(e)
}
