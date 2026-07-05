import type { RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine } from './engine'
import { frameBounds, frameSlots, subtreeCarriers, worldBindAnchor } from './engine'
import type { ChainDisc } from './wirechain'
import { buildEdgeNear, chainEnergy, chainGradient, pointLocalE, resample, straightenStep, topologyStep, WIREP } from './wirechain'

/** Tension of a point's incident edges (analytic in the gradient; the local
    line-search energies need it explicitly). */
function tensionLocal(ch: { pts: Vec2[]; adj: number[][] }, v: number): number {
  let s = 0
  for (const n of ch.adj[v]!) s += Math.hypot(ch.pts[n]!.x - ch.pts[v]!.x, ch.pts[n]!.y - ch.pts[v]!.y)
  return s
}
export { WIREP } from './wirechain'

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
  /** wire descent step (USER: max responsiveness is right — the line
      searches guard stability, so big steps just settle faster) */
  chainStep: 0.4,
  /** ∃-dot descent step */
  homedStep: 0.15,
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
  for (const ch of e.chains.values()) for (const hm of ch.homed) wireOwnedP.add(hm.bodyId)
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

/** Constraint projection for one chain: bind terminals sit AT their port
    anchors with the first interior point projected onto the port-normal ray
    (the perpendicular-exit law as a constraint, not a spring); homed
    terminals mirror their owning bodies; slot terminals sit at their
    canonical frame slots. */
function pinChain(e: Engine, ch: { pts: Vec2[]; adj: number[][]; binds: { idx: number; body: string; key: string; normal?: number }[]; homed: { idx: number; bodyId: string }[]; slots: { idx: number; slot: number }[] }, slotPts: { point: Vec2 }[] | null): void {
  for (const bind of ch.binds) {
    const b = e.bodies.get(bind.body)!
    const anchor = worldBindAnchor(b, bind.key)
    ch.pts[bind.idx] = anchor
    const a = b.localAnchor.get(bind.key)!
    const normal = Math.atan2(a.y, a.x) + b.theta
    bind.normal = normal
    const nbr = ch.adj[bind.idx]![0]
    if (nbr !== undefined) {
      const p = ch.pts[nbr]!
      // the exit run is VISIBLE (≥ one pitch): with a sub-pixel run the
      // wire visually left the node at an arbitrary angle (USER report)
      const dist = Math.max(2, Math.hypot(p.x - anchor.x, p.y - anchor.y))
      ch.pts[nbr] = { x: anchor.x + Math.cos(normal) * dist, y: anchor.y + Math.sin(normal) * dist }
    }
  }
  for (const hm of ch.homed) ch.pts[hm.idx] = e.bodies.get(hm.bodyId)!.pos
  if (slotPts !== null) for (const s of ch.slots) if (slotPts[s.slot] !== undefined) ch.pts[s.idx] = slotPts[s.slot]!.point
}

/** Total wire energy of the engine — the monotonicity pin's observable. */
export function wireEnergy(e: Engine): number {
  const discs: ChainDisc[] = [...e.bodies.values()]
    .filter((b) => b.kind !== 'junction' && b.kind !== 'anchor')
    .map((b) => ({ id: b.id, pos: b.pos, r: b.discR }))
  let E = 0
  for (const ch of e.chains.values()) E += chainEnergy(ch, discs)
  return E
}

/** One relaxation tick — force integration + rotation + projection.
    Deterministic: no randomness, seed comes from mkEngine's spiral. `pinned`
    bodies take no sibling attraction so a drag holding them at the cursor
    feels direct (the caller overrides their positions each tick). */
export function settleStep(e: Engine, pinned: ReadonlySet<string> | null = null): void {
  recomputeRegions(e)
  // snapshot every body position: the end-of-tick quotient of the global
  // rotation zero mode is fitted against this
  const carrierStart: { get(): Vec2; set(p: Vec2): void; p0: Vec2 }[] = []
  for (const b of e.bodies.values()) {
    carrierStart.push({ get: () => b.pos, set: (p) => { b.pos = p }, p0: b.pos })
  }
  // force accumulator: mutable points, not the readonly Vec2 used for state
  const force = new Map<string, { x: number; y: number }>()
  for (const id of e.bodies.keys()) force.set(id, { x: 0, y: 0 })

  // Homed wire ends (∃ free ends, ∀-dangle tips) are owned by their WIRE'S
  // energy: the chain's tension + bend + exit constraint fully determine
  // them (no zero mode), so the content anchoring must not park them (USER:
  // dangles must be pulled by their edges). Their sibling pairs skip the
  // attraction branch symmetrically; the barrier stands. A bare ∃ (no
  // chain) keeps full anchoring — nothing else holds it.
  const wireOwned = new Set<string>()
  for (const ch of e.chains.values()) for (const hm of ch.homed) wireOwned.add(hm.bodyId)

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

  // PLAN 21 — the wire chains. Constraints pin terminals (port anchors,
  // homed bodies, frame slots); the chain descends its OWN energy; the
  // wire's pull on the bodies is the TRUE gradient of the chain energy with
  // respect to the body's DOF, INCLUDING the constraint coupling: a
  // translation carries the anchor AND the ray-constrained exit point
  // rigidly (both gradients land on the body), and the θ-gradient is
  // evaluated numerically THROUGH the constraint — an incomplete gradient
  // is a one-sided force and injects energy. Disc↔wire barrier reactions
  // land at disc centers (radial: no torque).
  const torque = new Map<string, number>()
  for (const id of e.bodies.keys()) torque.set(id, 0)
  const fb0 = frameBounds(e)
  const slotPts = fb0 === null ? null : frameSlots(fb0, e.boundary.length)
  const discs: ChainDisc[] = [...e.bodies.values()]
    .filter((b) => b.kind !== 'junction' && b.kind !== 'anchor')
    .map((b) => ({ id: b.id, pos: b.pos, r: b.discR }))
  for (const ch of e.chains.values()) {
    pinChain(e, ch, slotPts)
    // UNIFIED CO-EVOLUTION: one gradient evaluation drives the whole tick.
    // Interior chain points step by it (overdamped, travel-capped); the
    // gradient at pinned points lands on the owning BODY as force + lever
    // torque (the collinear discipline the old leg springs used — the exit
    // point rotates rigidly with the body, so its lever contributes too);
    // barrier reactions land on discs. Splitting the chain into its own
    // converging subsystem was tried and is WRONG: sampled-stale forces
    // between two integrators are nonreciprocal and every configuration
    // found a way to swim with them.
    const rays = new Map<number, { origin: Vec2; angle: number }>()
    for (const bind of ch.binds) {
      const nbr = ch.adj[bind.idx]![0]
      if (nbr === undefined) continue
      const b = e.bodies.get(bind.body)!
      const a = b.localAnchor.get(bind.key)!
      rays.set(nbr, { origin: ch.pts[bind.idx]!, angle: Math.atan2(a.y, a.x) + b.theta })
    }
    const nearMap = buildEdgeNear(ch, discs)
    const grad = chainGradient(ch, discs, nearMap)
    // pinned-point gradients -> body forces + torques (analytic levers)
    for (const bind of ch.binds) {
      const A = e.bodies.get(bind.body)!
      const F = force.get(A.id)!
      const r = grad.f[bind.idx]!
      F.x += r.x
      F.y += r.y
      const pa = ch.pts[bind.idx]!
      let tq = (pa.x - A.pos.x) * r.y - (pa.y - A.pos.y) * r.x
      const nbr = ch.adj[bind.idx]![0]
      if (nbr !== undefined) {
        const rn = grad.f[nbr]!
        // the exit point is ray-locked: it translates AND rotates rigidly
        // with the body — its along-ray component descends on its own, so
        // only the constrained (rigid) share belongs to the body; passing
        // the full gradient double-counts the along-ray part, which the
        // point itself will also act on. Split by projection.
        const ux = Math.cos(rays.get(nbr)!.angle), uy = Math.sin(rays.get(nbr)!.angle)
        const along = rn.x * ux + rn.y * uy
        const px = rn.x - along * ux, py = rn.y - along * uy
        F.x += px
        F.y += py
        const pn = ch.pts[nbr]!
        tq += (pn.x - A.pos.x) * py - (pn.y - A.pos.y) * px
      }
      // the mask's θ-dependence (the exit corridor turns with the body)
      tq += grad.bindTorque.get(bind.idx) ?? 0
      torque.set(A.id, torque.get(A.id)! + tq)
    }
    // homed ∃/∀ bodies are WIRE degrees of freedom: they move at the
    // chain's mobility, not the content integrator's (10× slower — a
    // 40-unit re-contraction at body mobility takes ~44 s of real time).
    // Content forces don't apply; scope containment is an ENERGY here (a
    // soft ring barrier vs child regions, reactions distributed over the
    // region's subtree — the content pattern), with the projection as the
    // final legality guarantee. A hard projection alone against wire
    // tension at a breathing circle is a standing contact cycle (measured
    // on the ∀-shape fixture: +2.7 E swings, 3 wu/200-tick drift).
    for (const hm of ch.homed) {
      const r = { ...grad.f[hm.idx]! }
      const b = e.bodies.get(hm.bodyId)!
      for (const child of e.childrenOf.get(b.region)!) {
        const g = e.regions.get(child)
        if (g === undefined) continue
        const rr = g.radius + b.discR
        const dx = b.pos.x - g.center.x, dy = b.pos.y - g.center.y
        const dd = Math.max(Math.hypot(dx, dy), 1e-9)
        if (dd >= rr + PACE.ringBand) continue
        const mag = PACE.ringSlope * Math.min(1, (rr + PACE.ringBand - dd) / PACE.ringBand)
        const ux = dx / dd, uy = dy / dd
        r.x += ux * mag
        r.y += uy * mag
        const carriers = subtreeCarriers(e, child)
        for (const cid of carriers) {
          const F = force.get(cid)!
          F.x -= (ux * mag) / carriers.length
          F.y -= (uy * mag) / carriers.length
        }
      }
      // stability bound: the dot parks inside the barrier ramp (slope ≈
      // BARRIER_SLOPE over half a clearance ≈ 5/wu) stacked with spacing
      // and bend curvature (~2·SPACING + …); an explicit step is stable
      // only below 2/k_total ≈ 0.08 — at PACE.chainStep (0.15) it overshoots
      // the contact every tick (measured: exact period-2, ±0.8 E)
      let dx = r.x * PACE.homedStep, dy = r.y * PACE.homedStep
      const d = Math.hypot(dx, dy)
      if (d > WIREP.travelCap) {
        dx = (dx / d) * WIREP.travelCap
        dy = (dy / d) * WIREP.travelCap
      }
      // backtracking line search for the tip too: its ring + barrier
      // channels are as stiff as any chain term (an unguarded step here
      // was the ∀-fixture walker's leading edge)
      const ringE = (): number => {
        let s2 = 0
        for (const child of e.childrenOf.get(b.region)!) {
          const g = e.regions.get(child)
          if (g === undefined) continue
          const rr = g.radius + b.discR
          const dd = Math.max(Math.hypot(b.pos.x - g.center.x, b.pos.y - g.center.y), 1e-9)
          if (dd < rr + PACE.ringBand) {
            const pen = rr + PACE.ringBand - dd
            s2 += (PACE.ringSlope / 2) * Math.min(pen, PACE.ringBand) * pen
          }
        }
        return s2
      }
      const tipE = (): number => pointLocalE(ch, discs, hm.idx, nearMap) + tensionLocal(ch, hm.idx) + ringE()
      const p0 = b.pos
      const chainP0 = ch.pts[hm.idx]!
      const e0 = tipE()
      let scale = 1
      for (let t2 = 0; t2 < 4; t2++) {
        b.pos = { x: p0.x + dx * scale, y: p0.y + dy * scale }
        ch.pts[hm.idx] = b.pos
        if (tipE() <= e0 + 1e-9) break
        b.pos = p0
        ch.pts[hm.idx] = chainP0
        scale /= 2
        if (t2 === 3) scale = 0
      }
      b.vel = { x: 0, y: 0 }
    }
    // disc barrier reactions (the other half of the shared term)
    for (const [id, r] of grad.onDiscs) {
      const F = force.get(id)!
      F.x += r.x
      F.y += r.y
    }
    // interior points step by the SAME gradient (overdamped, capped)
    const pinnedIdx = new Set<number>()
    for (const b of ch.binds) pinnedIdx.add(b.idx)
    for (const hm of ch.homed) pinnedIdx.add(hm.idx)
    for (const s of ch.slots) pinnedIdx.add(s.idx)
    for (let v = 0; v < ch.pts.length; v++) {
      if (pinnedIdx.has(v)) continue
      const ray = rays.get(v)
      let dx: number, dy: number
      if (ray !== undefined) {
        const ux = Math.cos(ray.angle), uy = Math.sin(ray.angle)
        const along = (grad.f[v]!.x * ux + grad.f[v]!.y * uy) * PACE.chainStep
        const cur = (ch.pts[v]!.x - ray.origin.x) * ux + (ch.pts[v]!.y - ray.origin.y) * uy
        const next = Math.max(0.5, cur + Math.max(-WIREP.travelCap, Math.min(WIREP.travelCap, along)))
        ch.pts[v] = { x: ray.origin.x + ux * next, y: ray.origin.y + uy * next }
        continue
      }
      dx = grad.f[v]!.x * PACE.chainStep
      dy = grad.f[v]!.y * PACE.chainStep
      const d = Math.hypot(dx, dy)
      if (d > WIREP.travelCap) {
        dx = (dx / d) * WIREP.travelCap
        dy = (dy / d) * WIREP.travelCap
      }
      // BACKTRACKING LINE SEARCH (Gauss–Seidel descent): the move must not
      // raise the point's complete local energy, else halve it (×3) and
      // finally stay. Guarantees per-move descent for EVERY term — the
      // serial per-term stability tunings this replaces are all measured
      // failures (bend 1/l, barrier ramp, mask band each found a mobility
      // × stiffness product to oscillate at).
      // sub-milli steps skip the search: at rest nearly every point takes
      // a ~0 step and the bounded energy error is far inside the band
      if (Math.hypot(dx, dy) < 1e-3) {
        ch.pts[v] = { x: ch.pts[v]!.x + dx, y: ch.pts[v]!.y + dy }
        continue
      }
      const p0 = ch.pts[v]!
      const e0 = pointLocalE(ch, discs, v, nearMap) + tensionLocal(ch, v)
      let scale = 1
      for (let t = 0; t < 4; t++) {
        ch.pts[v] = { x: p0.x + dx * scale, y: p0.y + dy * scale }
        if (pointLocalE(ch, discs, v, nearMap) + tensionLocal(ch, v) <= e0 + 1e-9) break
        ch.pts[v] = p0
        scale /= 2
        if (t === 3) scale = 0
      }
      if (scale === 0) ch.pts[v] = p0
    }
    topologyStep(ch, discs)
    straightenStep(ch, discs)
    resample(ch)
  }

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

  // spin: overdamped rotation under the accumulated anchor torques
  // (rotational drag scales with the disc area, the rotational analogue of
  // the translational damping)
  for (const b of e.bodies.values()) {
    const tq = torque.get(b.id)!
    if (tq !== 0) b.theta += (tq / (PACE.damp * PACE.rotDrag * b.discR * b.discR)) * PACE.dt
  }

  // re-pin after body motion so this tick's drawn chains touch their
  // anchors exactly (constraint projection, incl. the perpendicular exit)
  const fb1 = frameBounds(e)
  const slotPts1 = fb1 === null ? null : frameSlots(fb1, e.boundary.length)
  for (const ch of e.chains.values()) pinChain(e, ch, slotPts1)

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
      // the quotient is a rigid transform of the WHOLE state: chain points
      // rotate with the bodies. Rotating bodies alone twists every chain
      // against its pins each tick; the pins' corrective drag is DIRECTED
      // work — measured as a slow self-propelled conveyor of bound pairs.
      for (const ch of e.chains.values()) {
        for (let k = 0; k < ch.pts.length; k++) {
          const rx = ch.pts[k]!.x - c1x, ry = ch.pts[k]!.y - c1y
          ch.pts[k] = { x: c1x + rx * cs - ry * sn, y: c1y + rx * sn + ry * cs }
        }
      }
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
