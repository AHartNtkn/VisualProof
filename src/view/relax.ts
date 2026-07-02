import type { RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine } from './engine'
import { pkey, subtreeCarriers, worldAnchor } from './engine'

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
export const SIB_GAP = 5

// Relaxation coefficients. Not correctness heuristics: any positive values give
// a valid equilibrium of the same constraint system; they tune visual pacing.
const DT = 0.06
const DAMP = 4
const REP = 900
const SPRING = 2.2
const ROT_BLEND = 0.15
const REST = 18
/** The soft-force bound: every SOFT pull (sibling attraction, leg-spring
    tension) saturates at this one magnitude — the old linear cohesion
    evaluated at one leg rest-length (0.65·REST), no new scale. An unbounded
    soft force can outpull every bounded one and drive a permanent conveyor:
    a leg spring stretched across a region ring (its geometric length must
    exceed the rest length) would otherwise drag body + enclosing circle +
    junction across the sheet forever — minimal enclosing circles exert no
    inward wall, so only the sibling attraction anchors content, and it can
    hold precisely because nothing soft can exceed it. */
const SOFT_MAX = 0.65 * REST
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
        const ca = centerOf(A), cb = centerOf(B)
        const dx = cb.x - ca.x, dy = cb.y - ca.y
        const dist = Math.hypot(dx, dy)
        const need = A.r + B.r + SIB_GAP
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

type LegRef = { key: string; other: Body; otherKey: string | null }

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

  // Sibling pair force from ONE potential: repulsive below the target gap,
  // zero at it, constant-force attractive beyond (the smooth corner ramps over
  // one further SIB_GAP). One curve for what used to be repulsion + cohesion +
  // a contact fade: the position force field is a GRADIENT, and a gradient
  // flow with damping cannot cycle — the previous two-curve arrangement had
  // knife-edge equilibria whose stiffness grew with region size, and large
  // diagrams chattered on them forever. The attraction saturates at a
  // constant (anchored to the leg rest-length — no new scale), so compaction
  // has a pace, not a spring; pairs rest exactly at the potential minimum.
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
      // φ'(g): negative = repulsion (below G0), positive = attraction.
      // Repulsive branch is the old 1/(g+8)² law shifted to vanish at G0;
      // attractive branch ramps to COHESION over [G0, 2·G0] and stays there.
      const G0 = 2 * SIB_GAP
      const f = gap < G0
        ? -(REP / Math.max(gap + 8, 4) ** 2 - REP / (G0 + 8) ** 2)
        : SOFT_MAX * Math.min(1, (gap - G0) / G0)
      const ux = dx / dist, uy = dy / dist
      // Each side receives a TOTAL of ±f shared among its subtree members
      // (equal-and-opposite by construction — unshared application would
      // inject (N−1)·f of net momentum per contact per tick). A pinned
      // (dragged) side takes no attraction — the drag must feel direct —
      // but repulsion still applies so a drag cannot tunnel through things.
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

  // Leg springs with a rest length, acting AT THE ANCHORS: the pair exchanges
  // equal-and-opposite forces along the anchor-to-anchor line (zero net torque
  // on the drawing by construction — collinear application points), and the
  // moment (anchor − center) × F becomes SPIN torque on the body's own θ.
  // Applying the same force at the centers instead leaves that moment as an
  // orbital couple on the whole layout: with multi-leg bodies the couples
  // never all vanish at rest, and the drawing spins forever.
  const torque = new Map<string, number>()
  for (const id of e.bodies.keys()) torque.set(id, 0)
  for (const leg of e.legs) {
    const A = e.bodies.get(leg.from.body)!, B = e.bodies.get(leg.to.body)!
    if (A === B) continue
    const pa = worldAnchor(A, leg.from.key), pb = worldAnchor(B, leg.to.key)
    const dx = pb.x - pa.x, dy = pb.y - pa.y
    const dist = Math.max(Math.hypot(dx, dy), 0.5)
    const stretch = dist - REST
    const f = Math.sign(stretch) * Math.min(SPRING * Math.abs(stretch), SOFT_MAX) / dist
    const FA = force.get(A.id)!, FB = force.get(B.id)!
    FA.x += dx * f; FA.y += dy * f
    FB.x -= dx * f; FB.y -= dy * f
    const rax = pa.x - A.pos.x, ray = pa.y - A.pos.y
    const rbx = pb.x - B.pos.x, rby = pb.y - B.pos.y
    torque.set(A.id, torque.get(A.id)! + rax * dy * f - ray * dx * f)
    torque.set(B.id, torque.get(B.id)! + rbx * -dy * f - rby * -dx * f)
  }

  for (const b of e.bodies.values()) {
    const F = force.get(b.id)!
    b.vel = { x: (b.vel.x + F.x * DT) / (1 + DAMP * DT), y: (b.vel.y + F.y * DT) / (1 + DAMP * DT) }
    b.pos = { x: b.pos.x + b.vel.x * DT, y: b.pos.y + b.vel.y * DT }
  }

  // spin: overdamped rotation under the accumulated anchor torques
  // (rotational drag scales with the disc area, the rotational analogue of
  // the translational damping)
  for (const b of e.bodies.values()) {
    const tq = torque.get(b.id)!
    if (tq !== 0) b.theta += (tq / (DAMP * b.discR * b.discR)) * DT
  }

  // boundary exits keep a kinematic aim (there is no spring to take a torque
  // from): the exit body rotates its port normal OUTWARD along the radial
  // from the sheet center through the body. The radial is continuous in
  // position and independent of θ — an anchor- or nearest-edge-derived
  // target feeds back through θ (the anchor moves as the body rotates) and
  // flips discontinuously near the frame diagonals, which sustains a chase
  // oscillation that never rests.
  const legsByBody = new Map<string, LegRef[]>()
  const push = (body: string, ref: LegRef): void => {
    let ls = legsByBody.get(body)
    if (ls === undefined) { ls = []; legsByBody.set(body, ls) }
    ls.push(ref)
  }
  const sheetG = e.regions.get(e.d.root)
  for (const [wid, bid] of e.boundaryOf) {
    const b = e.bodies.get(bid)!
    if (b.kind === 'junction' || sheetG === undefined) continue
    const w0 = e.d.wires[wid]!
    const key = pkey(w0.endpoints.find((ep) => ep.node === bid)!.port)
    const dx = b.pos.x - sheetG.center.x, dy = b.pos.y - sheetG.center.y
    const rr = Math.hypot(dx, dy)
    const q = rr < 1e-9
      ? { x: sheetG.center.x + sheetG.radius, y: sheetG.center.y }
      : { x: b.pos.x + (dx / rr) * sheetG.radius, y: b.pos.y + (dy / rr) * sheetG.radius }
    push(bid, { key, other: { ...b, id: '__frame__', pos: q }, otherKey: null })
  }
  for (const b of e.bodies.values()) {
    const ls = legsByBody.get(b.id)
    if (ls === undefined || ls.length === 0) continue
    let sinS = 0, cosS = 0
    for (const l of ls) {
      if (l.other.id === b.id) continue
      const q = worldAnchor(l.other, l.otherKey)
      const want = Math.atan2(q.y - b.pos.y, q.x - b.pos.x)
      const a = b.localAnchor.get(l.key)!
      const rest = Math.atan2(a.y, a.x)
      const delta = want - rest - b.theta
      sinS += Math.sin(delta); cosS += Math.cos(delta)
    }
    b.theta += Math.atan2(sinS, cosS) * ROT_BLEND
  }

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
