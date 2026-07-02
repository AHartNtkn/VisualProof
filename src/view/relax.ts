import type { RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine } from './engine'
import { pkey, worldAnchor } from './engine'

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
/** Per-call sweep budget for the overlap projection (work bound per tick;
    projection runs every tick, so any residual finishes on later ticks). */
const PROJECTION_PASSES = 60

export function recomputeRegions(e: Engine): void {
  const order: RegionId[] = []
  const visit = (rid: RegionId): void => { for (const c of e.childrenOf.get(rid)!) visit(c); order.push(rid) }
  visit(e.d.root)
  for (const rid of order) {
    const discs: { c: Vec2; r: number }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      discs.push({ c: b.pos, r: b.discR })
    }
    for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius + REGION_PAD * 0.8 })
    if (discs.length === 0) {
      // An empty leaf region has no member to derive a center from: its center
      // IS its positional state, preserved across recomputes and moved by
      // shiftSubtree/projection like any other carrier. Resetting it here
      // would pin every empty cut to the origin, immovably and illegally.
      const prev = e.regions.get(rid)
      e.regions.set(rid, { center: prev === undefined ? { x: 0, y: 0 } : { x: prev.center.x, y: prev.center.y }, radius: 10 })
      continue
    }
    // true minimal enclosing circle of the member discs: subgradient descent
    // on the convex objective f(c) = max_i (|c - c_i| + r_i)
    const center = { x: 0, y: 0 }
    for (const m of discs) { center.x += m.c.x; center.y += m.c.y }
    center.x /= discs.length; center.y /= discs.length
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
    let radius = 10
    for (const m of discs) radius = Math.max(radius, Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r + REGION_PAD)
    e.regions.set(rid, { center, radius })
  }
}

function shiftSubtree(e: Engine, rid: RegionId, dx: number, dy: number): void {
  const g = e.regions.get(rid)
  if (g !== undefined) e.regions.set(rid, { center: { x: g.center.x + dx, y: g.center.y + dy }, radius: g.radius })
  for (const mid of e.membersOf.get(rid)!) {
    const b = e.bodies.get(mid)!
    b.pos = { x: b.pos.x + dx, y: b.pos.y + dy }
  }
  for (const c of e.childrenOf.get(rid)!) shiftSubtree(e, c, dx, dy)
}

function emptyLeafRegions(e: Engine): RegionId[] {
  const out: RegionId[] = []
  for (const rid of e.regions.keys()) {
    if (e.membersOf.get(rid)!.length === 0 && e.childrenOf.get(rid)!.length === 0) out.push(rid)
  }
  return out
}

/** Positional state carriers in a subtree: member bodies, plus one per empty
    leaf region (whose center is its own state). Used as the mass of a subtree
    in projections — a region is as heavy as what actually moves with it. */
function subtreeCarriers(e: Engine, rid: RegionId): number {
  const mids = e.membersOf.get(rid)!
  const kids = e.childrenOf.get(rid)!
  if (mids.length === 0 && kids.length === 0) return 1
  let n = mids.length
  for (const c of kids) n += subtreeCarriers(e, c)
  return n
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
        const mA = A.sub === null ? 1 : subtreeCarriers(e, A.sub)
        const mB = B.sub === null ? 1 : subtreeCarriers(e, B.sub)
        const wA = mB / (mA + mB), wB = mA / (mA + mB)
        const shift = (it: typeof A, sx: number, sy: number): void => {
          if (it.sub === null) {
            const b = e.bodies.get(it.id)!
            b.pos = { x: b.pos.x + sx, y: b.pos.y + sy }
          } else {
            shiftSubtree(e, it.sub, sx, sy)
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
    recomputeRegions(e)
  }
  return any
}

type LegRef = { key: string; other: Body; otherKey: string | null }

/** One relaxation tick — force integration + rotation + periodic projection.
    Deterministic: no randomness, seed comes from mkEngine's spiral. A `pinned`
    body is excluded from the cohesion pull so a drag holding it at the cursor
    feels direct (the caller overrides its position each tick). */
export function settleStep(e: Engine, pinned: string | null = null): void {
  recomputeRegions(e)
  // snapshot every positional carrier: the end-of-tick quotient of the global
  // rotation zero mode is fitted against this
  const carrierStart: { get(): Vec2; set(p: Vec2): void; p0: Vec2 }[] = []
  for (const b of e.bodies.values()) {
    carrierStart.push({ get: () => b.pos, set: (p) => { b.pos = p }, p0: b.pos })
  }
  for (const rid of emptyLeafRegions(e)) {
    carrierStart.push({
      get: () => e.regions.get(rid)!.center,
      set: (p) => { const g = e.regions.get(rid)!; e.regions.set(rid, { center: p, radius: g.radius }) },
      p0: e.regions.get(rid)!.center,
    })
  }
  // force accumulator: mutable points, not the readonly Vec2 used for state
  const force = new Map<string, { x: number; y: number }>()
  for (const id of e.bodies.keys()) force.set(id, { x: 0, y: 0 })

  // disc repulsion within each region (members + child-region discs)
  for (const rid of e.regions.keys()) {
    const discs: { c: Vec2; r: number; mid?: string; sub?: RegionId }[] = []
    for (const mid of e.membersOf.get(rid)!) discs.push({ c: e.bodies.get(mid)!.pos, r: e.bodies.get(mid)!.discR, mid })
    for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius, sub: c })
    for (let i = 0; i < discs.length; i++) for (let j = i + 1; j < discs.length; j++) {
      const A = discs[i]!, B = discs[j]!
      const dx = B.c.x - A.c.x, dy = B.c.y - A.c.y
      const dist = Math.max(Math.hypot(dx, dy), 1)
      const gap = dist - A.r - B.r
      const f = REP / Math.max(gap + 8, 4) ** 2
      const ux = dx / dist, uy = dy / dist
      // Each side of the pair receives a TOTAL of ±f, shared among the
      // subtree's members (a region is heavier than a lone disc). Adding f to
      // every member instead would make the pair interaction inject
      // (N−1)·f of net momentum per tick — with damping that is a constant
      // thrust, and dense diagrams fly off-screen at terminal velocity.
      const apply = (D: typeof A, sx: number, sy: number): void => {
        const targets = D.mid !== undefined ? [D.mid] : subtreeMembers(e, D.sub!)
        const per = 1 / targets.length
        for (const mid of targets) { const F = force.get(mid)!; F.x += sx * per; F.y += sy * per }
      }
      apply(A, -ux * f, -uy * f)
      apply(B, ux * f, uy * f)
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
    const f = SPRING * (dist - REST) / dist
    const FA = force.get(A.id)!, FB = force.get(B.id)!
    FA.x += dx * f; FA.y += dy * f
    FB.x -= dx * f; FB.y -= dy * f
    const rax = pa.x - A.pos.x, ray = pa.y - A.pos.y
    const rbx = pb.x - B.pos.x, rby = pb.y - B.pos.y
    torque.set(A.id, torque.get(A.id)! + rax * dy * f - ray * dx * f)
    torque.set(B.id, torque.get(B.id)! + rbx * -dy * f - rby * -dx * f)
  }

  // per-region cohesion toward the content centroid
  for (const rid of e.regions.keys()) {
    const mids = e.membersOf.get(rid)!
    const kids = e.childrenOf.get(rid)!
    if (mids.length + kids.length < 2) continue
    const cen = { x: 0, y: 0 }
    let m = 0
    for (const mid of mids) { const b = e.bodies.get(mid)!; cen.x += b.pos.x; cen.y += b.pos.y; m++ }
    for (const c of kids) { const g = e.regions.get(c)!; cen.x += g.center.x; cen.y += g.center.y; m++ }
    cen.x /= m; cen.y /= m
    // Cohesion is a compaction force: it is meaningless once the separation
    // constraint binds. Fade it to zero as a member's nearest-sibling gap
    // approaches SIB_GAP, so a genuine force equilibrium exists (constant
    // cohesion at contact fights the projection forever — a limit cycle).
    const sibDiscs: { c: Vec2; r: number; id: string }[] = []
    for (const mid of mids) { const b = e.bodies.get(mid)!; sibDiscs.push({ c: b.pos, r: b.discR, id: mid }) }
    for (const c of kids) { const g = e.regions.get(c)!; sibDiscs.push({ c: g.center, r: g.radius, id: c }) }
    const cohesionFactor = (id: string, c: Vec2, r: number): number => {
      let nearest = Infinity
      for (const s of sibDiscs) {
        if (s.id === id) continue
        nearest = Math.min(nearest, Math.hypot(s.c.x - c.x, s.c.y - c.y) - s.r - r)
      }
      if (nearest === Infinity) return 1
      return Math.min(1, Math.max(0, (nearest - SIB_GAP) / SIB_GAP))
    }
    // Cohesion is INTERNAL to the region: its resultant over the pulled bodies
    // must be zero, or the region self-propels (the fade factors make the raw
    // pulls asymmetric, so the net does not cancel by itself). Accumulate the
    // pulls, then subtract the mean — relative compaction is unchanged, net
    // thrust is removed exactly.
    const pulls = new Map<string, { x: number; y: number }>()
    const addPull = (mid: string, fx: number, fy: number): void => {
      const p = pulls.get(mid)
      if (p === undefined) pulls.set(mid, { x: fx, y: fy })
      else { p.x += fx; p.y += fy }
    }
    for (const mid of mids) {
      if (mid === pinned) continue // a dragged body is not pulled toward the centroid
      const b = e.bodies.get(mid)!
      const k = 0.65 * cohesionFactor(mid, b.pos, b.discR)
      addPull(mid, (cen.x - b.pos.x) * k, (cen.y - b.pos.y) * k)
    }
    for (const c of kids) {
      const g = e.regions.get(c)!
      const kSub = 0.35 * cohesionFactor(c, g.center, g.radius)
      for (const mid of subtreeMembers(e, c)) {
        addPull(mid, (cen.x - g.center.x) * kSub, (cen.y - g.center.y) * kSub)
      }
    }
    if (pulls.size > 0) {
      let nx = 0, ny = 0
      for (const p of pulls.values()) { nx += p.x; ny += p.y }
      nx /= pulls.size; ny /= pulls.size
      for (const [mid, p] of pulls) {
        const F = force.get(mid)!
        F.x += p.x - nx; F.y += p.y - ny
      }
    }
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
  // from): the exit body rotates its port normal toward its nearest frame
  // edge (approximated by the sheet box)
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
    const p = worldAnchor(b, key)
    const fr = sheetG.radius + 6
    const cand: Vec2[] = [
      { x: sheetG.center.x - fr, y: p.y }, { x: sheetG.center.x + fr, y: p.y },
      { x: p.x, y: sheetG.center.y - fr }, { x: p.x, y: sheetG.center.y + fr },
    ]
    let q = cand[0]!
    for (const c of cand) if (Math.hypot(c.x - p.x, c.y - p.y) < Math.hypot(q.x - p.x, q.y - p.y)) q = c
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

  // project every tick: per-tick motion is small, so corrections stay small —
  // a sparser cadence lets violations accumulate and resolves them as
  // spring-fighting teleports
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
