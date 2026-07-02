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
    if (discs.length === 0) { e.regions.set(rid, { center: { x: 0, y: 0 }, radius: 10 }); continue }
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
  let moved = false
  for (const rid of e.regions.keys()) {
    const items: { sub: RegionId | null; id: string; c: Vec2; r: number }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      items.push({ sub: null, id: mid, c: b.pos, r: b.discR })
    }
    for (const c of e.childrenOf.get(rid)!) {
      const g = e.regions.get(c)!
      items.push({ sub: c, id: c, c: g.center, r: g.radius })
    }
    for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
      const A = items[i]!, B = items[j]!
      const dx = B.c.x - A.c.x, dy = B.c.y - A.c.y
      const dist = Math.hypot(dx, dy) || 0.001
      const need = A.r + B.r + SIB_GAP
      if (dist < need) {
        const push = (need - dist) / 2 + 0.1
        const ux = dx / dist, uy = dy / dist
        const move = (it: typeof A, sx: number, sy: number): void => {
          if (it.sub === null) {
            const b = e.bodies.get(it.id)!
            b.pos = { x: b.pos.x + sx, y: b.pos.y + sy }
          } else shiftSubtree(e, it.sub, sx, sy)
        }
        move(A, -ux * push, -uy * push)
        move(B, ux * push, uy * push)
        moved = true
      }
    }
  }
  if (moved) recomputeRegions(e)
  return moved
}

type LegRef = { key: string; other: Body; otherKey: string | null }

/** One relaxation tick — force integration + rotation + periodic projection.
    Deterministic: no randomness, seed comes from mkEngine's spiral. A `pinned`
    body is excluded from the cohesion pull so a drag holding it at the cursor
    feels direct (the caller overrides its position each tick). */
export function settleStep(e: Engine, pinned: string | null = null): void {
  recomputeRegions(e)
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
      const apply = (D: typeof A, sx: number, sy: number): void => {
        const targets = D.mid !== undefined ? [D.mid] : subtreeMembers(e, D.sub!)
        for (const mid of targets) { const F = force.get(mid)!; F.x += sx; F.y += sy }
      }
      apply(A, -ux * f, -uy * f)
      apply(B, ux * f, uy * f)
    }
  }

  // leg springs with a rest length: legs approach one spatial rhythm
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
    for (const mid of mids) {
      if (mid === pinned) continue // a dragged body is not pulled toward the centroid
      const b = e.bodies.get(mid)!
      const F = force.get(mid)!
      F.x += (cen.x - b.pos.x) * 0.65; F.y += (cen.y - b.pos.y) * 0.65
    }
    for (const c of kids) {
      const g = e.regions.get(c)!
      const pull = { x: (cen.x - g.center.x) * 0.35, y: (cen.y - g.center.y) * 0.35 }
      for (const mid of subtreeMembers(e, c)) { const F = force.get(mid)!; F.x += pull.x; F.y += pull.y }
    }
  }

  for (const b of e.bodies.values()) {
    const F = force.get(b.id)!
    b.vel = { x: (b.vel.x + F.x * DT) / (1 + DAMP * DT), y: (b.vel.y + F.y * DT) / (1 + DAMP * DT) }
    b.pos = { x: b.pos.x + b.vel.x * DT, y: b.pos.y + b.vel.y * DT }
  }

  // rotation toward the circular mean of leg-direction mismatches
  const legsByBody = new Map<string, LegRef[]>()
  const push = (body: string, ref: LegRef): void => {
    let ls = legsByBody.get(body)
    if (ls === undefined) { ls = []; legsByBody.set(body, ls) }
    ls.push(ref)
  }
  for (const leg of e.legs) {
    if (leg.from.key !== null) push(leg.from.body, { key: leg.from.key, other: e.bodies.get(leg.to.body)!, otherKey: leg.to.key })
    if (leg.to.key !== null) push(leg.to.body, { key: leg.to.key, other: e.bodies.get(leg.from.body)!, otherKey: leg.from.key })
  }
  // boundary exits contribute rotation torque: the exit body wants its port
  // normal aimed at its nearest frame edge (approximated by the sheet box)
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

  if (e.tick % 10 === 0) resolveOverlaps(e)
  e.tick++
}

/** Run a tick budget, then project to a fully legal (overlap-free) drawing. */
export function settle(e: Engine, ticks: number): void {
  for (let t = 0; t < ticks; t++) settleStep(e)
  recomputeRegions(e)
  for (let k = 0; k < 400 && resolveOverlaps(e); k++) { /* push to a legal drawing */ }
}
