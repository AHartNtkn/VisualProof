import type { WireId } from '../kernel/diagram/diagram'
import {
  add3, anyPerp, cross3, dist3, len3, norm3, scale3, segClosest, segPointDist, sub3, v3, type Vec3,
} from './vec3'

export type Capsule = { a: Vec3; b: Vec3; r: number }
export type EdgeIn = { p: Vec3; q: Vec3; tp: Vec3 | null; tq: Vec3 | null }
export type NetIn = { id: WireId; edges: EdgeIn[] }

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
    for (let i = 0; i < pts.length; i++) {
      if (isExempt(pts[i]!, exempt, delta)) continue
      const hits = penetrations(pts[i]!, obstacles, delta)
      if (hits.length === 0) continue
      if (i === 0 || i === pts.length - 1) {
        // A fixed terminal inside an obstacle with no exemption is
        // unroutable — no push can move it, so leave the round dirty and
        // let the round cap throw loudly instead of accepting the contact.
        dirty = true
        continue
      }
      pts[i] = pushOut(pts[i]!, hits, obstacles, delta)
      dirty = true
    }
    if (!dirty) return pts // the scan above just verified every sample clear
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

export function routeAll(nets: NetIn[], tree: Capsule[], exempt: Vec3[], delta: number): Map<WireId, Vec3[][]> {
  const obstacles: Capsule[] = [...tree]
  const out = new Map<WireId, Vec3[][]>()
  for (const net of nets) {
    const curves: Vec3[][] = []
    const ownCaps: Capsule[] = []
    net.edges.forEach((edge, i) => {
      const pts = repair(hermiteSeed(edge, delta), [...obstacles, ...ownCaps], exempt, delta, `${net.id}[${i}]`)
      curves.push(pts)
      ownCaps.push(...chainOf(pts))
    })
    out.set(net.id, curves)
    obstacles.push(...ownCaps)
  }
  return out
}
