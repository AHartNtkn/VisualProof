/** Plain 3D vector math for the 3D tree view. Pure; no three.js types. */
export type Vec3 = { readonly x: number; readonly y: number; readonly z: number }

export const v3 = (x: number, y: number, z: number): Vec3 => ({ x, y, z })
export const add3 = (a: Vec3, b: Vec3): Vec3 => v3(a.x + b.x, a.y + b.y, a.z + b.z)
export const sub3 = (a: Vec3, b: Vec3): Vec3 => v3(a.x - b.x, a.y - b.y, a.z - b.z)
export const scale3 = (a: Vec3, k: number): Vec3 => v3(a.x * k, a.y * k, a.z * k)
export const dot3 = (a: Vec3, b: Vec3): number => a.x * b.x + a.y * b.y + a.z * b.z
export const cross3 = (a: Vec3, b: Vec3): Vec3 =>
  v3(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x)
export const len3 = (a: Vec3): number => Math.hypot(a.x, a.y, a.z)
export const dist3 = (a: Vec3, b: Vec3): number => len3(sub3(a, b))
export const lerp3 = (a: Vec3, b: Vec3, t: number): Vec3 =>
  v3(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t, a.z + (b.z - a.z) * t)

export function norm3(a: Vec3): Vec3 {
  const l = len3(a)
  if (l === 0) throw new Error('norm3: zero vector')
  return scale3(a, 1 / l)
}

/** A deterministic unit vector perpendicular to `u` (crosses with the axis
    least aligned with `u`, so the result is never degenerate). */
export function anyPerp(u: Vec3): Vec3 {
  const ax = Math.abs(u.x), ay = Math.abs(u.y), az = Math.abs(u.z)
  const pick = ax <= ay && ax <= az ? v3(1, 0, 0) : ay <= az ? v3(0, 1, 0) : v3(0, 0, 1)
  return norm3(cross3(u, pick))
}

/** Rodrigues rotation of `p` about unit `axis` by `angle`. */
export function rotateAbout(p: Vec3, axis: Vec3, angle: number): Vec3 {
  const k = norm3(axis)
  const c = Math.cos(angle), s = Math.sin(angle)
  return add3(
    add3(scale3(p, c), scale3(cross3(k, p), s)),
    scale3(k, dot3(k, p) * (1 - c)),
  )
}

/** Closest point to `p` on segment [a,b] (handles the degenerate a=b). */
export function segClosest(p: Vec3, a: Vec3, b: Vec3): Vec3 {
  const ab = sub3(b, a)
  const denom = dot3(ab, ab)
  if (denom === 0) return a
  const t = Math.min(1, Math.max(0, dot3(sub3(p, a), ab) / denom))
  return add3(a, scale3(ab, t))
}

export const segPointDist = (p: Vec3, a: Vec3, b: Vec3): number => dist3(p, segClosest(p, a, b))

const clamp01 = (x: number): number => Math.min(1, Math.max(0, x))

/** Closest-approach points between two segments [p1,q1] and [p2,q2]:
    [pointOnFirst, pointOnSecond]. Standard robust closest-point-between-
    segments construction (Ericson, Real-Time Collision Detection §5.1.9):
    parametrize each segment by s, t ∈ [0,1], minimize the squared distance
    of a convex quadratic over the unit square, degenerate-safe when either
    segment collapses to a point. */
export function segSegClosest(p1: Vec3, q1: Vec3, p2: Vec3, q2: Vec3): [Vec3, Vec3] {
  const d1 = sub3(q1, p1)
  const d2 = sub3(q2, p2)
  const r = sub3(p1, p2)
  const a = dot3(d1, d1)
  const e = dot3(d2, d2)
  const f = dot3(d2, r)
  const EPS = 1e-12
  let s: number, t: number
  if (a <= EPS && e <= EPS) {
    s = 0
    t = 0
  } else if (a <= EPS) {
    s = 0
    t = clamp01(f / e)
  } else {
    const c = dot3(d1, r)
    if (e <= EPS) {
      t = 0
      s = clamp01(-c / a)
    } else {
      const b = dot3(d1, d2)
      const denom = a * e - b * b
      s = denom > EPS ? clamp01((b * f - c * e) / denom) : 0
      t = (b * s + f) / e
      if (t < 0) {
        t = 0
        s = clamp01(-c / a)
      } else if (t > 1) {
        t = 1
        s = clamp01((b - c) / a)
      }
    }
  }
  return [add3(p1, scale3(d1, s)), add3(p2, scale3(d2, t))]
}

/** Closest-approach distance between two segments [p1,q1] and [p2,q2]. */
export function segSegDist(p1: Vec3, q1: Vec3, p2: Vec3, q2: Vec3): number {
  const [c1, c2] = segSegClosest(p1, q1, p2, q2)
  return dist3(c1, c2)
}
