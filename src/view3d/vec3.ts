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
