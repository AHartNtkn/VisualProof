import { add3, cross3, dist3, norm3, scale3, sub3, v3, type Vec3 } from './vec3'

export type CamPose = { target: Vec3; dist: number; yaw: number; pitch: number }

export const FOV_DEG = 45
const HALF_FOV = (FOV_DEG * Math.PI) / 360
const FIT_MARGIN = 1.15        // breathing room around the fitted sphere
const ORBIT_RATE = 0.008       // rad per pixel dragged
const PITCH_MAX = 1.45         // keep off the poles so the up vector stays valid
const ZOOM_RATE = 0.0012       // exponent per wheel unit
const MIN_DIST = 0.05            // hard floor so zoom can never collapse the eye onto the target

/** `aspect`: viewport width / height. The camera's vertical half-FOV is
    fixed at HALF_FOV; the horizontal half-FOV follows from aspect
    (`atan(tan(HALF_FOV) * aspect)`, matching three.js's PerspectiveCamera).
    Framing must satisfy whichever is smaller — a narrow (portrait)
    viewport is bound by its horizontal FOV, a wide one by its vertical —
    so fitting uses the smaller of the two half-angles. */
export function fitPose(center: Vec3, radius: number, aspect = 1): CamPose {
  const hHalf = Math.atan(Math.tan(HALF_FOV) * aspect)
  const binding = Math.min(HALF_FOV, hHalf)
  return {
    target: center,
    dist: (Math.max(radius, 1e-6) / Math.sin(binding)) * FIT_MARGIN,
    yaw: 0.6,
    pitch: 0.35,
  }
}

export const orbited = (p: CamPose, dxPx: number, dyPx: number): CamPose => ({
  ...p,
  yaw: p.yaw - dxPx * ORBIT_RATE,
  pitch: Math.max(-PITCH_MAX, Math.min(PITCH_MAX, p.pitch + dyPx * ORBIT_RATE)),
})

export const zoomed = (p: CamPose, wheelDeltaY: number): CamPose => ({
  ...p,
  dist: Math.max(MIN_DIST, p.dist * Math.exp(wheelDeltaY * ZOOM_RATE)),
})

export function eyeOf(p: CamPose): Vec3 {
  const cp = Math.cos(p.pitch)
  return add3(p.target, scale3(v3(cp * Math.sin(p.yaw), Math.sin(p.pitch), cp * Math.cos(p.yaw)), p.dist))
}

export function panned(p: CamPose, dxPx: number, dyPx: number, viewportHPx: number): CamPose {
  const worldPerPx = (2 * p.dist * Math.tan(HALF_FOV)) / Math.max(1, viewportHPx)
  const fwd = norm3(sub3(p.target, eyeOf(p)))
  const right = norm3(cross3(fwd, v3(0, 1, 0))) // pitch clamp keeps fwd off the vertical
  const up = cross3(right, fwd)
  return { ...p, target: add3(p.target, add3(scale3(right, -dxPx * worldPerPx), scale3(up, dyPx * worldPerPx))) }
}

/** True when the current pose no longer frames the given bounds: the target
    drifted off-center, the sphere outgrew the view, or the scene shrank far
    below the working distance. */
export function escapesFraming(p: CamPose, center: Vec3, radius: number): boolean {
  const needed = Math.max(radius, 1e-6) / Math.sin(HALF_FOV)
  return dist3(p.target, center) > 0.5 * radius || needed > p.dist * 1.05 || needed < p.dist / 8
}
