import type { Vec2 } from './vec'

/** Fraction of the smaller viewport dimension occupied by the fitted frame diameter. */
const FIT_DIAMETER_FRACTION = 0.9
export const MIN_USER_ZOOM = 1
export const MAX_USER_ZOOM = 8
const DEFAULT_FRAME_RADIUS = 10
const FALLBACK_SCALE = 1

export type Camera = { readonly scale: number; readonly offsetX: number; readonly offsetY: number }

/** The single zoom-state policy used by camera rendering and every input surface. */
export function normalizeUserZoom(value: number): number {
  return Number.isFinite(value)
    ? Math.max(MIN_USER_ZOOM, Math.min(MAX_USER_ZOOM, value))
    : MIN_USER_ZOOM
}

/**
 * Center a stored diagram frame in the viewport.
 *
 * User zoom 1 is canonical: every valid frame occupies the same 90% square in
 * screen space, regardless of its stored world-space radius. User zoom is
 * bounded here so every caller shares the same full-fit and maximum-zoom
 * semantics.
 *
 * Invalid frame or viewport geometry cannot produce a zero, negative, or
 * non-finite scale because pointer-to-world conversion divides by this value.
 */
export function fitCamera(
  sheet: { readonly center: Vec2; readonly radius: number } | undefined,
  canvasW: number,
  canvasH: number,
  userZoom: number,
): Camera {
  const width = Number.isFinite(canvasW) ? Math.max(0, canvasW) : 0
  const height = Number.isFinite(canvasH) ? Math.max(0, canvasH) : 0
  const radius = sheet !== undefined && Number.isFinite(sheet.radius) && sheet.radius > 0
    ? sheet.radius
    : DEFAULT_FRAME_RADIUS
  const cx = sheet !== undefined && Number.isFinite(sheet.center.x) ? sheet.center.x : 0
  const cy = sheet !== undefined && Number.isFinite(sheet.center.y) ? sheet.center.y : 0
  const zoom = normalizeUserZoom(userZoom)
  const rawScale = (FIT_DIAMETER_FRACTION * Math.min(width, height) * zoom) / (2 * radius)
  const scale = Number.isFinite(rawScale) && rawScale > 0 ? rawScale : FALLBACK_SCALE

  return { scale, offsetX: width / 2 - cx * scale, offsetY: height / 2 - cy * scale }
}
