import type { Vec2 } from './vec'

/**
 * The viewport is a pure FIT (no pan): centered on the sheet circle at a scale
 * that keeps the whole sheet on screen, capped at the design's unit scale so
 * small sheets don't blow up, times the user's wheel-zoom factor. Extracted
 * from the shell as a pure function so the degenerate-input guard is testable.
 */

/** The design's unit (maximum) world→device scale. */
export const DESIGN_SCALE = 6
/** Fraction of the smaller canvas dimension the sheet diameter is fit into. */
const FIT_FRACTION = 0.45

export type Camera = { readonly scale: number; readonly offsetX: number; readonly offsetY: number }

/**
 * Fit the camera on the sheet circle. The returned scale is ALWAYS a positive
 * finite number: `toWorld` divides by it, so a 0/negative/NaN scale would
 * poison the pointer→world mapping for the whole frame. A degenerate viewport
 * (zero/NaN canvas extent) or a non-finite sheet radius is the only way the raw
 * fit is not positive-finite; in that case the scale falls back to the design
 * unit scale (draw at 1:1). Reachable frames — positive canvas, radius floored
 * at 10, positive userZoom — never take the fallback, so it changes no real
 * drawing.
 */
export function fitCamera(
  sheet: { readonly center: Vec2; readonly radius: number } | undefined,
  canvasW: number,
  canvasH: number,
  userZoom: number,
): Camera {
  const R = Math.max(sheet === undefined ? 10 : sheet.radius, 10)
  const cx = sheet === undefined ? 0 : sheet.center.x
  const cy = sheet === undefined ? 0 : sheet.center.y
  const raw = Math.min(DESIGN_SCALE, (FIT_FRACTION * Math.min(canvasW, canvasH)) / R) * userZoom
  const scale = Number.isFinite(raw) && raw > 0 ? raw : DESIGN_SCALE
  return { scale, offsetX: canvasW / 2 - cx * scale, offsetY: canvasH / 2 - cy * scale }
}
