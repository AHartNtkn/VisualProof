/**
 * Round-6h shared bits: cached state thumbnails (a visual proof assistant's
 * history should be VISUAL) — one small render per state, cached by the
 * immutable diagram object.
 */
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { renderPreview } from './prove'

const cache = new WeakMap<Diagram, HTMLCanvasElement>()

export function stateThumb(d: Diagram, boundary: readonly WireId[], w = 132, h = 92): HTMLCanvasElement {
  const hit = cache.get(d)
  if (hit !== undefined) return hit
  const c = document.createElement('canvas')
  c.width = w * 2; c.height = h * 2 // crisp on hidpi
  c.style.width = `${w}px`; c.style.height = `${h}px`
  renderPreview(c, d, boundary.filter((x) => d.wires[x] !== undefined))
  cache.set(d, c)
  return c
}
