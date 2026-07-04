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

/** The bodies a step touched: fresh nodes plus the wire bodies of fresh
    wires (engine convention j:/x:). Empty on pure removals — callers fall
    back to the whole diagram. */
export function changedBodies(before: Diagram, after: Diagram): string[] {
  const out: string[] = []
  for (const id of Object.keys(after.nodes)) if (before.nodes[id] === undefined) out.push(id)
  for (const id of Object.keys(after.wires)) {
    if (before.wires[id] === undefined) { out.push(`j:${id}`, `x:${id}`) }
  }
  return out
}

const zoomCache = new WeakMap<Diagram, Map<Diagram, HTMLCanvasElement>>()

/** A thumbnail of `after` ZOOMED to what the step changed (A's readability
    verdict: whole-diagram miniatures blur together; the change doesn't). */
export function zoomThumb(before: Diagram, after: Diagram, boundary: readonly WireId[], w = 220, h = 154): HTMLCanvasElement {
  let byAfter = zoomCache.get(before)
  if (byAfter?.has(after)) return byAfter.get(after)!
  const c = document.createElement('canvas')
  c.width = w * 2; c.height = h * 2
  c.style.width = `${w}px`; c.style.height = `${h}px`
  renderPreview(c, after, boundary.filter((x) => after.wires[x] !== undefined), changedBodies(before, after))
  if (byAfter === undefined) { byAfter = new Map(); zoomCache.set(before, byAfter) }
  byAfter.set(after, c)
  return c
}
