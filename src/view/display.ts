import type { Vec2 } from './vec'
import { add, polar } from './vec'
import type { Scene } from './scene'

export type Shape =
  | { readonly kind: 'circle'; readonly center: Vec2; readonly r: number; readonly stroke: string; readonly fill?: string }
  | { readonly kind: 'arc'; readonly center: Vec2; readonly r: number; readonly a0: number; readonly a1: number; readonly stroke: string; readonly width: number }
  | { readonly kind: 'segment'; readonly from: Vec2; readonly to: Vec2; readonly stroke: string; readonly width: number }
  | { readonly kind: 'polyline'; readonly points: readonly Vec2[]; readonly stroke: string; readonly width: number }
  | { readonly kind: 'label'; readonly pos: Vec2; readonly text: string; readonly color: string }

/** Golden-angle hue per binder row: distinct, stable, no configuration. */
export function binderHue(row: number): string {
  const hue = ((row * 137.508) % 360 + 360) % 360
  return `hsl(${hue.toFixed(1)}, 70%, 45%)`
}

const REGION_STROKE = '#444'
const NEGATIVE_FILL = 'rgba(60, 60, 80, 0.25)'
const BACKGROUND_FILL = '#fafaf7'
const BUBBLE_STROKE = '#7a4dbf'
const WIRE_STROKE = '#1f6f8b'
const STRUCTURE = '#222'

/**
 * Pure display list, paint-ordered: regions (outer first), wires, then node
 * structure with binder hues at rest (tethers-on-hover is interaction,
 * Plan 10). Shading paints polarity: NEGATIVE cuts get the shade fill and
 * POSITIVE cuts get the opaque background fill — painting outer-first, an
 * even-depth cut visibly UN-shades the odd-depth shading it sits on. Bubbles
 * never fill (they do not flip parity, so their interior must show their
 * parent's shading through).
 */
export function renderScene(scene: Scene): Shape[] {
  const shapes: Shape[] = []
  const regions = [...scene.regions].sort((a, b) => b.radius - a.radius)
  for (const r of regions) {
    if (r.kind === 'sheet') continue
    if (r.kind === 'bubble') {
      shapes.push({ kind: 'circle', center: r.center, r: r.radius, stroke: BUBBLE_STROKE })
    } else {
      shapes.push({
        kind: 'circle',
        center: r.center,
        r: r.radius,
        stroke: REGION_STROKE,
        fill: r.shaded ? NEGATIVE_FILL : BACKGROUND_FILL,
      })
    }
  }
  for (const w of scene.wires) {
    if (w.spokes.length === 0) {
      shapes.push({ kind: 'polyline', points: [w.hub, add(w.hub, polar(0, 2))], stroke: WIRE_STROKE, width: 1.5 })
      continue
    }
    for (const s of w.spokes) {
      shapes.push({ kind: 'polyline', points: [w.hub, s], stroke: WIRE_STROKE, width: 1.5 })
    }
  }
  for (const n of scene.nodes) {
    const g = n.geometry
    for (const a of g.arcs) {
      shapes.push({
        kind: 'arc', center: n.center, r: a.r, a0: a.a0, a1: a.a1,
        stroke: a.kind === 'lam' ? binderHue(a.hueRow) : STRUCTURE, width: a.kind === 'lam' ? 2 : 1.2,
      })
    }
    for (const r of g.radials) {
      shapes.push({
        kind: 'segment',
        from: add(n.center, polar(r.angle, r.r0)),
        to: add(n.center, polar(r.angle, r.r1)),
        stroke: r.hueRow === null ? STRUCTURE : binderHue(r.hueRow),
        width: 1.2,
      })
    }
    if (g.exitArc !== null) {
      shapes.push({ kind: 'arc', center: n.center, r: g.exitArc.r, a0: g.exitArc.a0, a1: g.exitArc.a1, stroke: STRUCTURE, width: 1.2 })
    }
    shapes.push({ kind: 'segment', from: add(n.center, g.exitLine[0]), to: add(n.center, g.exitLine[1]), stroke: STRUCTURE, width: 1.2 })
    for (const gl of g.glyphs) {
      shapes.push({ kind: 'label', pos: add(n.center, gl.pos), text: gl.constId, color: STRUCTURE })
    }
  }
  return shapes
}
