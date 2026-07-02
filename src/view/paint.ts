import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine } from './engine'
import { ascaleOf, DISC_R, frameBounds } from './engine'
import { boundaryExits, existentialStubs, legPaths } from './wires'

/**
 * The display list (round-8 lab spec), pure — `paint(engine, theme)` returns
 * world-space shapes; `canvas.ts` renders them under the view transform. Two
 * first-class themes ship: Light/Manuscript (warm paper, inset wells, unified
 * dark linework) and Dark/Slate (glowing cyan linework, deepened wells, SO-
 * quantifier bubble rings glowing in their binder hue like their atoms).
 *
 * Laws enforced by construction and checked in paint.test.ts: text appears
 * ONLY on named discs (law 2); boundary wires exit the frame while internal
 * singletons get an ∃ stub (law 3); wires and λ-anatomy share one stroke and
 * width from the theme (law 5); atom strokes and bubble rings both derive from
 * the per-bubble hue, and Dark glows both (law 6).
 */

export type Theme = {
  readonly name: string
  /** Page background behind the sheet (owned by the shell/canvas element). */
  readonly canvas: string
  readonly paper: string
  readonly ink: string
  readonly frame: string
  readonly wire: string
  readonly wireW: number
  readonly negFill: string
  readonly rimW: number
  readonly discFill: string
  readonly discText: string
  readonly font: string
  readonly insetColor: string
  readonly wireGlow: boolean
  readonly bubbleLightness: number
}

export type Shape =
  | { readonly kind: 'frame'; readonly x: number; readonly y: number; readonly w: number; readonly h: number; readonly cornerPx: number; readonly fill: string; readonly stroke: string; readonly width: number }
  | { readonly kind: 'circle'; readonly center: Vec2; readonly r: number; readonly fill: string | null; readonly stroke: string | null; readonly width: number; readonly insetColor: string | null; readonly glow: string | null }
  | { readonly kind: 'arc'; readonly center: Vec2; readonly r: number; readonly a0: number; readonly a1: number; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'segment'; readonly from: Vec2; readonly to: Vec2; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'bezier'; readonly from: Vec2; readonly c1: Vec2; readonly c2: Vec2; readonly to: Vec2; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'exit'; readonly from: Vec2; readonly c1: Vec2; readonly c2: Vec2; readonly to: Vec2; readonly tick: { readonly center: Vec2; readonly vertical: boolean }; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'stub'; readonly from: Vec2; readonly to: Vec2; readonly dot: Vec2; readonly dotRpx: number; readonly stroke: string; readonly width: number; readonly glow: string | null }
  /** A filled disc whose radius is fixed DEVICE pixels (junction dots): stays a
      constant size under zoom, unlike world-scaled circles. */
  | { readonly kind: 'dot'; readonly center: Vec2; readonly rPx: number; readonly fill: string }
  | { readonly kind: 'label'; readonly center: Vec2; readonly text: string; readonly color: string; readonly r: number; readonly font: string }

const FRAME_STROKE_W = 2
const FRAME_CORNER_PX = 16
const BUBBLE_RING_W = 2.0
const DISC_RIM_W = 1.4
const JUNCTION_OUTER_R = 3.6
const JUNCTION_INNER_R = 2.6
const STUB_DOT_R = 2.6
/** Satellite discs are slightly smaller than relation-ref discs. */
const SAT_DISC_SCALE = 0.82
/** Satellite stems read as thinner tethers than core λ-anatomy. */
const SAT_STEM_W = 0.85
/** Disc labels truncate to this many glyphs. */
const LABEL_MAX = 5

/** Per-bubble hue (golden-angle spread from binder violet); the ONLY node
    colour code (law 6/8). Same map feeds atom strokes and the bubble ring. */
export function bubbleHues(d: Diagram, lightness: number): Map<RegionId, string> {
  const out = new Map<RegionId, string>()
  let k = 0
  for (const [rid, r] of Object.entries(d.regions)) {
    if (r.kind === 'bubble') {
      const hue = (268 + k * 137.5) % 360
      out.set(rid, `hsl(${hue.toFixed(0)}, 48%, ${lightness}%)`)
      k++
    }
  }
  return out
}

/** Cut-nesting depth of a region (drives shade parity: odd depth shades). */
function cutDepth(d: Diagram, rid: RegionId): number {
  let cur = rid, k = 0
  for (;;) {
    const r = d.regions[cur]!
    if (r.kind === 'sheet') return k
    if (r.kind === 'cut') k++
    cur = r.parent
  }
}

export function paint(e: Engine, st: Theme): Shape[] {
  const fb = frameBounds(e)
  if (fb === null) throw new Error('paint requires a settled engine: call settleStep/settle first')
  const hues = bubbleHues(e.d, st.bubbleLightness)
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const shapes: Shape[] = []

  // sheet frame
  shapes.push({ kind: 'frame', x: fb.minX, y: fb.minY, w: fb.maxX - fb.minX, h: fb.maxY - fb.minY, cornerPx: FRAME_CORNER_PX, fill: st.paper, stroke: st.frame, width: FRAME_STROKE_W })

  // regions, outer first: cuts fill + inset well + ink rim; bubbles are hue rings
  const rs = [...e.regions.entries()]
    .filter(([rid]) => e.d.regions[rid]!.kind !== 'sheet')
    .sort((a, b) => b[1].radius - a[1].radius)
  for (const [rid, g] of rs) {
    const kind = e.d.regions[rid]!.kind
    if (kind === 'bubble') {
      const hue = hues.get(rid)!
      shapes.push({ kind: 'circle', center: g.center, r: g.radius, fill: null, stroke: hue, width: BUBBLE_RING_W, insetColor: null, glow: glow(hue) })
      continue
    }
    const fill = cutDepth(e.d, rid) % 2 === 1 ? st.negFill : st.paper
    shapes.push({ kind: 'circle', center: g.center, r: g.radius, fill, stroke: st.ink, width: st.rimW, insetColor: st.insetColor, glow: null })
  }

  // wires
  for (const { path } of legPaths(e)) {
    shapes.push({ kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  // existential stubs (genuine internal loose ends)
  for (const s of existentialStubs(e)) {
    shapes.push({ kind: 'stub', from: s.from, to: s.to, dot: s.dot, dotRpx: STUB_DOT_R, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  // boundary frame exits
  for (const ex of boundaryExits(e)) {
    shapes.push({ kind: 'exit', from: ex.path.from, c1: ex.path.c1, c2: ex.path.c2, to: ex.path.to, tick: ex.tick, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  // junction dots (ring: paper halo + wire core), fixed device size
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_OUTER_R, fill: st.paper })
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_INNER_R, fill: st.wire })
  }

  // node bodies: anatomy (shared linework / binder-hue atoms) + named discs
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction') continue
    const node = b.node!
    if (node.kind === 'ref') {
      shapes.push({ kind: 'circle', center: b.pos, r: DISC_R, fill: st.discFill, stroke: st.ink, width: DISC_RIM_W, insetColor: null, glow: null })
      shapes.push({ kind: 'label', center: b.pos, text: node.defId.slice(0, LABEL_MAX), color: st.discText, r: DISC_R, font: st.font })
      continue
    }
    const g = b.geometry!
    const ascale = ascaleOf(b.kind)
    const cos = Math.cos(b.theta), sin = Math.sin(b.theta)
    const worldLocal = (lp: Vec2): Vec2 => {
      const x = lp.x * ascale, y = lp.y * ascale
      return { x: b.pos.x + x * cos - y * sin, y: b.pos.y + x * sin + y * cos }
    }
    const atomHue = node.kind === 'atom' ? hues.get(node.binder)! : null
    const stroke = atomHue ?? st.wire
    const anatomyGlow = glow(atomHue ?? st.wire)
    for (const a of g.arcs) {
      shapes.push({ kind: 'arc', center: b.pos, r: a.r * ascale, a0: a.a0 + b.theta, a1: a.a1 + b.theta, stroke, width: st.wireW, glow: anatomyGlow })
    }
    for (const r of g.radials) {
      shapes.push({ kind: 'segment', from: worldLocal({ x: Math.cos(r.angle) * r.r0, y: Math.sin(r.angle) * r.r0 }), to: worldLocal({ x: Math.cos(r.angle) * r.r1, y: Math.sin(r.angle) * r.r1 }), stroke, width: st.wireW, glow: anatomyGlow })
    }
    if (node.kind === 'term') {
      // the term output run stays monochrome linework (term-internal anatomy
      // never carries a binder hue — law 8)
      if (g.exitArc !== null) {
        shapes.push({ kind: 'arc', center: b.pos, r: g.exitArc.r * ascale, a0: g.exitArc.a0 + b.theta, a1: g.exitArc.a1 + b.theta, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
      }
      if (g.exitLine !== null) {
        shapes.push({ kind: 'segment', from: worldLocal(g.exitLine[0]), to: worldLocal(g.exitLine[1]), stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
      }
    }
    for (const s of b.satellites) {
      shapes.push({ kind: 'segment', from: worldLocal(s.localPos), to: worldLocal(s.discLocal), stroke: st.wire, width: st.wireW * SAT_STEM_W, glow: glow(st.wire) })
    }
    for (const s of b.satellites) {
      const c = worldLocal(s.discLocal)
      shapes.push({ kind: 'circle', center: c, r: DISC_R * SAT_DISC_SCALE, fill: st.discFill, stroke: st.ink, width: DISC_RIM_W, insetColor: null, glow: null })
      shapes.push({ kind: 'label', center: c, text: s.label.slice(0, LABEL_MAX), color: st.discText, r: DISC_R * SAT_DISC_SCALE, font: st.font })
    }
  }

  return shapes
}

export const LIGHT: Theme = {
  name: 'Light (Manuscript)', canvas: '#e8e4d8', paper: '#faf7ee', ink: '#2a2118', frame: '#7a7263',
  wire: '#26343a', wireW: 2.2, negFill: 'rgba(90, 78, 58, 0.12)', rimW: 1.3,
  discFill: '#fffdf6', discText: '#2a2118', font: 'Georgia, serif',
  insetColor: 'rgba(58, 48, 32, 0.13)', wireGlow: false, bubbleLightness: 46,
}

export const DARK: Theme = {
  name: 'Dark (Slate)', canvas: '#0e1013', paper: '#1c2026', ink: '#e6e1d6', frame: '#4a5058',
  wire: '#5bd2de', wireW: 2.2, negFill: 'rgba(255, 255, 255, 0.06)', rimW: 1.2,
  discFill: '#262c33', discText: '#eae5da', font: 'Georgia, serif',
  insetColor: 'rgba(0, 0, 0, 0.32)', wireGlow: true, bubbleLightness: 64,
}

export const THEMES: readonly Theme[] = [LIGHT, DARK]
