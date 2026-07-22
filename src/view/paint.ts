import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { NodeGeometry } from './bend'
import type { Body, Engine } from './engine'
import { ascaleOf, DISC_R, FRAME_CORNER_W, frameBounds, localToWorld, resolvedFrameSlot } from './engine'
import { existentialStubs, legPaths } from './wires'

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
  readonly mode: 'light' | 'dark'
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
  readonly interaction: InteractionPalette
  readonly controls: ControlPalette
}

export type ControlPalette = {
  readonly surface: string
  readonly foreground: string
  readonly border: string
  readonly hoverSurface: string
  readonly activeSurface: string
  readonly primarySurface: string
  readonly primaryForeground: string
  readonly primaryBorder: string
  readonly primaryHoverSurface: string
  readonly primaryActiveSurface: string
  readonly disabledSurface: string
  readonly disabledForeground: string
  readonly disabledBorder: string
  readonly focusRing: string
  readonly menuSurface: string
  readonly menuHoverSurface: string
  readonly mutedForeground: string
}

export type InteractionPalette = {
  readonly selection: string
  readonly hover: string
  readonly selectedHover: string
  readonly pin: string
  readonly valid: string
  readonly validWash: string
  readonly refusal: string
}

export type Shape =
  | { readonly kind: 'frame'; readonly x: number; readonly y: number; readonly w: number; readonly h: number; readonly cornerW: number; readonly fill: string; readonly stroke: string; readonly width: number }
  | { readonly kind: 'circle'; readonly center: Vec2; readonly r: number; readonly fill: string | null; readonly stroke: string | null; readonly width: number; readonly insetColor: string | null; readonly glow: string | null }
  | { readonly kind: 'arc'; readonly center: Vec2; readonly r: number; readonly a0: number; readonly a1: number; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'segment'; readonly from: Vec2; readonly to: Vec2; readonly stroke: string; readonly width: number; readonly glow: string | null }
  /** A traced wire leg: the massless-elastica θ-quadratic sampled at paint
      resolution (plan 22 — the polyline IS the wire, not a spline fit). */
  | { readonly kind: 'polyline'; readonly pts: readonly Vec2[]; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'stub'; readonly from: Vec2; readonly to: Vec2; readonly dot: Vec2; readonly dotRpx: number; readonly stroke: string; readonly width: number; readonly glow: string | null }
  /** A filled disc whose radius is fixed DEVICE pixels (junction dots): stays a
      constant size under zoom, unlike world-scaled circles. */
  | { readonly kind: 'dot'; readonly center: Vec2; readonly rPx: number; readonly fill: string }
  | { readonly kind: 'label'; readonly center: Vec2; readonly text: string; readonly color: string; readonly r: number; readonly font: string }

const FRAME_STROKE_W = 2
const BUBBLE_RING_W = 2.0
const DISC_RIM_W = 1.4
const JUNCTION_OUTER_R = 3.6
const JUNCTION_INNER_R = 2.6
const STUB_DOT_R = 2.6
/** Device-pixel radius of the port-order pip (junction-dot family). */
const PIP_R = 3.2
/** The sheet's port-0 origin must dominate ordinary existential-sized ports. */
const FRAME_ORIGIN_R = 5.2
/** Hover-group highlight: lightness bump and extra stroke width over the base. */
const HL_BRIGHT = 18
const HL_WIDTH = 0.8

/** Full user-facing name of a reference. Namespace qualification identifies the
    definition semantically; the disc displays its complete final path segment. */
export function referenceDisplayLabel(defId: string): string {
  const slash = defId.lastIndexOf('/')
  return slash < 0 ? defId : defId.slice(slash + 1)
}

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

/** The disc/port outline of a body (arcs + radials) in one stroke/width/glow.
    Shared by the base paint and the hover-group highlight; the term-only
    output run is added by the caller. */
function anatomyOutline(e: Engine, b: Body, g: NodeGeometry, stroke: string, width: number, glow: string | null): Shape[] {
  const ascale = ascaleOf(b.kind) * e.scale
  const out: Shape[] = []
  for (const a of g.arcs) {
    out.push({ kind: 'arc', center: b.pos, r: a.r * ascale, a0: a.a0 + b.theta, a1: a.a1 + b.theta, stroke, width, glow })
  }
  for (const r of g.radials) {
    out.push({
      kind: 'segment',
      from: localToWorld(e, b, { x: Math.cos(r.angle) * r.r0, y: Math.sin(r.angle) * r.r0 }),
      to: localToWorld(e, b, { x: Math.cos(r.angle) * r.r1, y: Math.sin(r.angle) * r.r1 }),
      stroke, width, glow,
    })
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

/** The wire pass of the base painter: legs, existential stubs, boundary
    exits, the frame pip, and junction dots. Exported (and overridable via
    paint's `wires` parameter) so wire-rendering experiments can substitute
    their own pass without duplicating the rest of the painter. */
export function paintWires(e: Engine, st: Theme): Shape[] {
  const fb = frameBounds(e)
  if (fb === null) throw new Error('paintWires requires a settled engine: call settleStep/settle first')
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const shapes: Shape[] = []
  // ≥3-leg interior junctions are drawn as a soap-film Steiner tree with tangential
  // tributary merging (round-8 · D, the user-approved look), NOT as a star of legs
  // meeting at one hub point — so those wires' star legs are skipped here and the
  // hub-point branch dot is NOT drawn (USER 2026-07-07: branch points are unmarked).
  // wires (traced elastica legs) — the ACTUAL physics wire, junctions included
  for (const { wid, pts } of legPaths(e)) {
    void wid
    shapes.push({ kind: 'polyline', pts, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  // existential stubs (genuine internal loose ends — the ∃ dot is SEMANTIC, stays)
  for (const s of existentialStubs(e)) {
    shapes.push({ kind: 'stub', from: s.from, to: s.to, dot: s.dot, dotRpx: STUB_DOT_R, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  // An unattached boundary wire is already a formal port: paint it exactly at
  // its canonical frame slot rather than inventing a floating existential body.
  // The origin slot gets only the larger origin marker below, never a stacked
  // second dot.
  for (const [position, wid] of e.boundary.entries()) {
    const w = e.wires.get(wid)
    if (w === undefined || w.binds.length !== 0) continue
    const slot = resolvedFrameSlot(e, position)
    if (slot === null) continue
    if (position !== 0) shapes.push({ kind: 'dot', center: slot.point, rPx: STUB_DOT_R, fill: st.wire })
  }
  // Port 0 is always the single prominent reading origin whenever the sheet has
  // a boundary. All remaining ports are read clockwise from this logical port,
  // including after a proof-wide cyclic slot shift.
  if (e.boundary.length > 0 && e.wires.has(e.boundary[0]!)) {
    const origin = resolvedFrameSlot(e, 0)
    if (origin !== null) shapes.push({ kind: 'dot', center: origin.point, rPx: FRAME_ORIGIN_R, fill: st.ink })
  }
  // SEMANTIC junction-body dots only: a genuine degree-1 loose end of a line of
  // identity — an ∃ tip or a bare wire (the existential dot is semantic, USER LAW).
  // A ∀ via-body (a body that IS a branch hub) carries branching arms, so it is not
  // dotted — the branch legs are the only visual. Wire-owned Steiner branch points
  // are not bodies and are never dotted.
  const hubBodies = new Set<string>()
  for (const w of e.wires.values()) if (w.hub !== null && w.hub.kind === 'body') hubBodies.add(w.hub.bodyId)
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction' || hubBodies.has(b.id)) continue
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_OUTER_R, fill: st.paper })
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_INNER_R, fill: st.wire })
  }
  return shapes
}

export function paint(e: Engine, st: Theme, wires: (e: Engine, st: Theme) => Shape[] = paintWires): Shape[] {
  const fb = frameBounds(e)
  if (fb === null) throw new Error('paint requires a settled engine: call settleStep/settle first')
  const hues = bubbleHues(e.d, st.bubbleLightness)
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const shapes: Shape[] = []

  // sheet frame
  shapes.push({ kind: 'frame', x: fb.minX, y: fb.minY, w: fb.maxX - fb.minX, h: fb.maxY - fb.minY, cornerW: FRAME_CORNER_W, fill: st.paper, stroke: st.frame, width: FRAME_STROKE_W })

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

  for (const s of wires(e, st)) shapes.push(s) // no spread: big diagrams overflow the arg stack

  // The port-order pip: nodes with two or more ORDERED ports (refs by arity,
  // atoms by their binder's arity) get a filled dot on their rim at port a0's
  // angle; ports read clockwise from it (canvas y-down). Device-pixel sized
  // like junction dots so it survives every zoom, drawn in the node's own
  // stroke, rotating with the body. Without it a featureless rotating disc
  // gives no way to tell which leg is which.
  const pipArity = (b: Body): number => {
    const node = b.node
    if (node === null) return 0
    if (node.kind === 'ref') return node.arity
    if (node.kind === 'atom') {
      const binder = e.d.regions[node.binder]!
      return binder.kind === 'bubble' ? binder.arity : 0
    }
    return 0
  }
  const pipAt = (b: Body, rimR: number, fill: string): Shape => {
    const c = Math.cos(b.theta + Math.PI / 2), s = Math.sin(b.theta + Math.PI / 2)
    return { kind: 'dot', center: { x: b.pos.x + c * rimR, y: b.pos.y + s * rimR }, rPx: PIP_R, fill }
  }

  // node bodies: anatomy (shared linework / binder-hue atoms) + named discs
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' || b.kind === 'anchor') continue
    const node = b.node!
    if (node.kind === 'ref') {
      const discR = DISC_R * e.scale
      shapes.push({ kind: 'circle', center: b.pos, r: discR, fill: st.discFill, stroke: st.ink, width: DISC_RIM_W, insetColor: null, glow: null })
      shapes.push({ kind: 'label', center: b.pos, text: referenceDisplayLabel(node.defId), color: st.discText, r: discR, font: st.font })
      if (pipArity(b) >= 2) shapes.push(pipAt(b, discR, st.ink))
      continue
    }
    const g = b.geometry!
    const ascale = ascaleOf(b.kind) * e.scale
    const atomHue = node.kind === 'atom' ? hues.get(node.binder)! : null
    const stroke = atomHue ?? st.wire
    shapes.push(...anatomyOutline(e, b, g, stroke, st.wireW, glow(atomHue ?? st.wire)))
    if (node.kind === 'atom' && pipArity(b) >= 2) {
      shapes.push(pipAt(b, g.arcs[0]!.r * ascale, stroke))
    }
    if (node.kind === 'term') {
      // the term output run stays monochrome linework (term-internal anatomy
      // never carries a binder hue — law 8)
      if (g.exitArc !== null) {
        shapes.push({ kind: 'arc', center: b.pos, r: g.exitArc.r * ascale, a0: g.exitArc.a0 + b.theta, a1: g.exitArc.a1 + b.theta, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
      }
      if (g.exitLine !== null) {
        shapes.push({ kind: 'segment', from: localToWorld(e, b, g.exitLine[0]), to: localToWorld(e, b, g.exitLine[1]), stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
      }
    }
  }

  return shapes
}

/** The alternate theme (two-theme toggle). */
export function nextTheme(t: Theme): Theme {
  return t === LIGHT ? DARK : LIGHT
}

/**
 * Hover-group highlight: brighten a whole binder group (its bubble ring and
 * every atom bound to it) in the shared hue — same hue family, brighter and
 * wider, glowing in Dark. Returns overlay shapes drawn over the base paint;
 * empty when `binderRid` is not a bubble.
 */
export function highlightGroup(e: Engine, st: Theme, binderRid: RegionId): Shape[] {
  const hue = bubbleHues(e.d, Math.min(st.bubbleLightness + HL_BRIGHT, 88)).get(binderRid)
  if (hue === undefined) return []
  const out: Shape[] = []
  const g = e.regions.get(binderRid)
  if (g !== undefined) {
    out.push({ kind: 'circle', center: g.center, r: g.radius, fill: null, stroke: hue, width: BUBBLE_RING_W + HL_WIDTH, insetColor: null, glow: st.wireGlow ? hue : null })
  }
  for (const b of e.bodies.values()) {
    if (b.node?.kind !== 'atom' || b.node.binder !== binderRid) continue
    out.push(...anatomyOutline(e, b, b.geometry!, hue, st.wireW + HL_WIDTH, st.wireGlow ? hue : null))
  }
  return out
}

export const LIGHT: Theme = {
  mode: 'light',
  name: 'Light (Manuscript)', canvas: '#e8e4d8', paper: '#faf7ee', ink: '#2a2118', frame: '#7a7263',
  wire: '#26343a', wireW: 2.2, negFill: 'rgba(90, 78, 58, 0.12)', rimW: 1.3,
  discFill: '#fffdf6', discText: '#2a2118', font: 'Georgia, serif',
  insetColor: 'rgba(58, 48, 32, 0.13)', wireGlow: false, bubbleLightness: 46,
  interaction: {
    selection: '#d97706', hover: '#2563eb', selectedHover: '#92400e', pin: '#dc2626',
    valid: '#16a34a', validWash: '#16a34a10', refusal: '#dc2626',
  },
  controls: {
    surface: '#fffdf6', foreground: '#2a2118', border: '#8a806f',
    hoverSurface: '#f1eadc', activeSurface: '#e4d8c5',
    primarySurface: '#8a3f0a', primaryForeground: '#fffaf0', primaryBorder: '#743306',
    primaryHoverSurface: '#743306', primaryActiveSurface: '#5f2905',
    disabledSurface: '#e8e0d2', disabledForeground: '#655e54', disabledBorder: '#857b6a',
    focusRing: '#a94f00', menuSurface: '#fffdf6', menuHoverSurface: '#f4e6cb',
    mutedForeground: '#665d51',
  },
}

export const DARK: Theme = {
  mode: 'dark',
  name: 'Dark (Slate)', canvas: '#0e1013', paper: '#1c2026', ink: '#e6e1d6', frame: '#4a5058',
  wire: '#5bd2de', wireW: 2.2, negFill: 'rgba(255, 255, 255, 0.06)', rimW: 1.2,
  discFill: '#262c33', discText: '#eae5da', font: 'Georgia, serif',
  insetColor: 'rgba(0, 0, 0, 0.32)', wireGlow: true, bubbleLightness: 64,
  interaction: {
    selection: '#f59e0b', hover: '#60a5fa', selectedHover: '#fbbf24', pin: '#fb7185',
    valid: '#4ade80', validWash: '#4ade8018', refusal: '#fb7185',
  },
  controls: {
    surface: '#282d33', foreground: '#f1eadf', border: '#737b85',
    hoverSurface: '#353c45', activeSurface: '#414a55',
    primarySurface: '#f0a43a', primaryForeground: '#1a1611', primaryBorder: '#ffc15c',
    primaryHoverSurface: '#ffc15c', primaryActiveSurface: '#d98a20',
    disabledSurface: '#25292e', disabledForeground: '#a9a39a', disabledBorder: '#737b85',
    focusRing: '#f3aa3d', menuSurface: '#1f242a', menuHoverSurface: '#343b43',
    mutedForeground: '#b8b0a5',
  },
}

export const THEMES: readonly Theme[] = [LIGHT, DARK]
