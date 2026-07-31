import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { sigOrder } from '../kernel/diagram/sig'
import type { Vec2 } from './vec'
import type { NodeGeometry } from './bend'
import type { Body, Engine } from './engine'
import { ascaleOf, DISC_R, FRAME_CORNER_W, frameBounds, resolvedFrameSlot } from './engine'
import { existentialStubs, legPaths } from './wires'

/**
 * The display list (round-8 lab spec), pure — `paint(engine, theme)` returns
 * world-space shapes; `canvas.ts` renders them under the view transform. Two
 * first-class themes ship: Light/Manuscript (warm paper, inset wells, unified
 * dark linework) and Dark/Slate (glowing cyan linework, deepened wells,
 * relational wires glowing in their order-ladder hue like their atoms).
 *
 * Laws enforced by construction and checked in paint.test.ts: text appears
 * ONLY on named refs; boundary wires exit the frame while internal singletons
 * get an ∃ stub; semantic-node rails share one theme-owned stroke and width;
 * a relational wire's colour codes the order of its signature and an atom
 * strokes in its head wire's rung.
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
  readonly relationHueLightness: number
  readonly interaction: InteractionPalette
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
  /** A traced wire stroke: the Hobby-chain samples at paint
      resolution (plan 22 — the polyline IS the wire, not a spline fit). */
  | { readonly kind: 'polyline'; readonly pts: readonly Vec2[]; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'bezierPath'; readonly cubics: readonly { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }[]; readonly pts: readonly Vec2[]; readonly stroke: string; readonly width: number; readonly glow: string | null }
  | { readonly kind: 'stub'; readonly from: Vec2; readonly to: Vec2; readonly dot: Vec2; readonly dotRpx: number; readonly stroke: string; readonly width: number; readonly glow: string | null }
  /** A filled disc whose radius is fixed DEVICE pixels (junction dots): stays a
      constant size under zoom, unlike world-scaled circles. */
  | { readonly kind: 'dot'; readonly center: Vec2; readonly rPx: number; readonly fill: string }
  | { readonly kind: 'label'; readonly center: Vec2; readonly text: string; readonly color: string; readonly r: number; readonly font: string }

const FRAME_STROKE_W = 2
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

/**
 * The order ladder: every relational wire is coloured by the ORDER (depth) of
 * its signature — the canonical colours-as-sort code (law 6), replacing the old
 * colours-as-names per-bubble hue. Order 1 is violet; each further order
 * steps one golden angle. Individual wires are absent from the map and keep
 * the theme's base wire colour, so the caller reads
 * `hues.get(wid) ?? st.wire`. This is the single ladder authority — the app
 * (spawn option colours, proof-front hover) imports it from here.
 */
export function relationWireHues(d: Diagram, lightness: number): Map<WireId, string> {
  const out = new Map<WireId, string>()
  for (const [wid, w] of Object.entries(d.wires)) {
    if (w.sig.kind !== 'rel') continue
    const hue = (268 + (sigOrder(w.sig) - 1) * 137.5) % 360
    out.set(wid, `hsl(${hue.toFixed(0)}, 48%, ${lightness}%)`)
  }
  return out
}

/** The relational wire an atom's head port binds, per node — the wire whose
    order-ladder rung the atom body strokes in, and the group key for hover. */
function atomHeadWires(d: Diagram): Map<NodeId, WireId> {
  const out = new Map<NodeId, WireId>()
  for (const [wid, w] of Object.entries(d.wires)) {
    for (const ep of w.endpoints) if (ep.port.kind === 'head') out.set(ep.node, wid)
  }
  return out
}

/** The semantic-node rail outline in one stroke/width/glow. */
function anatomyOutline(e: Engine, b: Body, g: NodeGeometry, stroke: string, width: number, glow: string | null): Shape[] {
  const ascale = ascaleOf(b.kind) * e.scale
  const out: Shape[] = []
  for (const a of g.arcs) {
    out.push({ kind: 'arc', center: b.pos, r: a.r * ascale, a0: a.a0 + b.theta, a1: a.a1 + b.theta, stroke, width, glow })
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
  const hues = relationWireHues(e.d, st.relationHueLightness)
  // A relational wire strokes in its order-ladder rung; an individual wire
  // keeps the base colour. One colour is uniform along the whole wire.
  const wireStroke = (wid: WireId): string => hues.get(wid) ?? st.wire
  const shapes: Shape[] = []
  // ≥3-leg interior junctions draw as a soap-film Steiner tree with tangential
  // tributary merging (round-8 · D, the user-approved look): `legPaths` already
  // traces every tree edge (leg), branch vertices included, so there is nothing
  // extra to draw at a branch — no dot is painted there (USER 2026-07-07: branch
  // points are unmarked).
  // wires (Hobby-chain strokes) — the ACTUAL wire network, junctions included
  for (const { wid, pts, cubics } of legPaths(e)) {
    const stroke = wireStroke(wid)
    shapes.push({ kind: 'bezierPath', cubics, pts, stroke, width: st.wireW, glow: glow(stroke) })
  }
  // existential stubs (genuine internal loose ends — the ∃ dot is SEMANTIC, stays)
  for (const s of existentialStubs(e)) {
    const stroke = wireStroke(s.wid)
    shapes.push({ kind: 'stub', from: s.from, to: s.to, dot: s.dot, dotRpx: STUB_DOT_R, stroke, width: st.wireW, glow: glow(stroke) })
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
  // Wire-owned END-body dots: the outermost quantifier point of a line of identity —
  // an ∃ tip, a ∀ via (ruling A: now a leaf terminal, dotted like an ∃ tip pending the
  // Task 5 gallery ruling on the ∀ glyph), or a bare wire. Wire-owned Steiner branch
  // vertices are not bodies and are never dotted (USER 2026-07-07: branch points are
  // unmarked; where legs meet is downstream of the tree).
  for (const b of e.bodies.values()) {
    if (b.kind !== 'end') continue
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_OUTER_R, fill: st.paper })
    shapes.push({ kind: 'dot', center: b.pos, rPx: JUNCTION_INNER_R, fill: st.wire })
  }
  return shapes
}

export function paint(e: Engine, st: Theme, wires: (e: Engine, st: Theme) => Shape[] = paintWires): Shape[] {
  const fb = frameBounds(e)
  if (fb === null) throw new Error('paint requires a settled engine: call settleStep/settle first')
  const hues = relationWireHues(e.d, st.relationHueLightness)
  const headWireOf = atomHeadWires(e.d)
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const shapes: Shape[] = []

  // sheet frame
  shapes.push({ kind: 'frame', x: fb.minX, y: fb.minY, w: fb.maxX - fb.minX, h: fb.maxY - fb.minY, cornerW: FRAME_CORNER_W, fill: st.paper, stroke: st.frame, width: FRAME_STROKE_W })

  // regions, outer first: cuts get fill + inset well + ink rim. Regions are only
  // sheet/cut; relational quantifiers are wires, never regions.
  const rs = [...e.regions.entries()]
    .filter(([rid]) => e.d.regions[rid]!.kind !== 'sheet')
    .sort((a, b) => b[1].radius - a[1].radius)
  for (const [rid, g] of rs) {
    const fill = cutDepth(e.d, rid) % 2 === 1 ? st.negFill : st.paper
    shapes.push({ kind: 'circle', center: g.center, r: g.radius, fill, stroke: st.ink, width: st.rimW, insetColor: st.insetColor, glow: null })
  }

  for (const s of wires(e, st)) shapes.push(s) // no spread: big diagrams overflow the arg stack

  // Atom/ref argument positions are ordered by their relation signatures, so a
  // two-or-more-argument node gets a rim pip at a:0. Identity anchors are
  // unordered and deliberately never receive this marker.
  const pipArity = (b: Body): number => {
    const node = b.node
    if (node === null) return 0
    if (node.kind === 'ref' || node.kind === 'atom') return node.sig.args.length
    return 0
  }
  const pipAt = (b: Body, rimR: number, fill: string): Shape => {
    const c = Math.cos(b.theta + Math.PI / 2), s = Math.sin(b.theta + Math.PI / 2)
    return { kind: 'dot', center: { x: b.pos.x + c * rimR, y: b.pos.y + s * rimR }, rPx: PIP_R, fill }
  }

  // Semantic node bodies: shared-linework atoms/identities plus named refs.
  for (const b of e.bodies.values()) {
    if (b.kind === 'end' || b.kind === 'anchor') continue
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
    // An atom strokes in its head wire's order-ladder rung; identity stays
    // neutral shared linework.
    const atomHue = node.kind === 'atom' ? (hues.get(headWireOf.get(b.id) ?? '') ?? st.wire) : null
    const stroke = atomHue ?? st.wire
    shapes.push(...anatomyOutline(e, b, g, stroke, st.wireW, glow(stroke)))
    if (node.kind === 'atom' && pipArity(b) >= 2) {
      shapes.push(pipAt(b, g.arcs[0]!.r * ascale, stroke))
    }
  }

  return shapes
}

/** The alternate theme (two-theme toggle). */
export function nextTheme(t: Theme): Theme {
  return t === LIGHT ? DARK : LIGHT
}

/**
 * ONE wire's overlay stroke (hover, selection, drag feedback): the SAME Hobby
 * cubic chain the painter draws, restroked in the interaction colour/width.
 * Every overlay producer uses this — drawing the sampled `pts` as a polyline
 * instead renders a visible discretization of the wire (USER 2026-07-30).
 */
export function wireOverlayShapes(e: Engine, wid: WireId, stroke: string, width: number, glow: string | null = null): Shape[] {
  const out: Shape[] = []
  for (const l of legPaths(e)) {
    if (l.wid === wid) out.push({ kind: 'bezierPath', cubics: l.cubics, pts: l.pts, stroke, width, glow })
  }
  for (const s of existentialStubs(e)) {
    if (s.wid === wid) out.push({ kind: 'segment', from: s.from, to: s.to, stroke, width, glow })
  }
  return out
}

/**
 * Hover-group highlight: brighten a whole relation group — the shared head wire
 * (its traced legs) and every atom bound to it — in the wire's order-ladder hue,
 * brighter and wider, glowing in Dark. The group key is the WIRE itself (heads
 * share a wire, replacing the old bubble-region key). Returns overlay shapes
 * drawn over the base paint; empty when `wireId` is not a relational wire.
 */
export function highlightGroup(e: Engine, st: Theme, wireId: WireId): Shape[] {
  const hue = relationWireHues(e.d, Math.min(st.relationHueLightness + HL_BRIGHT, 88)).get(wireId)
  if (hue === undefined) return []
  const wireGlow = st.wireGlow ? hue : null
  const out: Shape[] = wireOverlayShapes(e, wireId, hue, st.wireW + HL_WIDTH, wireGlow)
  const w = e.d.wires[wireId]
  const atomIds = new Set(w === undefined ? [] : w.endpoints.filter((ep) => ep.port.kind === 'head').map((ep) => ep.node))
  for (const b of e.bodies.values()) {
    if (b.node?.kind !== 'atom' || !atomIds.has(b.id)) continue
    out.push(...anatomyOutline(e, b, b.geometry!, hue, st.wireW + HL_WIDTH, wireGlow))
  }
  return out
}

export const LIGHT: Theme = {
  name: 'Light (Manuscript)', canvas: '#e8e4d8', paper: '#faf7ee', ink: '#2a2118', frame: '#7a7263',
  wire: '#26343a', wireW: 2.2, negFill: 'rgba(90, 78, 58, 0.12)', rimW: 1.3,
  discFill: '#fffdf6', discText: '#2a2118', font: 'Georgia, serif',
  insetColor: 'rgba(58, 48, 32, 0.13)', wireGlow: false, relationHueLightness: 46,
  interaction: {
    selection: '#d97706', hover: '#2563eb', selectedHover: '#92400e', pin: '#dc2626',
    valid: '#16a34a', validWash: '#16a34a10', refusal: '#dc2626',
  },
}

export const DARK: Theme = {
  name: 'Dark (Slate)', canvas: '#0e1013', paper: '#1c2026', ink: '#e6e1d6', frame: '#4a5058',
  wire: '#5bd2de', wireW: 2.2, negFill: 'rgba(255, 255, 255, 0.06)', rimW: 1.2,
  discFill: '#262c33', discText: '#eae5da', font: 'Georgia, serif',
  insetColor: 'rgba(0, 0, 0, 0.32)', wireGlow: true, relationHueLightness: 64,
  interaction: {
    selection: '#f59e0b', hover: '#60a5fa', selectedHover: '#fbbf24', pin: '#fb7185',
    valid: '#4ade80', validWash: '#4ade8018', refusal: '#fb7185',
  },
}

export const THEMES: readonly Theme[] = [LIGHT, DARK]
