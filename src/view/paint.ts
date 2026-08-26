import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { sigOrder } from '../kernel/diagram/sig'
import type { Vec2 } from './vec'
import type { NodeGeometry } from './bend'
import { ARGUMENT_COLOR, type LambdaStrokeFrame } from './lambda-motion'
import type { Body, Engine } from './engine'
import { ascaleOf, DISC_R, FRAME_CORNER_W, frameBounds, localToWorld, resolvedFrameSlot } from './engine'
import { computeLegs, legPaths } from './wires'
import type { Leg } from './engine'

/**
 * The display list (round-8 lab spec), pure — `paint(engine, theme)` returns
 * world-space shapes; `canvas.ts` renders them under the view transform. Two
 * first-class themes ship: Light/Manuscript (warm paper, inset wells, unified
 * dark linework) and Dark/Slate (glowing cyan linework, deepened wells,
 * relational wires glowing in their order-ladder hue like their atoms).
 *
 * Laws enforced by construction and checked in paint.test.ts: text appears
 * ONLY on named refs; boundary wires exit the frame while internal singletons
 * get a wire-owned end body; semantic-node rails share one theme-owned stroke and width;
 * a relational wire's colour codes the order of its signature and an atom
 * strokes in its head wire's rung.
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
  readonly relationHueLightness: number
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
  /** A traced wire stroke: the Hobby cubic chain, with its shared samples
      (`pts`) for energy/hit-test identity. There is deliberately NO sampled-
      polyline stroke shape — a wire stroke that is not the painted cubics is
      unrepresentable (the 2026-07-30 highlight-discretization defect). */
  | { readonly kind: 'bezierPath'; readonly cubics: readonly { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }[]; readonly pts: readonly Vec2[]; readonly stroke: string; readonly width: number; readonly glow: string | null }
  /** A filled disc whose radius is fixed DEVICE pixels (junction dots): stays a
      constant size under zoom, unlike world-scaled circles. */
  | { readonly kind: 'dot'; readonly center: Vec2; readonly rPx: number; readonly fill: string }
  | { readonly kind: 'label'; readonly center: Vec2; readonly text: string; readonly color: string; readonly r: number; readonly font: string }

const FRAME_STROKE_W = 2
const DISC_RIM_W = 1.4
const PORT_DOT_R = 2.6
const JUNCTION_OUTER_R = 3.6
const JUNCTION_INNER_R = 2.6
/** Device-pixel radius of the port-order pip (junction-dot family). */
const PIP_R = 3.2
/** The sheet's port-0 origin must dominate ordinary existential-sized ports. */
const FRAME_ORIGIN_R = 5.2
/** Hover-group highlight: lightness bump and extra stroke width over the base. */
const HL_BRIGHT = 18
const HL_WIDTH = 0.8

/** The point-node glyph: a paper halo under a filled pip in the wire's colour.
    Fixed device-pixel radii — a point node never scales into a medium circle. */
function pointNode(center: Vec2, fill: string, paper: string): Shape[] {
  return [
    { kind: 'dot', center, rPx: JUNCTION_OUTER_R, fill: paper },
    { kind: 'dot', center, rPx: JUNCTION_INNER_R, fill },
  ]
}

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

/** All line anatomy owned by one semantic node. */
function anatomyOutline(e: Engine, b: Body, g: NodeGeometry, stroke: string, width: number, glow: string | null): Shape[] {
  const ascale = ascaleOf(b.kind) * e.scale
  const out: Shape[] = []
  for (const a of g.arcs) {
    out.push({ kind: 'arc', center: b.pos, r: a.r * ascale, a0: a.a0 + b.theta, a1: a.a1 + b.theta, stroke, width, glow })
  }
  for (const radial of g.radials) {
    out.push({
      kind: 'segment',
      from: localToWorld(e, b, {
        x: Math.cos(radial.angle) * radial.r0,
        y: Math.sin(radial.angle) * radial.r0,
      }),
      to: localToWorld(e, b, {
        x: Math.cos(radial.angle) * radial.r1,
        y: Math.sin(radial.angle) * radial.r1,
      }),
      stroke,
      width,
      glow,
    })
  }
  if (g.exitArc !== null) {
    out.push({
      kind: 'arc',
      center: b.pos,
      r: g.exitArc.r * ascale,
      a0: g.exitArc.a0 + b.theta,
      a1: g.exitArc.a1 + b.theta,
      stroke,
      width,
      glow,
    })
  }
  if (g.exitLine !== null) {
    out.push({
      kind: 'segment',
      from: localToWorld(e, b, g.exitLine[0]),
      to: localToWorld(e, b, g.exitLine[1]),
      stroke,
      width,
      glow,
    })
  }
  return out
}

const transformLambdaPoint = (point: Vec2, center: Vec2, theta: number, scale: number): Vec2 => {
  const cosine = Math.cos(theta), sine = Math.sin(theta)
  return {
    x: center.x + (point.x * cosine - point.y * sine) * scale,
    y: center.y + (point.x * sine + point.y * cosine) * scale,
  }
}

const motionAlpha = (color: string, alpha: number): string => {
  const byte = Math.max(0, Math.min(255, Math.round(alpha * 255))).toString(16).padStart(2, '0')
  return /^#[0-9a-f]{6}$/i.test(color) ? `${color}${byte}` : color
}

/** Paint one shared Lambda motion frame in the same local plane as a term body. */
export function paintLambdaFrame(
  frame: LambdaStrokeFrame,
  center: Vec2,
  theta: number,
  scale: number,
  width: number,
  wireGlow: boolean,
): Shape[] {
  const shapes: Shape[] = frame.strokes.map((stroke): Shape => {
    const glow = wireGlow ? stroke.color : null
    if (stroke.geometry.kind === 'arc') {
      return {
        kind: 'arc', center,
        r: stroke.geometry.r * scale,
        a0: stroke.geometry.a0 + theta,
        a1: stroke.geometry.a1 + theta,
        stroke: stroke.color, width, glow,
      }
    }
    return {
      kind: 'segment',
      from: transformLambdaPoint(stroke.geometry.from, center, theta, scale),
      to: transformLambdaPoint(stroke.geometry.to, center, theta, scale),
      stroke: stroke.color, width, glow,
    }
  })
  for (const socket of frame.sockets) {
    if (socket.amount <= 0.002) continue
    shapes.push({
      kind: 'circle',
      center: transformLambdaPoint(socket.point, center, theta, scale),
      r: (0.16 + socket.copyIndex * 0.025) * scale,
      fill: null,
      stroke: motionAlpha(ARGUMENT_COLOR, socket.amount),
      width: Math.max(1, width * 0.64),
      insetColor: null,
      glow: null,
    })
  }
  return shapes
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

/** The wire pass of the base painter: legs, boundary exits, the frame pip,
    and junction dots. Exported (and overridable via
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
  // An unattached boundary wire is already a formal port: paint it exactly at
  // its canonical frame slot rather than inventing a floating existential body.
  // The origin slot gets only the larger origin marker below, never a stacked
  // second dot.
  for (const [position, wid] of e.boundary.entries()) {
    const w = e.wires.get(wid)
    if (w === undefined || w.binds.length !== 0) continue
    const slot = resolvedFrameSlot(e, position)
    if (slot === null) continue
    if (position !== 0) shapes.push({ kind: 'dot', center: slot.point, rPx: PORT_DOT_R, fill: wireStroke(wid) })
  }
  // Port 0 is always the single prominent reading origin whenever the sheet has
  // a boundary. All remaining ports are read clockwise from this logical port,
  // including after a proof-wide cyclic slot shift.
  if (e.boundary.length > 0 && e.wires.has(e.boundary[0]!)) {
    const origin = resolvedFrameSlot(e, 0)
    if (origin !== null) shapes.push({ kind: 'dot', center: origin.point, rPx: FRAME_ORIGIN_R, fill: st.ink })
  }
  return shapes
}

export function paint(e: Engine, st: Theme, wires: (e: Engine, st: Theme) => Shape[] = paintWires): Shape[] {
  const fb = frameBounds(e)
  if (fb === null) throw new Error('paint requires a settled engine: call settleStep/settle first')
  const hues = relationWireHues(e.d, st.relationHueLightness)
  const headWireOf = atomHeadWires(e.d)
  const ownerWireOf = new Map<string, WireId>()
  for (const [wid, wire] of e.wires) {
    for (const bind of wire.binds) {
      if (e.bodies.get(bind.body)?.kind === 'identity' && !ownerWireOf.has(bind.body)) {
        ownerWireOf.set(bind.body, wid)
      }
    }
  }
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const bodyStroke = (body: Body): string => {
    const owner = body.kind === 'atom' ? headWireOf.get(body.id) : ownerWireOf.get(body.id)
    return owner === undefined ? st.wire : hues.get(owner) ?? st.wire
  }
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

  // Every materialized body owns its anatomy here. Wire ownership selects only
  // stroke hue; the wire pass never synthesizes small-body geometry. An
  // identity is a point node: the two-dot pip glyph, never a stroked rail.
  for (const b of e.bodies.values()) {
    if (b.kind === 'anchor') continue
    if (b.kind === 'identity') {
      shapes.push(...pointNode(b.pos, bodyStroke(b), st.paper))
      continue
    }
    const node = b.node
    if (node?.kind === 'ref') {
      const discR = DISC_R * e.scale
      shapes.push({ kind: 'circle', center: b.pos, r: discR, fill: st.discFill, stroke: st.ink, width: DISC_RIM_W, insetColor: null, glow: null })
      shapes.push({ kind: 'label', center: b.pos, text: referenceDisplayLabel(node.defId), color: st.discText, r: discR, font: st.font })
      if (pipArity(b) >= 2) shapes.push(pipAt(b, discR, st.ink))
      continue
    }
    const g = b.geometry
    if (g === null) continue
    const ascale = ascaleOf(b.kind) * e.scale
    const stroke = b.kind === 'term' ? st.wire : bodyStroke(b)
    shapes.push(...anatomyOutline(e, b, g, stroke, st.wireW, glow(stroke)))
    if (node?.kind === 'atom' && pipArity(b) >= 2) {
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
 * Every overlay producer uses this — a wire stroke that is not the painted
 * cubics is unrepresentable (USER 2026-07-30: the sampled-polyline overlays
 * read as a discretization of the wire).
 */
export function wireOverlayShapes(
  e: Engine, wid: WireId, stroke: string, width: number, glow: string | null = null,
  legFilter: ((leg: Leg) => boolean) | null = null,
): Shape[] {
  const out: Shape[] = []
  for (const { leg, pts, cubics } of computeLegs(e)) {
    if (leg.wid !== wid) continue
    if (legFilter !== null && !legFilter(leg)) continue
    out.push({ kind: 'bezierPath', cubics, pts, stroke, width, glow })
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
  mode: 'light',
  name: 'Light (Manuscript)', canvas: '#e8e4d8', paper: '#faf7ee', ink: '#2a2118', frame: '#7a7263',
  wire: '#26343a', wireW: 2.2, negFill: 'rgba(90, 78, 58, 0.12)', rimW: 1.3,
  discFill: '#fffdf6', discText: '#2a2118', font: 'Georgia, serif',
  insetColor: 'rgba(58, 48, 32, 0.13)', wireGlow: false, relationHueLightness: 46,
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
  insetColor: 'rgba(0, 0, 0, 0.32)', wireGlow: true, relationHueLightness: 64,
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
