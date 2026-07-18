import type { Diagram, NodeId, RegionId, WireId } from '../../../kernel/diagram/diagram'
import type { SubgraphSelection } from '../../../kernel/diagram/subgraph/selection'
import { mkSelection } from '../../../kernel/diagram/subgraph/selection'
import { resolvedFrameSlot, type Engine } from '../../../view/engine'
import { legPaths, existentialStubs } from '../../../view/wires'
import type { Vec2 } from '../../../view/vec'
import { length, sub } from '../../../view/vec'

export type Hit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

type WireHit = Extract<Hit, { readonly kind: 'wire' }>

/** View information needed to express device-pixel interaction sizes in the
    engine's world coordinates. Callers must supply the scale used to paint the
    geometry being picked; there is deliberately no implicit/default scale. */
export type HitViewport = { readonly scale: number }

/** Device-pixel radius around a wire centerline or semantic wire marker. */
const WIRE_HIT_RADIUS_PX = 6

function wireHitRadius(viewport: HitViewport): number {
  if (!Number.isFinite(viewport.scale) || viewport.scale <= 0) {
    throw new RangeError('hit-test viewport scale must be finite and positive')
  }
  return WIRE_HIT_RADIUS_PX / viewport.scale
}
function segmentDistance(p: Vec2, a: Vec2, b: Vec2): number {
  const ab = sub(b, a)
  const ap = sub(p, a)
  const len2 = ab.x * ab.x + ab.y * ab.y
  const t = len2 === 0 ? 0 : Math.max(0, Math.min(1, (ap.x * ab.x + ap.y * ab.y) / len2))
  return length(sub(p, { x: a.x + ab.x * t, y: a.y + ab.y * t }))
}

/** Nearest distance from a point to a traced-leg polyline. */
function polylineDistance(p: Vec2, pts: readonly Vec2[]): number {
  let best = Infinity
  for (let i = 1; i < pts.length; i++) best = Math.min(best, segmentDistance(p, pts[i - 1]!, pts[i]!))
  return best
}

/**
 * Topmost engine item under the point: semantic wire markers, then a node disc,
 * then a wire stroke (leg spline, frame exit, or ∃ stub), then the smallest
 * containing region. Junction dots sit on their wires' legs, so a click on one
 * resolves to the wire — junctions are not kernel entities and are never selected.
 */
type WireCandidate = { readonly id: WireId; readonly distance: number }

function nearer(a: WireCandidate, b: WireCandidate): WireCandidate {
  if (a.distance !== b.distance) return a.distance < b.distance ? a : b
  return a.id < b.id ? a : b
}

function nearestWire(candidates: readonly WireCandidate[], radius: number): WireHit | null {
  const byWire = new Map<WireId, WireCandidate>()
  for (const candidate of candidates) {
    if (candidate.distance > radius) continue
    const previous = byWire.get(candidate.id)
    if (previous === undefined || candidate.distance < previous.distance) byWire.set(candidate.id, candidate)
  }
  let best: WireCandidate | null = null
  for (const candidate of byWire.values()) best = best === null ? candidate : nearer(best, candidate)
  return best === null ? null : { kind: 'wire', id: best.id }
}

function boundaryOrDotCandidates(e: Engine, point: Vec2): WireCandidate[] {
  const out: WireCandidate[] = []
  // Boundary incidences are interaction targets at the frame. Use the same
  // resolved geometry as painting and leg solving; port 0's larger origin marker
  // gets a correspondingly larger target while ordinary slots match ∃ dots.
  for (const [position, wid] of e.boundary.entries()) {
    if (!e.wires.has(wid)) continue
    const slot = resolvedFrameSlot(e, position)
    if (slot === null) continue
    out.push({ id: wid, distance: length(sub(point, slot.point)) })
  }
  // ∃ dots first: they are drawn ON TOP of node discs and may rest within
  // a disc's margin ring (paint/hit parity — the topmost target wins)
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    const wid = b.id.startsWith('j:') || b.id.startsWith('x:') ? b.id.slice(2) : null
    if (wid !== null && e.d.wires[wid] !== undefined) out.push({ id: wid, distance: length(sub(point, b.pos)) })
  }
  return out
}

function wireStrokeCandidates(e: Engine, point: Vec2): WireCandidate[] {
  const out: WireCandidate[] = []
  // Every wire — junctions included — is DRAWN as its elastica legs (the junction
  // is a tree of legs), so hit-test those same legs (paint and this share legPaths).
  for (const { wid, pts } of legPaths(e)) {
    out.push({ id: wid, distance: polylineDistance(point, pts) })
  }
  for (const s of existentialStubs(e)) {
    out.push({ id: s.wid, distance: segmentDistance(point, s.from, s.to) })
  }
  return out
}

/** The painted wire under a manipulation pointer. Unlike general selection,
    this deliberately gives a wire endpoint priority over the node rim it meets. */
export function wireHitTest(e: Engine, point: Vec2, viewport: HitViewport): WireHit | null {
  const radius = wireHitRadius(viewport)
  return nearestWire(boundaryOrDotCandidates(e, point), radius)
    ?? nearestWire(wireStrokeCandidates(e, point), radius)
}

export function hitTest(e: Engine, point: Vec2, viewport: HitViewport): Hit | null {
  const radius = wireHitRadius(viewport)
  const topWire = nearestWire(boundaryOrDotCandidates(e, point), radius)
  if (topWire !== null) return topWire
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' || b.kind === 'anchor') continue
    // the drawn disc is scaled by e.scale (paint) — the hit radius must match, or
    // a content-scaled node is clicked at a different size than it is drawn
    if (length(sub(point, b.pos)) <= b.discR * e.scale) return { kind: 'node', id: b.id }
  }
  const stroke = nearestWire(wireStrokeCandidates(e, point), radius)
  if (stroke !== null) return stroke
  let best: { id: RegionId; radius: number } | null = null
  for (const [rid, g] of e.regions) {
    if (e.d.regions[rid]!.kind === 'sheet') continue
    if (length(sub(point, g.center)) <= g.radius && (best === null || g.radius < best.radius)) {
      best = { id: rid, radius: g.radius }
    }
  }
  return best === null ? null : { kind: 'region', id: best.id }
}

/** Brush-specific pick rule. Stationary clicks retain ordinary full-disc
    region targeting; a moving brush claims a region only on its visible ring.
    Node and wire targeting is identical to `hitTest`. */
export function brushHitTest(e: Engine, point: Vec2, viewport: HitViewport, moving: boolean): Hit | null {
  const hit = hitTest(e, point, viewport)
  if (!moving || hit?.kind === 'node' || hit?.kind === 'wire') return hit
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, region] of e.regions) {
    if (e.d.regions[id]!.kind === 'sheet') continue
    const ringDistance = Math.abs(length(sub(point, region.center)) - region.radius)
    if (ringDistance <= 1.5 && (best === null || region.radius < best.radius)) {
      best = { id, radius: region.radius }
    }
  }
  return best === null ? null : { kind: 'region', id: best.id }
}

export type DragTarget =
  | { readonly kind: 'body'; readonly id: string }
  | { readonly kind: 'region'; readonly id: RegionId }

/**
 * What a press-and-drag grabs: any body disc (junctions included — they are
 * draggable geometry even though a CLICK on one resolves to its wire), else
 * the smallest containing region (a grab of a cut/bubble moves its whole
 * subtree), else nothing. Wires are derived geometry and the sheet is the
 * fixed background — neither is draggable.
 */
export function dragTarget(e: Engine, point: Vec2, viewport: HitViewport): DragTarget | null {
  const radius = wireHitRadius(viewport)
  // ∃ dots first (paint/hit parity, same as hitTest): a dot resting inside
  // a disc's margin ring must stay independently grabbable (loose-ends law)
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    if (length(sub(point, b.pos)) <= radius) return { kind: 'body', id: b.id }
  }
  for (const b of e.bodies.values()) {
    if (b.kind === 'anchor') continue // an empty cut is grabbed by its region circle
    if (length(sub(point, b.pos)) <= b.discR * e.scale) return { kind: 'body', id: b.id }
  }
  let best: { id: RegionId; radius: number } | null = null
  for (const [rid, g] of e.regions) {
    if (e.d.regions[rid]!.kind === 'sheet') continue
    if (length(sub(point, g.center)) <= g.radius && (best === null || g.radius < best.radius)) {
      best = { id: rid, radius: g.radius }
    }
  }
  return best === null ? null : { kind: 'region', id: best.id }
}

/**
 * Build a kernel selection from clicked items. The anchor is the common
 * parent: every picked node must live DIRECTLY in it and every picked region
 * must be its direct child — anything deeper needs its enclosing subtree
 * picked instead, and the refusal says so.
 */
export function buildSelection(d: Diagram, items: readonly Hit[]): SubgraphSelection {
  const nodes: NodeId[] = []
  const regions: RegionId[] = []
  const wires: WireId[] = []
  const anchors = new Set<RegionId>()
  for (const item of items) {
    if (item.kind === 'node') {
      const n = d.nodes[item.id]
      if (n === undefined) throw new Error(`unknown node '${item.id}'`)
      nodes.push(item.id)
      anchors.add(n.region)
    } else if (item.kind === 'region') {
      const r = d.regions[item.id]
      if (r === undefined) throw new Error(`unknown region '${item.id}'`)
      if (r.kind === 'sheet') throw new Error('the sheet cannot be selected')
      regions.push(item.id)
      anchors.add(r.parent)
    } else {
      const w = d.wires[item.id]
      if (w === undefined) throw new Error(`unknown wire '${item.id}'`)
      wires.push(item.id)
      anchors.add(w.scope)
    }
  }
  if (anchors.size === 0) throw new Error('nothing selected')
  if (anchors.size > 1) {
    throw new Error(
      `selection spans several regions (${[...anchors].map((a) => `'${a}'`).join(', ')}); select the enclosing cut instead of reaching inside it`,
    )
  }
  const region = [...anchors][0]!
  return mkSelection(d, { region, regions, nodes, wires })
}
