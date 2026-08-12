import type { Diagram, Endpoint, RegionId, WireId } from '../kernel/diagram/diagram'
import { pkey, resolvedFrameSlot, type Engine, type LegEnd } from '../view/engine'
import { computeLegs, legPaths, wireOwnedEnds } from '../view/wires'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'
import type { Hit } from './hit-selection'

export { buildSelection, type Hit } from './hit-selection'

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
 * then a routed wire stroke, then the smallest
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
  // Wire-owned bodies resolve to their semantic wire over their rendered disc.
  for (const { wid, body } of wireOwnedEnds(e)) {
    const centerDistance = length(sub(point, body.pos))
    out.push({ id: wid, distance: Math.max(0, centerDistance - body.discR * e.scale) })
  }
  return out
}

function wireStrokeCandidates(e: Engine, point: Vec2): WireCandidate[] {
  const out: WireCandidate[] = []
  // Every wire — junctions included — is DRAWN as its routed strokes (the junction
  // is a tree of legs), so hit-test those same legs (paint and this share legPaths).
  for (const { wid, pts } of legPaths(e)) {
    out.push({ id: wid, distance: polylineDistance(point, pts) })
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

export type WireManipulationHit = {
  readonly kind: 'endpoint'
  readonly wire: WireId
  readonly endpoint: Endpoint
} | {
  readonly kind: 'looseEnd' | 'via'
  readonly wire: WireId
  readonly body: string
  readonly region: RegionId
} | {
  readonly kind: 'wireBody'
  readonly wire: WireId
} | {
  readonly kind: 'frame'
  readonly wire: WireId
  readonly position: number
}

export type PendingWireGeometry = {
  readonly wire: WireId
  readonly bodyPaths: readonly (readonly Vec2[])[]
  readonly looseEnd: Vec2
}

export type PendingWireHit =
  | { readonly kind: 'pendingLooseEnd'; readonly wire: WireId }
  | { readonly kind: 'pendingWireBody'; readonly wire: WireId }

/**
 * Pick the displayed parts of a controller-local pending wire. The connection
 * controller owns lifecycle and geometry; this shared hit authority alone
 * decides which physical wire part the pointer names.
 */
export function pendingWireHitTest(
  geometry: PendingWireGeometry,
  point: Vec2,
  viewport: HitViewport,
): PendingWireHit | null {
  const radius = wireHitRadius(viewport)
  if (length(sub(point, geometry.looseEnd)) <= radius) {
    return { kind: 'pendingLooseEnd', wire: geometry.wire }
  }
  if (geometry.bodyPaths.some((path) => polylineDistance(point, path) <= radius)) {
    return { kind: 'pendingWireBody', wire: geometry.wire }
  }
  return null
}

function endpointForLegEnd(e: Engine, wire: WireId, end: LegEnd): Endpoint | null {
  if (end.key === null || e.d.nodes[end.body] === undefined) return null
  return e.d.wires[wire]?.endpoints.find((endpoint) =>
    endpoint.node === end.body && pkey(endpoint.port) === end.key) ?? null
}

/** A wire hit enriched only when the pointer is on the terminal halo of a
    concrete node port. Trunks, branch junctions, existential dots, and frame
    slots remain wire hits but deliberately carry no guessed endpoint. */
export function wireManipulationHitTest(
  e: Engine,
  point: Vec2,
  viewport: HitViewport,
): WireManipulationHit | null {
  const hit = wireHitTest(e, point, viewport)
  if (hit === null) return null
  const radius = wireHitRadius(viewport)
  let marker: {
    readonly kind: 'looseEnd' | 'via' | 'frame'
    readonly body?: string
    readonly region?: RegionId
    readonly position?: number
    readonly distance: number
  } | null = null
  for (const [position, wire] of e.boundary.entries()) {
    if (wire !== hit.id) continue
    const slot = resolvedFrameSlot(e, position)
    if (slot === null) continue
    const distance = length(sub(point, slot.point))
    if (distance <= radius && (marker === null || distance < marker.distance)) {
      marker = { kind: 'frame', position, distance }
    }
  }
  for (const prefix of ['j:', 'x:'] as const) {
    const body = e.bodies.get(`${prefix}${hit.id}`)
    if (body === undefined) continue
    const distance = length(sub(point, body.pos))
    if (distance <= radius && (marker === null || distance < marker.distance)) {
      marker = {
        kind: prefix === 'j:' ? 'looseEnd' : 'via',
        body: body.id,
        region: body.region,
        distance,
      }
    }
  }
  if (marker?.kind === 'frame') {
    return { kind: 'frame', wire: hit.id, position: marker.position! }
  }
  if (marker !== null) {
    return {
      kind: marker.kind,
      wire: hit.id,
      body: marker.body!,
      region: marker.region!,
    }
  }
  let best: { readonly endpoint: Endpoint; readonly distance: number } | null = null
  for (const geometry of computeLegs(e)) {
    if (geometry.leg.wid !== hit.id || geometry.pts.length === 0) continue
    for (const [end, at] of [
      [geometry.leg.from, geometry.pts[0]!],
      [geometry.leg.to, geometry.pts.at(-1)!],
    ] as const) {
      const endpoint = endpointForLegEnd(e, hit.id, end)
      if (endpoint === null) continue
      const distance = length(sub(point, at))
      if (distance <= radius && (best === null || distance < best.distance)) best = { endpoint, distance }
    }
  }
  return best === null
    ? { kind: 'wireBody', wire: hit.id }
    : { kind: 'endpoint', wire: hit.id, endpoint: best.endpoint }
}

export function hitTest(e: Engine, point: Vec2, viewport: HitViewport): Hit | null {
  const radius = wireHitRadius(viewport)
  const topWire = nearestWire(boundaryOrDotCandidates(e, point), radius)
  if (topWire !== null) return topWire
  for (const b of e.bodies.values()) {
    if (b.kind === 'end' || b.kind === 'anchor') continue
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

/** The smallest cut disc containing the point, else the diagram's root. */
export function regionAt(e: Engine, diagram: Diagram, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of e.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (
      length(sub(point, geometry.center)) <= geometry.radius
      && (best === null || geometry.radius < best.radius)
    ) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
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
  | { readonly kind: 'carrier'; readonly id: string }
  | { readonly kind: 'region'; readonly id: RegionId }

/**
 * What a press-and-drag grabs: any body disc (junctions included — they are
 * draggable geometry even though a CLICK on one resolves to its wire), else
 * the smallest containing region (a grab of a cut moves its whole
 * subtree), else nothing. Wires are derived geometry and the sheet is the
 * fixed background — neither is draggable.
 */
export function dragTarget(e: Engine, point: Vec2, _viewport: HitViewport): DragTarget | null {
  for (const b of e.bodies.values()) {
    if (b.kind === 'anchor') continue // an empty cut is grabbed by its region circle
    if (length(sub(point, b.pos)) <= b.discR * e.scale) return { kind: 'carrier', id: b.id }
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
