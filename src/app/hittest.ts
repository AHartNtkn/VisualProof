import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Engine } from '../view/engine'
import type { WirePath } from '../view/wires'
import { legPaths, boundaryExits, existentialStubs } from '../view/wires'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'

export type Hit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

/** UI pick tolerance around wire strokes, world units. Visual only. */
const WIRE_TOLERANCE = 1.5
/** Samples along a Bézier leg when measuring pick distance. */
const WIRE_SAMPLES = 16

function segmentDistance(p: Vec2, a: Vec2, b: Vec2): number {
  const ab = sub(b, a)
  const ap = sub(p, a)
  const len2 = ab.x * ab.x + ab.y * ab.y
  const t = len2 === 0 ? 0 : Math.max(0, Math.min(1, (ap.x * ab.x + ap.y * ab.y) / len2))
  return length(sub(p, { x: a.x + ab.x * t, y: a.y + ab.y * t }))
}

function bezierPoint(path: WirePath, t: number): Vec2 {
  const u = 1 - t
  const a = u * u * u, b = 3 * u * u * t, c = 3 * u * t * t, d = t * t * t
  return {
    x: a * path.from.x + b * path.c1.x + c * path.c2.x + d * path.to.x,
    y: a * path.from.y + b * path.c1.y + c * path.c2.y + d * path.to.y,
  }
}

function bezierDistance(p: Vec2, path: WirePath): number {
  let best = Infinity
  let prev = bezierPoint(path, 0)
  for (let i = 1; i <= WIRE_SAMPLES; i++) {
    const cur = bezierPoint(path, i / WIRE_SAMPLES)
    best = Math.min(best, segmentDistance(p, prev, cur))
    prev = cur
  }
  return best
}

/**
 * Topmost engine item under the point: a node disc first, then a wire stroke
 * (leg spline, frame exit, or ∃ stub), then the smallest containing region.
 * Junction dots sit on their wires' legs, so a click on one resolves to the
 * wire — junctions are not kernel entities and are never selected.
 */
export function hitTest(e: Engine, point: Vec2): Hit | null {
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' || b.kind === 'anchor') continue
    if (length(sub(point, b.pos)) <= b.discR) return { kind: 'node', id: b.id }
  }
  for (const { wid, path } of legPaths(e)) {
    if (bezierDistance(point, path) <= WIRE_TOLERANCE) return { kind: 'wire', id: wid }
  }
  for (const ex of boundaryExits(e)) {
    if (bezierDistance(point, ex.path) <= WIRE_TOLERANCE) return { kind: 'wire', id: ex.wid }
  }
  for (const s of existentialStubs(e)) {
    if (segmentDistance(point, s.from, s.to) <= WIRE_TOLERANCE) return { kind: 'wire', id: s.wid }
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
export function dragTarget(e: Engine, point: Vec2): DragTarget | null {
  for (const b of e.bodies.values()) {
    if (b.kind === 'anchor') continue // an empty cut is grabbed by its region circle
    if (length(sub(point, b.pos)) <= b.discR) return { kind: 'body', id: b.id }
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
