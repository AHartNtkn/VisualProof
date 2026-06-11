import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Scene } from '../view/scene'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'

export type Hit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

/** UI pick tolerance around wire segments, world units. Visual only. */
const WIRE_TOLERANCE = 1.5

function segmentDistance(p: Vec2, a: Vec2, b: Vec2): number {
  const ab = sub(b, a)
  const ap = sub(p, a)
  const len2 = ab.x * ab.x + ab.y * ab.y
  const t = len2 === 0 ? 0 : Math.max(0, Math.min(1, (ap.x * ab.x + ap.y * ab.y) / len2))
  return length(sub(p, { x: a.x + ab.x * t, y: a.y + ab.y * t }))
}

/** Topmost item under the point: node, then wire, then smallest region. */
export function hitTest(scene: Scene, point: Vec2): Hit | null {
  for (const n of scene.nodes) {
    if (length(sub(point, n.center)) <= n.geometry.outerRadius) {
      return { kind: 'node', id: n.id }
    }
  }
  for (const w of scene.wires) {
    for (const spoke of w.spokes) {
      if (segmentDistance(point, w.hub, spoke) <= WIRE_TOLERANCE) {
        return { kind: 'wire', id: w.id }
      }
    }
  }
  let best: { id: RegionId; radius: number } | null = null
  for (const r of scene.regions) {
    if (r.kind === 'sheet') continue
    if (length(sub(point, r.center)) <= r.radius && (best === null || r.radius < best.radius)) {
      best = { id: r.id, radius: r.radius }
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
