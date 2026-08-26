import type { RegionId } from '../kernel/diagram/diagram'
import type { DiagramSpec } from './spec'
import type { Entity } from './scene'
import type { Vec3 } from './vec3'

/** The full highlight group for a hit entity key: a strand lights its whole
    wire network; a branch lights its whole subtree's lines; a
    ring or label lights the node's ring and label. */
export function expandHover(key: string, spec: DiagramSpec, entities: readonly Entity[]): Set<string> {
  const out = new Set<string>([key])
  const hit = entities.find((entity) => entity.key === key)
  if (hit?.kind === 'lambda') {
    const ownedByHit = (path: readonly string[]): boolean => (
      hit.subtermPath.every((segment, index) => path[index] === segment)
    )
    for (const entity of entities) {
      if (entity.kind === 'lambda' && entity.node === hit.node && ownedByHit(entity.subtermPath)) out.add(entity.key)
    }
    const incidentWires = new Set(
      spec.wires.filter((wire) => wire.terminals.some((terminal) => terminal.node === hit.node)).map((wire) => wire.id),
    )
    for (const entity of entities) {
      if (entity.kind === 'strand' && incidentWires.has(entity.wire)) out.add(entity.key)
    }
    return out
  }
  const [tag, id] = [key.slice(0, 1), key.slice(2)]
  if (tag === 's') {
    const wid = id.slice(0, id.lastIndexOf(':'))
    for (const e of entities) if (e.kind === 'strand' && e.wire === wid) out.add(e.key)
    return out
  }
  if (tag === 'b') {
    const inSubtree = (r: RegionId): boolean => {
      for (let cur: RegionId | null = r; cur !== null; cur = spec.regions.get(cur)!.parent) if (cur === id) return true
      return false
    }
    for (const rid of spec.regions.keys()) {
      if (!inSubtree(rid)) continue
      out.add(`b:${rid}`)
    }
    return out
  }
  if (tag === 'p') {
    // A pip is its identity node: light it with every wire meeting there.
    for (const w of spec.wires) {
      if (!w.terminals.some((t) => t.node === id)) continue
      for (const e of entities) if (e.kind === 'strand' && e.wire === w.id) out.add(e.key)
    }
    return out
  }
  if (tag === 'r' || tag === 'l') {
    for (const e of entities) if ((e.kind === 'ring' || e.kind === 'label') && e.node === id) out.add(e.key)
    // Spec: "a node hit highlights its ring plus incident wire anchors" —
    // light every strand of every wire with a terminal at this node.
    const incidentWires = new Set(spec.wires.filter((w) => w.terminals.some((t) => t.node === id)).map((w) => w.id))
    for (const e of entities) if (e.kind === 'strand' && incidentWires.has(e.wire)) out.add(e.key)
    return out
  }
  return out
}

/** The orbit focus for a picked entity: pips and labels focus their point;
    a strand focuses its whole WIRE (the hover group is the wire, so the
    orbit target is too); everything else focuses its own bounding-box
    center. Null for keys not present in the scene. */
export function focusPoint(key: string, entities: readonly Entity[]): Vec3 | null {
  const hit = entities.find((e) => e.key === key)
  if (hit === undefined) return null
  if ('pos' in hit) return hit.pos
  const pts: Vec3[] = []
  if (hit.kind === 'strand') {
    for (const e of entities) if (e.kind === 'strand' && e.wire === hit.wire) pts.push(...e.pts)
  } else if (hit.kind === 'lambda') {
    const ownedByHit = (path: readonly string[]): boolean => (
      hit.subtermPath.every((segment, index) => path[index] === segment)
    )
    for (const entity of entities) {
      if (entity.kind === 'lambda' && entity.node === hit.node && ownedByHit(entity.subtermPath)) pts.push(...entity.pts)
    }
  } else {
    pts.push(...hit.pts)
  }
  let lo = { x: Infinity, y: Infinity, z: Infinity }
  let hi = { x: -Infinity, y: -Infinity, z: -Infinity }
  for (const p of pts) {
    lo = { x: Math.min(lo.x, p.x), y: Math.min(lo.y, p.y), z: Math.min(lo.z, p.z) }
    hi = { x: Math.max(hi.x, p.x), y: Math.max(hi.y, p.y), z: Math.max(hi.z, p.z) }
  }
  return { x: (lo.x + hi.x) / 2, y: (lo.y + hi.y) / 2, z: (lo.z + hi.z) / 2 }
}
