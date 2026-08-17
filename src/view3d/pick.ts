import type { RegionId } from '../kernel/diagram/diagram'
import type { DiagramSpec } from './spec'
import type { Entity } from './scene'

/** The full highlight group for a hit entity key: a strand lights its whole
    wire network; a branch lights its whole subtree's lines; a
    ring or label lights the node's ring and label. */
export function expandHover(key: string, spec: DiagramSpec, entities: readonly Entity[]): Set<string> {
  const out = new Set<string>([key])
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
