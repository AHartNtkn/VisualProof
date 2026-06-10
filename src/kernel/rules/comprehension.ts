import type { Diagram, DiagramNode, NodeId, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { spliceSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'
import { wireAt } from './access'

/** Remove one node, trimming its endpoints off their wires. */
function dropNode(d: Diagram, nodeId: NodeId): Diagram {
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id !== nodeId) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = { scope: w.scope, endpoints: w.endpoints.filter((ep) => ep.node !== nodeId) }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Rule 8, instantiation direction (spec §3.1): at a NEGATIVE position,
 * ∃R.φ(R) may be replaced by φ(G) — splice a copy of the comprehension G at
 * every atom the bubble binds (boundary wire i onto the atom's arg-i wire),
 * then dissolve the bubble, promoting its contents to its parent. The gate
 * tests the bubble's own polarity, which equals its parent's: bubbles never
 * flip parity (spec §2.1).
 */
export function applyComprehensionInstantiate(
  d: Diagram,
  bubbleId: RegionId,
  comp: DiagramWithBoundary,
): Diagram {
  const bubble = d.regions[bubbleId]
  if (bubble === undefined) throw new DiagramError(`unknown region '${bubbleId}'`)
  if (bubble.kind !== 'bubble') {
    throw new RuleError(`comprehension instantiation requires a bubble; '${bubbleId}' is a ${bubble.kind}`)
  }
  if (polarity(d, bubbleId) !== 'negative') {
    throw new RuleError(`comprehension instantiation requires a negative bubble; '${bubbleId}' is positive`)
  }
  if (comp.boundary.length !== bubble.arity) {
    throw new RuleError(
      `arity mismatch: bubble '${bubbleId}' binds a relation of arity ${bubble.arity}, but the comprehension has ${comp.boundary.length} boundary wires`,
    )
  }
  const atoms = Object.entries(d.nodes).filter(
    (entry): entry is [NodeId, Extract<DiagramNode, { kind: 'atom' }>] =>
      entry[1].kind === 'atom' && entry[1].binder === bubbleId,
  )
  let cur = d
  for (const [atomId, atom] of atoms) {
    const args: WireId[] = []
    for (let i = 0; i < bubble.arity; i++) {
      args.push(wireAt(cur, atomId, { kind: 'arg', index: i }))
    }
    cur = spliceSubgraph(cur, atom.region, comp, args)
    cur = dropNode(cur, atomId)
  }
  // dissolve the bubble: promote child regions, nodes, and wire scopes
  const parent = bubble.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(cur.regions)) {
    if (id === bubbleId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === bubbleId
      ? (r.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: r.arity })
      : r
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(cur.nodes)) {
    nodes[id] = n.region === bubbleId
      ? (n.kind === 'term'
        ? { kind: 'term', region: parent, term: n.term }
        : { kind: 'atom', region: parent, binder: n.binder })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(cur.wires)) {
    wires[id] = w.scope === bubbleId ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: cur.root, regions, nodes, wires })
}
