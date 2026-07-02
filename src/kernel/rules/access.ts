import type { Diagram, DiagramNode, NodeId, Port, WireId } from '../diagram/diagram'
import { DiagramError, portKey } from '../diagram/diagram'
import { RuleError } from './error'

/** The node, required to be a term node: unknown id is malformed input, an atom is a refusal. */
export function termNodeAt(d: Diagram, nodeId: NodeId): Extract<DiagramNode, { kind: 'term' }> {
  const node = d.nodes[nodeId]
  if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
  if (node.kind !== 'term') throw new RuleError(`this rule applies to term nodes; '${nodeId}' has kind '${node.kind}'`)
  return node
}

/**
 * The unique wire holding (node, port). The port-partition invariant of
 * mkDiagram guarantees existence for every required port of a validated
 * diagram, so a miss means the caller asked about a port the node lacks.
 */
export function wireAt(d: Diagram, node: NodeId, p: Port): WireId {
  const key = portKey(p)
  for (const [id, w] of Object.entries(d.wires)) {
    for (const ep of w.endpoints) {
      if (ep.node === node && portKey(ep.port) === key) return id
    }
  }
  throw new DiagramError(`no wire holds port '${key}' of node '${node}'`)
}
