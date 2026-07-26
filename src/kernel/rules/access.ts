import type { Diagram, DiagramNode, NodeId, Port, WireId } from '../diagram/diagram'
import { DiagramError, portKey } from '../diagram/diagram'
import { RuleError } from './error'

/** Resolve one node and require the sole definition-bearing node kind. */
export function refNodeAt(
  diagram: Diagram,
  nodeId: NodeId,
): Extract<DiagramNode, { kind: 'ref' }> {
  const node = diagram.nodes[nodeId]
  if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
  if (node.kind !== 'ref') {
    throw new RuleError(
      `fold/unfold applies to ref nodes; '${nodeId}' has kind '${node.kind}'`,
    )
  }
  return node
}

/** Find the unique wire holding one validated node port. */
export function wireAt(diagram: Diagram, node: NodeId, port: Port): WireId {
  const key = portKey(port)
  for (const [id, wire] of Object.entries(diagram.wires)) {
    for (const endpoint of wire.endpoints) {
      if (endpoint.node === node && portKey(endpoint.port) === key) return id
    }
  }
  throw new DiagramError(`no wire holds port '${key}' of node '${node}'`)
}
