import type { Diagram, NodeId } from '../../kernel/diagram/diagram'

export function introducedNodeId(before: Diagram, after: Diagram): NodeId {
  const introduced = Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined)
  if (introduced.length !== 1) {
    throw new Error(`expected one introduced node, found ${introduced.length}`)
  }
  return introduced[0]!
}
