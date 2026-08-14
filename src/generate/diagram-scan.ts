import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { relSig, sigEquals } from '../kernel/diagram/sig'

const PROPOSITION = relSig([])

export function childCuts(diagram: Diagram, parent: RegionId): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) => region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

export function nodesIn(diagram: Diagram, region: RegionId): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
    .sort()
}

/** Wires of the nullary-relation (proposition) signature. */
export function propWires(diagram: Diagram): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => sigEquals(wire.sig, PROPOSITION))
    .map(([id]) => id)
    .sort()
}

/** Wires all of whose endpoints are arity-1 identity pins (vacuity-deletable). */
export function bareWires(diagram: Diagram): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.every(({ node }) => {
      const at = diagram.nodes[node]
      return at !== undefined && at.kind === 'identity' && at.arity === 1
    }))
    .map(([id]) => id)
    .sort()
}

/** The wire attached to an atom node's head port. */
export function headWireOf(diagram: Diagram, nodeId: NodeId): WireId {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wire.endpoints.some(({ node, port }) => node === nodeId && port.kind === 'head')) return wireId
  }
  throw new Error(`headWireOf: atom node '${nodeId}' has no head wire`)
}
