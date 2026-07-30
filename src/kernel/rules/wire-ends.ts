import type {
  Diagram,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, portKey } from '../diagram/diagram'
import type { RelSig } from '../diagram/sig'
import { sigKey } from '../diagram/sig'
import { RuleError } from './error'

export type AppliedEnd = {
  readonly node: NodeId
  readonly region: RegionId
  readonly args: readonly WireId[]
}

export function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

export function relSigOf(
  diagram: Diagram,
  wireId: WireId,
  operation: string,
): RelSig {
  const wire = wireAt(diagram, wireId)
  if (wire.sig.kind !== 'rel') {
    throw new RuleError(
      `${operation} requires a relation-signature wire; `
      + `'${wireId}' has '${sigKey(wire.sig)}'`,
    )
  }
  return wire.sig
}

export function argWireOf(
  diagram: Diagram,
  node: NodeId,
  index: number,
): WireId {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    for (const endpoint of wire.endpoints) {
      if (
        endpoint.node === node
        && endpoint.port.kind === 'arg'
        && endpoint.port.index === index
      ) return wireId
    }
  }
  throw new DiagramError(
    `atom '${node}' has no attached wire at argument ${index}`,
  )
}

/**
 * Every endpoint of the wire must be the head of an atom; content and
 * argument primitives act on all of them uniformly. Merge alone tolerates
 * other endpoint kinds.
 */
export function appliedEnds(
  diagram: Diagram,
  wireId: WireId,
  operation: string,
): AppliedEnd[] {
  const sig = relSigOf(diagram, wireId, operation)
  return wireAt(diagram, wireId).endpoints.map((endpoint) => {
    const node = diagram.nodes[endpoint.node]
    if (
      node === undefined
      || node.kind !== 'atom'
      || endpoint.port.kind !== 'head'
    ) {
      throw new RuleError(
        `${operation} requires every endpoint of '${wireId}' to be an applied `
        + `atom head; '${endpoint.node}'/'${portKey(endpoint.port)}' is not`,
      )
    }
    return {
      node: endpoint.node,
      region: node.region,
      args: sig.args.map((_, index) => argWireOf(diagram, endpoint.node, index)),
    }
  })
}

export function withoutEndpointsOf(
  wires: Record<WireId, Wire>,
  removed: ReadonlySet<NodeId>,
): void {
  for (const [wireId, wire] of Object.entries(wires)) {
    if (wire.endpoints.some((endpoint) => removed.has(endpoint.node))) {
      wires[wireId] = {
        scope: wire.scope,
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          !removed.has(endpoint.node)),
      }
    }
  }
}

export function attachArgs(
  wires: Record<WireId, Wire>,
  node: NodeId,
  args: readonly WireId[],
): void {
  args.forEach((argWire, index) => {
    const wire = wires[argWire]!
    wires[argWire] = {
      scope: wire.scope,
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node, port: { kind: 'arg', index } },
      ],
    }
  })
}
