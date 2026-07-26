import type {
  Diagram,
  DiagramNode,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

/**
 * Rule 4: insert one inherited identity in a negative region. Construction
 * delegates immediately to the canonical diagram owner, so an unconditional
 * same-scope identity collapses instead of surviving as a second authority.
 */
export function applyIdentityInsertion(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
  reservation?: IdReservation,
): Diagram {
  if (polarity(diagram, region) !== 'negative') {
    throw new RuleError('identity insertion requires a negative region')
  }
  if (wires.length < 2 || new Set(wires).size !== wires.length) {
    throw new RuleError('identity insertion requires at least two distinct wires')
  }

  const selected = wires.map((wireId) => [wireId, wireAt(diagram, wireId)] as const)
  const sig = selected[0]![1].sig
  for (const [wireId, wire] of selected) {
    if (!sigEquals(wire.sig, sig)) {
      throw new RuleError(
        `identity insertion wires must have the same signature; `
        + `'${wires[0]}' has '${sigKey(sig)}' but '${wireId}' has '${sigKey(wire.sig)}'`,
      )
    }
    if (!isAncestorOrEqual(diagram, wire.scope, region)) {
      throw new RuleError(
        `identity insertion wire '${wireId}' scoped at '${wire.scope}' is not visible at '${region}'`,
      )
    }
  }

  const nodeId = freshId(
    new Set(Object.keys(diagram.nodes)),
    'identity',
    reservation?.nodes,
  )
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [nodeId]: {
      kind: 'identity',
      region,
      sig,
      arity: wires.length,
    },
  }
  const rebuiltWires: Record<WireId, Wire> = { ...diagram.wires }
  wires.forEach((wireId, index) => {
    const wire = rebuiltWires[wireId]!
    rebuiltWires[wireId] = {
      scope: wire.scope,
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node: nodeId, port: { kind: 'identity', index } },
      ],
    }
  })

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires: rebuiltWires,
  })
}
