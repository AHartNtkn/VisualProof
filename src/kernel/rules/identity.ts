import type {
  Diagram,
  DiagramNode,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { derivedScope, polarity, wireVisibleAt } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

/**
 * Gated equality assertion (spec §4.1): physically insert one identity node.
 * Forward replay requires a negative region; backward replay the dual
 * positive region. The node persists — nothing rewrites identity content
 * eagerly; visibility keeps every touched wire's derived scope fixed.
 */
export function applyIdentityInsertion(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  if (polarity(diagram, region) !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `identity insertion requires a ${need} region`,
    )
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
    if (!wireVisibleAt(diagram, wireId, region)) {
      throw new RuleError(
        `identity insertion wire '${wireId}' scoped at '${derivedScope(diagram, wireId)}' is not visible at '${region}'`,
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
