import type { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../../src/kernel/diagram/diagram'
import type { Sig } from '../../src/kernel/diagram/sig'
import { IOTA } from '../../src/kernel/diagram/sig'
import { isPinEndpoint } from '../../src/kernel/rules/wire-ends'

/**
 * A wire with no content whose quantifier sits at `region`: the two pins are
 * its only incidences, so its derived scope is exactly `region`. This is what
 * an endpoint-free wire with a stored scope becomes now that scope is derived.
 */
export function bareWire(
  builder: DiagramBuilder,
  region: RegionId,
  sig: Sig = IOTA,
): WireId {
  const wire = builder.wire([], sig)
  builder.pin(wire, region)
  builder.pin(wire, region)
  return wire
}

/** A wire's real attachments: everything but the pins holding its quantifier. */
export function contentEndpoints(diagram: Diagram, wireId: WireId): readonly Endpoint[] {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new Error(`unknown wire '${wireId}'`)
  return wire.endpoints.filter((endpoint) => !isPinEndpoint(diagram, endpoint))
}

/**
 * Raw parts for a bare wire at `region` — the wire and the two pins that are
 * its only incidences — for fixtures written as diagram literals rather than
 * through the builder. Pin ids derive from the wire id.
 */
export function bareWireParts(
  wireId: WireId,
  region: RegionId,
  sig: Sig = IOTA,
): {
  readonly nodes: Record<NodeId, DiagramNode>
  readonly wires: Record<WireId, Wire>
} {
  const ends = [`${wireId}_pin0`, `${wireId}_pin1`]
  return {
    nodes: Object.fromEntries(ends.map((id) => [
      id,
      { kind: 'identity', region, sig, arity: 1 } satisfies DiagramNode,
    ])),
    wires: {
      [wireId]: {
        sig,
        endpoints: ends.map((id) => ({ node: id, port: { kind: 'identity', index: 0 } })),
      },
    },
  }
}
