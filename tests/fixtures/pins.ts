import type { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, Endpoint, RegionId, WireId } from '../../src/kernel/diagram/diagram'
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
