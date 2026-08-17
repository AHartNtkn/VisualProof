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
import { applyVacuityDelete } from '../../src/kernel/rules/identity-rules'
import { nextRemovablePinStep } from '../../src/kernel/proof/pin-sweep'

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

/**
 * Detach exactly the caps a removal minted: every arity-1 identity present
 * in `after` but not in `before`, removed by vacuity pin deletion. The
 * exact inverse of the removal residue — deiterate-then-detachCaps is the
 * old round-trip.
 */
export function detachCaps(before: Diagram, after: Diagram): Diagram {
  let current = after
  for (const [id, node] of Object.entries(after.nodes)) {
    if (before.nodes[id] !== undefined) continue
    if (node.kind !== 'identity' || node.arity !== 1) continue
    const wireEntry = Object.entries(current.wires)
      .find(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === id))
    if (wireEntry === undefined) throw new Error(`cap '${id}' holds no wire`)
    current = applyVacuityDelete(current, {
      kind: 'pin', wire: wireEntry[0], node: id, region: node.region,
    })
  }
  return current
}

/**
 * Sweep every ⊤-idle pin, exactly as the recorder's tidy pass does after
 * each action (proof/pin-sweep.ts): tests that apply raw steps use this to
 * reach the same pin-minimal shape recorded derivations settle into.
 */
export function sweepRemovablePins(diagram: Diagram): Diagram {
  let current = diagram
  for (;;) {
    const step = nextRemovablePinStep(current)
    if (step === null) return current
    if (step.rule !== 'vacuity' || step.direction !== 'delete') {
      throw new Error('pin sweep produced a non-vacuity step')
    }
    current = applyVacuityDelete(current, step.instance)
  }
}
