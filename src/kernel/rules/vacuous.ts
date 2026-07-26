import type { Diagram, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { Sig } from '../diagram/sig'
import { sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/** Add one endpoint-free wire of any well-formed signature at any polarity. */
export function applyVacuousIntro(
  diagram: Diagram,
  scope: RegionId,
  sig: Sig,
  reservation?: IdReservation,
): Diagram {
  if (diagram.regions[scope] === undefined) {
    throw new DiagramError(`unknown region '${scope}'`)
  }
  const wireId = freshId(
    new Set(Object.keys(diagram.wires)),
    `${scope}_vac`,
    reservation?.wires,
  )
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes: { ...diagram.nodes },
    wires: {
      ...diagram.wires,
      [wireId]: { scope, sig, endpoints: [] },
    },
  })
}

/** Eliminate only an endpoint-free wire; attached content is load-bearing. */
export function applyVacuousElim(
  diagram: Diagram,
  wireId: WireId,
): Diagram {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wire.endpoints.length !== 0) {
    throw new RuleError(
      `vacuous elimination requires an endpoint-free wire; `
      + `'${wireId}' (sig '${sigKey(wire.sig)}') has `
      + `${wire.endpoints.length} endpoint(s)`,
    )
  }

  const wires: Record<WireId, Wire> = {}
  for (const [id, candidate] of Object.entries(diagram.wires)) {
    if (id !== wireId) wires[id] = candidate
  }
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes: { ...diagram.nodes },
    wires,
  })
}
