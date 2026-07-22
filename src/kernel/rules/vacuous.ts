import type { Diagram, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { Sig } from '../diagram/sig'
import { sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Vacuous wire introduction: add ONE fresh endpoint-free wire of `sig`,
 * scoped at `scope`. ∃x.⊤ is valid at every signature — every sort has a
 * nonempty domain (λ-terms inhabit TERM; the empty relation inhabits every
 * relational sig) — so the introduced wire is a valid conjunct at ANY
 * polarity: an equivalence in a positive region, a sound weakening in a
 * negative one. No polarity gate is needed, and no atom can reference a
 * wire that did not exist, so nothing downstream is disturbed.
 */
export function applyVacuousIntro(d: Diagram, scope: RegionId, sig: Sig, reservation?: IdReservation): Diagram {
  if (d.regions[scope] === undefined) throw new DiagramError(`unknown region '${scope}'`)
  const wireId = freshId(new Set(Object.keys(d.wires)), `${scope}_vac`, reservation?.wires)
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires: { ...d.wires, [wireId]: { scope, sig, endpoints: [] } },
  })
}

/**
 * Vacuous wire elimination: drop an endpoint-free wire. The reverse
 * direction of the same equivalence (∃x.⊤ ≡ ⊤) — dropping it changes
 * nothing about what the diagram asserts — so it requires EXACTLY zero
 * endpoints; a wired individual is load-bearing and refuses at any
 * polarity.
 */
export function applyVacuousElim(d: Diagram, wireId: WireId): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wire.endpoints.length > 0) {
    throw new RuleError(
      `vacuous elimination requires an endpoint-free wire; '${wireId}' (sig '${sigKey(wire.sig)}') has ${wire.endpoints.length} endpoint(s)`,
    )
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id !== wireId) wires[id] = w
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
