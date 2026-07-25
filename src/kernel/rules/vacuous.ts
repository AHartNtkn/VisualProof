import type { Diagram, DiagramNode, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { Sig } from '../diagram/sig'
import { sigKey } from '../diagram/sig'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { attachBodyCore } from './body'
import { RuleError } from './error'

/**
 * The optional bodied form of a vacuous introduction: attach a witness body to
 * the freshly introduced wire in the same step. `content` is the comprehension
 * `G` (arg stubs then parameter stubs); `params` are the host lines feeding its
 * parameter ports.
 */
export type VacuousBody = {
  readonly content: DiagramWithBoundary
  readonly params: readonly WireId[]
}

/**
 * Vacuous wire introduction. Two valid forms, both at ANY polarity:
 *
 *  - BARE (`body` omitted): add one endpoint-free wire of `sig`. ∃x.⊤ is valid
 *    at every signature — every sort has a nonempty domain (λ-terms inhabit
 *    IOTA; the empty relation inhabits every relational sig) — so the wire is a
 *    valid conjunct at any polarity: an equivalence positively, a sound
 *    weakening negatively. No atom can reference a wire that did not exist, so
 *    nothing downstream is disturbed.
 *
 *  - BODIED (`body` given): add the wire AND a witness body node in one step —
 *    the wire's only attachment is that body's output; the body may draw on
 *    `params`. This asserts `∃R. R=G`, the COMPREHENSION AXIOM: for any drawable
 *    `G` (with any parameters — comprehension with parameters is still valid) a
 *    relation equal to `G` exists, so `∃R. R=G ≡ ⊤` is a tautology introducible
 *    at any polarity, exactly like the bare `∃x.⊤`. The body coherence gates
 *    (boundary arithmetic, arg-stub sorts) come from `attachBodyCore`/mkDiagram;
 *    the parameter scope gate is at-or-outside the new wire's scope.
 *
 * The bodied form makes the derived comprehension macros orientation-uniform:
 * abstraction introduces `∃R. R=G` (any polarity here), folds occurrences, then
 * detaches the witness (the single polarity-gated step).
 */
export function applyVacuousIntro(
  d: Diagram,
  scope: RegionId,
  sig: Sig,
  reservation?: IdReservation,
  body?: VacuousBody,
): Diagram {
  if (d.regions[scope] === undefined) throw new DiagramError(`unknown region '${scope}'`)
  const wireId = freshId(new Set(Object.keys(d.wires)), `${scope}_vac`, reservation?.wires)
  const withWire = mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires: { ...d.wires, [wireId]: { scope, sig, endpoints: [] } },
  })
  if (body === undefined) return withWire
  return attachBodyCore(withWire, wireId, body.content, body.params, reservation)
}

/**
 * Vacuous wire elimination — the reverse of introduction, at ANY polarity. Two
 * valid forms mirroring intro:
 *
 *  - BARE: drop a wire with EXACTLY zero endpoints (∃x.⊤ ≡ ⊤). A wired
 *    individual is load-bearing and refuses.
 *  - BODIED: drop a wire whose SOLE endpoint is its own body node's output
 *    port — the tautology `∃R. R=G` — removing the wire and that body node
 *    (trimming the body's parameter endpoints off their wires). The body may
 *    hold parameter endpoints on OTHER wires; only its own output rides this
 *    wire. Any other endpoint mix (an atom still referencing the wire, or a
 *    body sharing the wire with other attachments) is load-bearing and refuses.
 */
export function applyVacuousElim(d: Diagram, wireId: WireId): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)

  if (wire.endpoints.length === 0) {
    const wires: Record<WireId, Wire> = {}
    for (const [id, w] of Object.entries(d.wires)) {
      if (id !== wireId) wires[id] = w
    }
    return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
  }

  const only = wire.endpoints.length === 1 ? wire.endpoints[0]! : undefined
  if (only !== undefined && only.port.kind === 'output' && d.nodes[only.node]?.kind === 'body') {
    const bodyId = only.node
    const nodes: Record<string, DiagramNode> = {}
    for (const [id, n] of Object.entries(d.nodes)) {
      if (id !== bodyId) nodes[id] = n
    }
    const wires: Record<WireId, Wire> = {}
    for (const [id, w] of Object.entries(d.wires)) {
      if (id === wireId) continue
      wires[id] = { scope: w.scope, sig: w.sig, endpoints: w.endpoints.filter((ep) => ep.node !== bodyId) }
    }
    return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
  }

  throw new RuleError(
    `vacuous elimination requires an endpoint-free wire or a solely-bodied wire; '${wireId}' (sig '${sigKey(wire.sig)}') has ${wire.endpoints.length} endpoint(s)`,
  )
}
