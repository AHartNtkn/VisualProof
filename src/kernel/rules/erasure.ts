import type { Diagram } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { derivedScope, polarity } from '../diagram/regions'
import type { IdReservation } from '../diagram/subgraph/freshId'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { removeSubgraphParts } from '../diagram/subgraph/splice'
import { completeWireEnds } from './wire-ends'
import { RuleError } from './error'

/** Ordinary erasure deletes any selected subgraph from a positive region.
 * Replayed backward it deletes from a negative region: its reverse reading
 * is insertion into a negative context — hypothesis weakening. Every
 * surviving wire the erased material touched is CAPPED: completion pins at
 * its pre-removal derived scope replace whatever quantifier support the
 * removal took, so no scope moves and no wire drops below two ends (the
 * Lean twin: Erasure.residue — retained content plus unary identities). */
export function applyErasure(
  d: Diagram,
  sel: SubgraphSelection,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, sel.region)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}erasure requires a `
      + `${need} region; '${sel.region}' is ${have}`,
    )
  }
  const contents = selectionContents(d, sel)
  const parts = removeSubgraphParts(d, sel)
  const internal = new Set(contents.internalWires)
  for (const [wireId, wire] of Object.entries(d.wires)) {
    if (internal.has(wireId)) continue
    if (!wire.endpoints.some((ep) => contents.allNodes.has(ep.node))) continue
    completeWireEnds(parts, wireId, derivedScope(d, wireId), 'erasure', reservation?.nodes)
  }
  return mkDiagram({ root: d.root, ...parts })
}
