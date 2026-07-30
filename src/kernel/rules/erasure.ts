import type { Diagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'

/** Ordinary erasure deletes any selected subgraph from a positive region.
 * Replayed backward it deletes from a negative region: its reverse reading
 * is insertion into a negative context — hypothesis weakening. */
export function applyErasure(
  d: Diagram,
  sel: SubgraphSelection,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, sel.region)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}erasure requires a `
      + `${need} region; '${sel.region}' is ${have}`,
    )
  }
  return removeSubgraph(d, sel)
}
