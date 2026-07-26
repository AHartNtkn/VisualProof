import type { Diagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'

/** Ordinary erasure deletes any selected subgraph from a positive region.
 * Negative insertion is owned by concrete insertion rules; there is no
 * backward-erasure insertion API. */
export function applyErasure(
  d: Diagram,
  sel: SubgraphSelection,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  if (orientation === 'backward') {
    throw new RuleError('backward erasure is not supported; erasure is forward-only')
  }
  const need = 'positive'
  const have = polarity(d, sel.region)
  if (have !== need) {
    throw new RuleError(`erasure requires a ${need} region; '${sel.region}' is ${have}`)
  }
  return removeSubgraph(d, sel)
}
