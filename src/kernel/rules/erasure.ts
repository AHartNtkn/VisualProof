import type { Diagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { requireRemovalScopePreserved } from './wire-ends'
import { RuleError } from './error'

/** Ordinary erasure deletes any selected subgraph from a positive region.
 * Replayed backward it deletes from a negative region: its reverse reading
 * is insertion into a negative context — hypothesis weakening. Surviving
 * touching wires must keep their derived scopes and their two ends (spec
 * §5, class (b)): erasing a scope-supporting incidence would silently move
 * a quantifier, so the rule refuses until the wire is pinned. */
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
  const contents = selectionContents(d, sel)
  requireRemovalScopePreserved(
    d,
    contents.allNodes,
    new Set(contents.internalWires),
    'erasure',
  )
  return removeSubgraph(d, sel)
}
