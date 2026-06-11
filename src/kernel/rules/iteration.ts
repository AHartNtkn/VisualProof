import type { Diagram, RegionId } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../diagram/subgraph/splice'
import { findOccurrences, type Occurrence } from '../diagram/subgraph/match'
import { RuleError } from './error'

/**
 * Rule 3a (spec §3.1): copy a subgraph into its own region or any descendant
 * not inside the copy, the copy's boundary attaching to the same wires.
 * Sound everywhere — no polarity gate.
 */
export function applyIteration(d: Diagram, sel: SubgraphSelection, targetRegion: RegionId): Diagram {
  const c = selectionContents(d, sel) // validates the selection loudly
  if (!isAncestorOrEqual(d, sel.region, targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' must lie within the source region '${sel.region}'`)
  }
  if (c.allRegions.has(targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' lies inside the iterated subgraph`)
  }
  const { pattern, attachments, binderStubs } = extractSubgraph(d, sel)
  // TEMPORARY (remove in plan 10a Task 4): splicing an open pattern today
  // copies the stub bubble as a FRESH quantifier instead of referencing the
  // SAME host binder — that is not the iteration rule. Refuse until splice
  // takes a binder map.
  if (binderStubs.length > 0) {
    throw new RuleError(
      `iteration of a subgraph with atoms bound outside the selection is not supported yet (open iteration lands in plan 10a Task 4)`,
    )
  }
  return spliceSubgraph(d, targetRegion, pattern, attachments)
}

/**
 * Rule 3b: remove a copy that iteration could have produced — there must be a
 * justifying occurrence of the same pattern, at an ancestor-or-equal region,
 * with identical attachments, disjoint from the copy itself. When none is
 * found but some node comparisons were undecided, the error says so (§3.7).
 */
export function applyDeiteration(d: Diagram, sel: SubgraphSelection, fuel: number): Diagram {
  const c = selectionContents(d, sel)
  const { pattern, attachments, binderStubs } = extractSubgraph(d, sel)
  // TEMPORARY (remove in plan 10a Task 4): the matcher reads stub bubbles
  // structurally, so an ISOMORPHIC occurrence under a DIFFERENT host binder
  // would justify removal — demonstrably unsound (∃S.S(x) justifying the
  // deletion of R(x) under a cut leaves an empty cut: satisfiable → false).
  // Binder justification must be by identity; refuse until the matcher takes
  // a binder map.
  if (binderStubs.length > 0) {
    throw new RuleError(
      `deiteration of a subgraph with atoms bound outside the selection is not supported yet (open deiteration lands in plan 10a Task 4)`,
    )
  }
  const { matches, undecided } = findOccurrences(d, pattern, { fuel })
  const disjoint = (m: Occurrence): boolean => {
    for (const r of m.regionMap.values()) if (c.allRegions.has(r)) return false
    for (const n of m.nodeMap.values()) if (c.allNodes.has(n)) return false
    const internal = new Set(c.internalWires)
    for (const [pw, hw] of m.wireMap) {
      if (pattern.boundary.includes(pw)) continue
      if (internal.has(hw)) return false
    }
    return true
  }
  const sameAttachments = (m: Occurrence): boolean =>
    m.attachments.length === attachments.length &&
    m.attachments.every((w, i) => w === attachments[i])
  const justifying = matches.find(
    (m) => isAncestorOrEqual(d, m.region, sel.region) && sameAttachments(m) && disjoint(m),
  )
  if (justifying === undefined) {
    const hint = undecided.length > 0
      ? `; ${undecided.length} node comparison(s) were undecided under fuel ${fuel} — a justification may exist beyond the fuel limit`
      : ''
    throw new RuleError(`no justifying occurrence found for deiteration at '${sel.region}'${hint}`)
  }
  return removeSubgraph(d, sel)
}
