import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../kernel/diagram/subgraph/splice'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { assertClosedGoal } from './blank'
import { GameDomainError, type PuzzleDefinition } from './types'

export function manifestSeal(host: Diagram, region: RegionId, puzzle: PuzzleDefinition): Diagram {
  assertClosedGoal(puzzle.goal)
  return spliceSubgraph(host, region, puzzle.goal, [])
}

export function dissolveSeal(
  host: Diagram,
  selection: SubgraphSelection,
  puzzle: PuzzleDefinition,
): Diagram {
  assertClosedGoal(puzzle.goal)
  const extraction = extractSubgraph(host, selection)
  if (extraction.attachments.length !== 0 || extraction.binderStubs.length !== 0
    || exploreForm(extraction.pattern.diagram) !== exploreForm(puzzle.goal.diagram)) {
    throw new GameDomainError(`selection is not an exact occurrence of solved seal '${puzzle.id}'`)
  }
  return removeSubgraph(host, selection)
}
