import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import { checkTheorem, type Theorem } from '../kernel/proof/theorem'
import { blankDiagram } from './blank'
import {
  GameDomainError,
  type GameRuleContext,
  type PuzzleDefinition,
  type PuzzleId,
} from './types'

const ARTIFACT_THEOREM_NAMESPACE = 'game:artifact:'

export const artifactTheoremName = (id: PuzzleId): string =>
  `${ARTIFACT_THEOREM_NAMESPACE}${id}`

export function artifactTheorem(
  puzzle: PuzzleDefinition,
  context: ProofContext,
): Theorem {
  const theorem: Theorem = {
    name: artifactTheoremName(puzzle.id),
    lhs: mkDiagramWithBoundary(blankDiagram(), []),
    rhs: puzzle.goal,
    steps: [],
    backSteps: puzzle.witness,
  }
  checkTheorem(theorem, context)
  return theorem
}

export function artifactTheoremContext(
  puzzles: readonly PuzzleDefinition[],
  completed: ReadonlySet<PuzzleId>,
  context: GameRuleContext,
): ProofContext {
  const byId = new Map(puzzles.map((puzzle) => [puzzle.id, puzzle] as const))
  const theorems = new Map<string, Theorem>()
  const building = new Set<PuzzleId>()

  const add = (id: PuzzleId): void => {
    if (!completed.has(id) || theorems.has(artifactTheoremName(id))) return
    const puzzle = byId.get(id)
    if (puzzle === undefined) {
      throw new GameDomainError(`completed artifacts name unknown puzzle '${id}'`)
    }
    if (building.has(id)) {
      throw new GameDomainError(`completed artifact theorem dependency cycle includes '${id}'`)
    }
    building.add(id)
    for (const prerequisite of puzzle.prerequisites) add(prerequisite)
    const theoremContext: ProofContext = { relations: context.relations, theorems }
    const theorem = artifactTheorem(puzzle, theoremContext)
    theorems.set(theorem.name, theorem)
    building.delete(id)
  }

  for (const id of [...completed].sort()) add(id)
  return { relations: context.relations, theorems }
}
