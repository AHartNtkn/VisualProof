import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { blankDiagram } from './blank'
import type { GameCatalog } from './catalog'
import { type PuzzleDefinition, type PuzzleId } from './types'

const ARTIFACT_THEOREM_NAMESPACE = 'game:artifact:'

export const artifactTheoremName = (id: PuzzleId): string =>
  `${ARTIFACT_THEOREM_NAMESPACE}${id}`

export function completedArtifactTheorem(puzzle: PuzzleDefinition): Theorem {
  return {
    name: artifactTheoremName(puzzle.id),
    lhs: mkDiagramWithBoundary(blankDiagram(), []),
    rhs: mkDiagramWithBoundary(puzzle.diagram, []),
    steps: [],
    backSteps: [],
  }
}

export function artifactTheoremContext(
  catalog: Pick<GameCatalog, 'puzzle' | 'context'>,
  completed: ReadonlySet<PuzzleId>,
): ProofContext {
  const theorems = new Map<string, Theorem>()
  for (const id of [...completed].sort()) {
    const theorem = completedArtifactTheorem(catalog.puzzle(id))
    theorems.set(theorem.name, theorem)
  }
  return { relations: catalog.context.relations, theorems }
}
