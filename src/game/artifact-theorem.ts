import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofAction } from '../kernel/proof/action'
import { registerTheorem, type ProofContext } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import { blankDiagram } from './blank'
import type { GameCatalog } from './catalog'
import { type CompletedArtifact, type PuzzleDefinition, type PuzzleId } from './types'

const ARTIFACT_THEOREM_NAMESPACE = 'game:artifact:'

export const artifactTheoremName = (id: PuzzleId): string =>
  `${ARTIFACT_THEOREM_NAMESPACE}${id}`

export function completedArtifactTheorem(
  puzzle: PuzzleDefinition,
  backActions: readonly ProofAction[],
): Theorem {
  return {
    name: artifactTheoremName(puzzle.id),
    lhs: mkDiagramWithBoundary(blankDiagram(), []),
    rhs: mkDiagramWithBoundary(puzzle.diagram, []),
    actions: [],
    backActions,
  }
}

export function artifactTheoremContext(
  catalog: Pick<GameCatalog, 'puzzle' | 'context'>,
  completed: ReadonlyMap<PuzzleId, CompletedArtifact>,
): ProofContext {
  let context = catalog.context
  for (const [id, artifact] of completed) {
    if (artifact.puzzle !== id) {
      throw new Error(`completed artifact key '${id}' does not match '${artifact.puzzle}'`)
    }
    context = registerTheorem(
      context,
      completedArtifactTheorem(catalog.puzzle(id), artifact.actions),
    )
  }
  return context
}

export function certifyCompletedArtifact(
  catalog: Pick<GameCatalog, 'puzzle' | 'context'>,
  completed: ReadonlyMap<PuzzleId, CompletedArtifact>,
  puzzle: PuzzleDefinition,
  actions: readonly ProofAction[],
): CompletedArtifact {
  if (completed.has(puzzle.id)) throw new Error(`puzzle '${puzzle.id}' is already completed`)
  const checkedContext = registerTheorem(
    artifactTheoremContext(catalog, completed),
    completedArtifactTheorem(puzzle, actions),
  )
  const checked = checkedContext.theorems.get(artifactTheoremName(puzzle.id))
  if (checked === undefined) throw new Error(`completed artifact '${puzzle.id}' was not registered`)
  return { puzzle: puzzle.id, actions: checked.backActions ?? [] }
}
