import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofAction } from '../kernel/proof/action'
import { registerTheorem, type ProofContext } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import { blankDiagram, isBlank } from './blank'
import type { GameCatalog } from './catalog'
import { applyGameAction, startPuzzle } from './session'
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
  const priorContext = artifactTheoremContext(catalog, completed)
  let session = startPuzzle(puzzle)
  for (const [index, action] of actions.entries()) {
    const transition = applyGameAction(session, action, { context: priorContext })
    if (transition.completedNow && index !== actions.length - 1) {
      throw new Error(`completed artifact '${puzzle.id}' continues after action ${index} reached canonical blank`)
    }
    session = transition.session
  }
  if (actions.length === 0 || session.timeline.cursor !== actions.length) {
    throw new Error(`completed artifact '${puzzle.id}' has no complete action witness`)
  }
  const final = session.timeline.states[session.timeline.cursor]!
  if (!isBlank(final)) {
    throw new Error(`completed artifact '${puzzle.id}' does not reach canonical blank`)
  }
  const ownedActions = session.timeline.actions
  const checkedContext = registerTheorem(
    priorContext,
    completedArtifactTheorem(puzzle, ownedActions),
  )
  const checked = checkedContext.theorems.get(artifactTheoremName(puzzle.id))
  if (checked === undefined) throw new Error(`completed artifact '${puzzle.id}' was not registered`)
  return { puzzle: puzzle.id, actions: checked.backActions ?? [] }
}
