import type { GameCatalog } from './catalog'
import { GameDomainError, type PuzzleDefinition, type PuzzleId } from './types'

export type GameProgress = { readonly completed: ReadonlySet<PuzzleId> }
export const emptyProgress = (): GameProgress => ({ completed: new Set() })

export function recordCompletion(progress: GameProgress, id: PuzzleId): GameProgress {
  if (progress.completed.has(id)) return progress
  return { completed: new Set([...progress.completed, id]) }
}

export function isUnlocked(catalog: GameCatalog, progress: GameProgress, id: PuzzleId): boolean {
  return catalog.puzzle(id).prerequisites.every((prerequisite) => progress.completed.has(prerequisite))
}

export function availableVellums(catalog: GameCatalog, progress: GameProgress): ReadonlySet<PuzzleId> {
  const available = new Set<PuzzleId>()
  for (const id of progress.completed) {
    let puzzle: PuzzleDefinition
    try { puzzle = catalog.puzzle(id) } catch { throw new GameDomainError(`progress names unknown puzzle '${id}'`) }
    if (puzzle.grantsVellum) available.add(id)
  }
  return available
}
