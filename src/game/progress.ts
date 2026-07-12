import type { GameCatalog } from './catalog'
import {
  GameDomainError, type CultureId, type PuzzleDefinition, type PuzzleId,
} from './types'

export type GameProgress = { readonly completed: ReadonlySet<PuzzleId> }
export const emptyProgress = (): GameProgress => ({ completed: new Set() })

export function recordCompletion(progress: GameProgress, id: PuzzleId): GameProgress {
  if (progress.completed.has(id)) return progress
  return { completed: new Set([...progress.completed, id]) }
}

export function isCultureUnlocked(
  catalog: GameCatalog,
  progress: GameProgress,
  id: CultureId,
): boolean {
  return catalog.culture(id).unlocksAfter.every((puzzle) => progress.completed.has(puzzle))
}

export function isUnlocked(catalog: GameCatalog, progress: GameProgress, id: PuzzleId): boolean {
  const puzzle = catalog.puzzle(id)
  return isCultureUnlocked(catalog, progress, puzzle.culture)
    && puzzle.prerequisites.every((prerequisite) => progress.completed.has(prerequisite))
}

export function requiredPuzzles(catalog: GameCatalog): ReadonlySet<PuzzleId> {
  const required = new Set<PuzzleId>()
  const add = (id: PuzzleId): void => {
    if (required.has(id)) return
    required.add(id)
    for (const prerequisite of catalog.puzzle(id).prerequisites) add(prerequisite)
  }
  for (const culture of catalog.source.cultures) {
    add(culture.gateway)
    for (const gate of culture.unlocksAfter) add(gate)
  }
  return required
}

export const isRequired = (catalog: GameCatalog, id: PuzzleId): boolean =>
  requiredPuzzles(catalog).has(id)

export function availableVellums(catalog: GameCatalog, progress: GameProgress): ReadonlySet<PuzzleId> {
  const available = new Set<PuzzleId>()
  for (const id of progress.completed) {
    let puzzle: PuzzleDefinition
    try { puzzle = catalog.puzzle(id) } catch { throw new GameDomainError(`progress names unknown puzzle '${id}'`) }
    if (puzzle.grantsVellum) available.add(id)
  }
  return available
}
