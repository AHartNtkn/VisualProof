import type { GameCatalog } from './catalog'
import { type CultureId, type PuzzleId } from './types'
import { meetsUnlockConditions } from './unlock'

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
  const placement = catalog.placement(id)
  return meetsUnlockConditions(catalog.culture(placement.culture), placement, progress.completed)
}

export function requiredPuzzles(catalog: GameCatalog): ReadonlySet<PuzzleId> {
  const required = new Set<PuzzleId>()
  const add = (id: PuzzleId): void => {
    if (required.has(id)) return
    required.add(id)
    for (const prerequisite of catalog.placement(id).prerequisites) add(prerequisite)
  }
  for (const id of catalog.cultureIds) {
    const culture = catalog.culture(id)
    add(culture.gateway)
    for (const gate of culture.unlocksAfter) add(gate)
  }
  return required
}

export const isRequired = (catalog: GameCatalog, id: PuzzleId): boolean =>
  requiredPuzzles(catalog).has(id)
