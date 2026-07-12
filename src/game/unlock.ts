import type { CultureDefinition, PuzzleDefinition, PuzzleId } from './types'

export function meetsUnlockConditions(
  culture: Pick<CultureDefinition, 'unlocksAfter'>,
  puzzle: Pick<PuzzleDefinition, 'prerequisites'>,
  completed: ReadonlySet<PuzzleId>,
): boolean {
  return culture.unlocksAfter.every((id) => completed.has(id))
    && puzzle.prerequisites.every((id) => completed.has(id))
}
