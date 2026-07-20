import type { ContentCulture } from './content-loader'
import type { PuzzleId, PuzzlePlacement } from './types'

export function meetsUnlockConditions(
  culture: Pick<ContentCulture, 'unlocksAfter'>,
  placement: Pick<PuzzlePlacement, 'prerequisites'>,
  completed: ReadonlySet<PuzzleId>,
): boolean {
  return culture.unlocksAfter.every((id) => completed.has(id))
    && placement.prerequisites.every((id) => completed.has(id))
}
