import type { ContentCulture } from './content-loader'
import type { CompletionIndex } from './progress'
import type { PuzzlePlacement } from './types'

export function meetsUnlockConditions(
  culture: Pick<ContentCulture, 'unlocksAfter'>,
  placement: Pick<PuzzlePlacement, 'prerequisites'>,
  completed: CompletionIndex,
): boolean {
  return culture.unlocksAfter.every((id) => completed.has(id))
    && placement.prerequisites.every((id) => completed.has(id))
}
