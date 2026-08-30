import type { SaveWriter } from '../src/game/save-writer'
import type { TutorialCommit } from '../src/game/tutorial'

export function enqueueTutorialCommit(
  writer: Pick<SaveWriter, 'completeTutorialMilestone'>,
  commit: TutorialCommit,
): void {
  for (const milestoneId of commit.newlyCompleted) {
    writer.completeTutorialMilestone(milestoneId)
  }
}
