import type { AuthoredContentClient } from '../src/game/content-client'
import type {
  LiveTutorialContent,
  TutorialContentRevision,
} from '../src/game/tutorial/content'
import type {
  LiveToolContent,
  ToolContentRevision,
} from '../src/game/tools/content'

function assertCurrent(isCurrent: () => boolean): void {
  if (!isCurrent()) throw new Error('loaded world is no longer active')
}

export async function publishTutorialContentRevision(config: {
  readonly candidate: TutorialContentRevision
  readonly contentClient: AuthoredContentClient
  readonly content: Pick<LiveTutorialContent, 'publish'>
  readonly isCurrent: () => boolean
}): Promise<void> {
  assertCurrent(config.isCurrent)
  await config.contentClient.saveTutorial(config.candidate.definitions)
  if (!config.isCurrent()) return
  config.content.publish(config.candidate)
}

export async function publishToolContentRevision(config: {
  readonly candidate: ToolContentRevision
  readonly contentClient: AuthoredContentClient
  readonly content: Pick<LiveToolContent, 'publish'>
  readonly isCurrent: () => boolean
}): Promise<void> {
  assertCurrent(config.isCurrent)
  await config.contentClient.saveTools(config.candidate.definitions)
  if (!config.isCurrent()) return
  config.content.publish(config.candidate)
}
