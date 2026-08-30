import { describe, expect, it } from 'vitest'
import { enqueueTutorialCommit } from '../../game/tutorial-progression'
import { SaveWriter } from '../../src/game/save-writer'
import { TutorialSession } from '../../src/game/tutorial'

function savePort(completed: string[]) {
  return {
    updateTree: async () => 1,
    insertTree: async () => 1,
    updateCamera: async () => {},
    acceptOrder: async () => {},
    abandonOrder: async () => {},
    completeOrder: async () => 1,
    setTutorialsEnabled: async () => {},
    completeTutorialMilestone: async (_slotId: string, milestoneId: string) => {
      completed.push(milestoneId)
    },
    acquireTool: async () => {},
  }
}

describe('tutorial progression persistence', () => {
  it('persists a reconstructed acquisition when its prerequisite later completes', async () => {
    // Catches reconstruction completing in memory without entering the active save writer.
    const completedBeforeSpawn = [
      'move',
      'look',
      'ascend',
      'descend',
      'sprint',
      'select-tree',
      'move-orbit',
      'exit-orbit',
    ] as const
    const session = new TutorialSession(false, completedBeforeSpawn)
    session.reconcileDurableProgress({
      acquiredToolIds: new Set(['sprout-spawner', 'double-cut']),
      orders: new Map(),
    })
    const completedWrites: string[] = []
    const writer = new SaveWriter('slot-a', savePort(completedWrites))

    enqueueTutorialCommit(
      writer,
      session.observe({ kind: 'sprout-spawned', blankTreeCount: 3 }),
    )
    await writer.flushChecked()

    expect(completedWrites).toEqual(['spawn-two-sprouts', 'acquire-double-cut'])
    await writer.dispose()
  })
})
