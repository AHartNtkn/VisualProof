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
  it('persists a repeatable disabled-ahead action across save and reload', async () => {
    const session = new TutorialSession(false)
    const completedWrites: string[] = []
    const writer = new SaveWriter('slot-a', savePort(completedWrites))

    enqueueTutorialCommit(
      writer,
      session.observe({ kind: 'nonblank-tree-duplicated' }),
    )
    await writer.flushChecked()

    expect(completedWrites).toEqual(['duplicate-nonblank'])
    const reloaded = new TutorialSession(true, completedWrites)
    expect(reloaded.completed.has('duplicate-nonblank')).toBe(true)
    expect(reloaded.currentInstruction?.milestoneId).toBe('move')
    await writer.dispose()
  })
})
