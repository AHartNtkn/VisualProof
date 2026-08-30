import { describe, expect, it } from 'vitest'
import {
  publishToolContentRevision,
  publishTutorialContentRevision,
} from '../../game/content-publication'
import {
  LiveTutorialContent,
  decodeTutorialContent,
  openingTutorialContent,
} from '../../src/game/tutorial/content'
import {
  LiveToolContent,
  decodeToolContent,
  openingToolContent,
} from '../../src/game/tools/content'

function deferred(): {
  readonly promise: Promise<void>
  resolve(): void
} {
  let resolve!: () => void
  const promise = new Promise<void>((done) => { resolve = done })
  return { promise, resolve }
}

function tutorialRevision(text: string) {
  return decodeTutorialContent(openingTutorialContent.current.definitions.map((definition) => ({
    ...definition,
    text: definition.milestoneId === 'move' ? text : definition.text,
  })))
}

function toolRevision(name: string) {
  return decodeToolContent(openingToolContent.current.definitions.map((definition) => ({
    ...definition,
    name: definition.id === 'sprout-spawner' ? name : definition.name,
  })))
}

describe('authored content publication', () => {
  // This catches live copy changing before the permanent write has succeeded.
  it('persists tutorial copy before publishing the live revision', async () => {
    const before = tutorialRevision('Before')
    const candidate = tutorialRevision('After')
    const content = new LiveTutorialContent(before)
    const events: string[] = []

    await publishTutorialContentRevision({
      candidate,
      contentClient: {
        saveTutorial: async (records) => {
          expect(records).toBe(candidate.definitions)
          events.push('persist')
        },
        saveTools: async () => {},
      },
      content: {
        publish(revision) {
          events.push('publish')
          content.publish(revision)
        },
      },
      isCurrent: () => true,
    })

    expect(events).toEqual(['persist', 'publish'])
    expect(content.current).toBe(candidate)
  })

  // This catches a rejected permanent tutorial write leaking into the running world.
  it('leaves live tutorial copy unchanged when persistence rejects', async () => {
    const before = tutorialRevision('Before')
    const candidate = tutorialRevision('After')
    const content = new LiveTutorialContent(before)

    await expect(publishTutorialContentRevision({
      candidate,
      contentClient: {
        saveTutorial: async () => { throw new Error('disk full') },
        saveTools: async () => {},
      },
      content,
      isCurrent: () => true,
    })).rejects.toThrow('disk full')

    expect(content.current).toBe(before)
  })

  // This catches tool publication using the tutorial operation or mutating live copy on failure.
  it('persists tool copy through its own operation before live publication', async () => {
    const before = toolRevision('Before')
    const candidate = toolRevision('After')
    const content = new LiveToolContent(before)
    const events: string[] = []

    await publishToolContentRevision({
      candidate,
      contentClient: {
        saveTutorial: async () => {},
        saveTools: async (records) => {
          expect(records).toBe(candidate.definitions)
          events.push('persist')
        },
      },
      content: {
        publish(revision) {
          events.push('publish')
          content.publish(revision)
        },
      },
      isCurrent: () => true,
    })

    expect(events).toEqual(['persist', 'publish'])
    expect(content.current).toBe(candidate)
  })

  // This catches a late persistent response publishing into a replacement world generation.
  it('does not publish tool copy when the world becomes stale during persistence', async () => {
    const before = toolRevision('Before')
    const candidate = toolRevision('After')
    const content = new LiveToolContent(before)
    const persistence = deferred()
    let current = true
    let saveStarted = false

    const publication = publishToolContentRevision({
      candidate,
      contentClient: {
        saveTutorial: async () => {},
        saveTools: async () => {
          saveStarted = true
          await persistence.promise
        },
      },
      content,
      isCurrent: () => current,
    })
    while (!saveStarted) await Promise.resolve()
    current = false
    persistence.resolve()

    await expect(publication).rejects.toThrow(/no longer active/i)
    expect(content.current).toBe(before)
  })

  // This catches persistence starting for a world generation already known to be stale.
  it('does not persist authored copy for an inactive world', async () => {
    let saves = 0

    await expect(publishTutorialContentRevision({
      candidate: tutorialRevision('After'),
      contentClient: {
        saveTutorial: async () => { saves += 1 },
        saveTools: async () => {},
      },
      content: new LiveTutorialContent(tutorialRevision('Before')),
      isCurrent: () => false,
    })).rejects.toThrow(/no longer active/i)

    expect(saves).toBe(0)
  })
})
