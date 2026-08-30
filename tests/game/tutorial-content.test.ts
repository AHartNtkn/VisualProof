import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import {
  LiveTutorialContent,
  decodeTutorialContent,
  openingTutorialContent,
} from '../../src/game/tutorial/content'

const openingRecords: unknown = JSON.parse(readFileSync(
  new URL('../../game/content/tutorial.json', import.meta.url),
  'utf8',
))

function records(): Array<Record<string, unknown>> {
  return structuredClone(openingRecords) as Array<Record<string, unknown>>
}

describe('tutorial content authority', () => {
  it('decodes the editable opening instruction for each visible semantic milestone', () => {
    // Catches authored tutorial copy that stops teaching the movement control.
    const revision = decodeTutorialContent(openingRecords)

    expect(revision.definition('move').text).toContain('W')
    expect(revision.definition('complete-blank-order').text).toMatch(/Orders > Available/i)
  })

  it('rejects a document that omits a visible tutorial milestone', () => {
    // Catches an edited document dropping a card while leaving progression intact.
    const candidate = records().filter(({ milestoneId }) => milestoneId !== 'move')

    expect(() => decodeTutorialContent(candidate)).toThrow(/missing/i)
  })

  it('rejects blank tutorial instruction text', () => {
    // Catches a successfully decoded card that presents no player guidance.
    const candidate = records()
    candidate[0]!['text'] = '   '

    expect(() => decodeTutorialContent(candidate)).toThrow(/blank/i)
  })

  it('publishes only complete decoded revisions and keeps lookup keyed by milestone ID', () => {
    // Catches live copy replacing semantic lookup or accepting an unchecked candidate.
    const live = new LiveTutorialContent(openingTutorialContent.current)
    const candidate = records()
    candidate[0]!['text'] = 'Use W/A/S/D to move through the orchard.'
    const revision = decodeTutorialContent(candidate)

    live.publish(revision)

    expect(live.current.definition('move').text).toBe('Use W/A/S/D to move through the orchard.')
    expect(() => live.current.definition('not-a-milestone')).toThrow(/unknown/i)
    expect(() => live.publish({ definitions: revision.definitions } as never)).toThrow(/decoded/i)
  })
})
