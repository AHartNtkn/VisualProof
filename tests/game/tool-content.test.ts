import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import {
  LiveToolContent,
  decodeToolContent,
  openingToolContent,
} from '../../src/game/tools/content'

const openingRecords: unknown = JSON.parse(readFileSync(
  new URL('../../game/content/tools.json', import.meta.url),
  'utf8',
))

function records(): Array<Record<string, unknown>> {
  return structuredClone(openingRecords) as Array<Record<string, unknown>>
}

describe('tool content authority', () => {
  it('decodes the editable description for each visible tool ID', () => {
    // Catches authored tool copy that no longer tells a player how to use Iteration.
    const revision = decodeToolContent(openingRecords)

    expect(revision.definition('iteration').description).toMatch(/right-click/i)
    expect(revision.definition('sprout-spawner').name).toBeTruthy()
  })

  it('rejects a document whose semantic tool IDs change', () => {
    // Catches content edits changing the stable mechanics identifier.
    const candidate = records()
    candidate[0]!['id'] = 'renamed-tool'

    expect(() => decodeToolContent(candidate)).toThrow(/unknown|missing/i)
  })

  it('rejects blank tool descriptions', () => {
    // Catches an editable tool record that gives no usage guidance.
    const candidate = records()
    candidate[0]!['description'] = ''

    expect(() => decodeToolContent(candidate)).toThrow(/blank/i)
  })

  it('publishes only complete decoded revisions and keeps lookup keyed by tool ID', () => {
    // Catches live content overwriting mechanics identity or accepting an unchecked candidate.
    const live = new LiveToolContent(openingToolContent.current)
    const candidate = records()
    candidate[2]!['name'] = 'Branch Copier'
    const revision = decodeToolContent(candidate)

    live.publish(revision)

    expect(live.current.definition('iteration').name).toBe('Branch Copier')
    expect(() => live.current.definition('not-a-tool')).toThrow(/unknown/i)
    expect(() => live.publish({ definitions: revision.definitions } as never)).toThrow(/decoded/i)
  })
})
