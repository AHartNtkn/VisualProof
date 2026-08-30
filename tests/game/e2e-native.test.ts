import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { validateNativeSlotId } from '../../game/e2e/slot-id'

function gameDataAttributes(): ReadonlyMap<string, string> {
  const markup = readFileSync(new URL('../../game/index.html', import.meta.url), 'utf8')
  const opening = markup.match(/<main\s+([\s\S]*?)>/)?.[1]
  if (opening === undefined) throw new Error('missing game root')
  return new Map([...opening.matchAll(/data-([\w-]+)="([^"]*)"/g)].map((match) => [match[1]!, match[2]!]))
}

describe('native save inspection boundary', () => {
  it('rejects slot IDs outside the production filename grammar before path construction', () => {
    // Catches an assertion helper accepting path separators, traversal, or overlong file stems.
    for (const slotId of ['', '../slot', 'slot/name', 'slot.name', 'a'.repeat(65)]) {
      expect(() => validateNativeSlotId(slotId)).toThrow(/invalid slot id/i)
    }
    expect(validateNativeSlotId('Slot_01-good')).toBe('Slot_01-good')
  })

  it('mounts stable native-observation hooks for every composed transient authority', () => {
    // Catches a composed controller becoming opaque to the direct native progression scenarios.
    expect(Object.fromEntries(gameDataAttributes())).toMatchObject({
      'tutorials-enabled': 'false',
      'completed-tutorial-milestones': '[]',
      'acquired-tool-ids': '[]',
      'selected-tool': '',
      'selector-visible': 'false',
      'ledger-open': 'false',
      'ledger-tab': 'tools',
      'developer-mode': 'false',
      'editor-state': 'closed',
    })
  })
})
