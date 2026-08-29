import { describe, expect, it } from 'vitest'
import { validateNativeSlotId } from '../../game/e2e/slot-id'

describe('native save inspection boundary', () => {
  it('rejects slot IDs outside the production filename grammar before path construction', () => {
    // Catches an assertion helper accepting path separators, traversal, or overlong file stems.
    for (const slotId of ['', '../slot', 'slot/name', 'slot.name', 'a'.repeat(65)]) {
      expect(() => validateNativeSlotId(slotId)).toThrow(/invalid slot id/i)
    }
    expect(validateNativeSlotId('Slot_01-good')).toBe('Slot_01-good')
  })
})
