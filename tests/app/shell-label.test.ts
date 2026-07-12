import { describe, expect, it } from 'vitest'
import { theoremActionCountLabel } from '../../src/app/shell'

describe('library theorem action counts', () => {
  it('uses action terminology with correct singular and plural forms', () => {
    expect(theoremActionCountLabel(0)).toBe('0 actions')
    expect(theoremActionCountLabel(1)).toBe('1 action')
    expect(theoremActionCountLabel(2)).toBe('2 actions')
  })
})
