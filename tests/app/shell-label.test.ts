import { describe, expect, it } from 'vitest'
import { theoremActionCountLabel } from '../../src/app/shell-label'

describe('shell proof labels', () => {
  it('pluralizes structural action counts', () => {
    expect(theoremActionCountLabel(0)).toBe('0 actions')
    expect(theoremActionCountLabel(1)).toBe('1 action')
    expect(theoremActionCountLabel(2)).toBe('2 actions')
  })
})
