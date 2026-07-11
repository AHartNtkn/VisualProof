import { describe, expect, it } from 'vitest'
import { DARK, LIGHT } from '../../src/view/paint'

describe('approved painter selection language', () => {
  it('production light and dark themes own the established orange selection', () => {
    expect(LIGHT.interaction.selection).toBe('#d97706')
    expect(DARK.interaction.selection).toBe('#f59e0b')
  })
})
