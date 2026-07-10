import { describe, expect, it } from 'vitest'
import { DARK, LIGHT } from '../../src/view/paint'
import { AESTHETIC_THEMES } from '../../ui-lab/aesthetic-themes'

describe('approved painter selection language', () => {
  it('uses the established orange selection in Porcelain light and dark', () => {
    expect(AESTHETIC_THEMES.porcelain[0].interaction.selection).toBe(LIGHT.interaction.selection)
    expect(AESTHETIC_THEMES.porcelain[1].interaction.selection).toBe(DARK.interaction.selection)
  })
})
