import { describe, expect, it } from 'vitest'
import { lensLayout } from '../../src/game/interface/lens-layout'

describe('Cursebreaker lens layout', () => {
  it.each([[1440, 900], [900, 1200], [640, 700]])(
    'keeps a centered square lens within a 16px safe edge at %s×%s',
    (width, height) => {
      const layout = lensLayout(width, height)
      expect(layout.size).toBe(Math.min(height - 32, width - 32))
      expect(layout.left).toBe((width - layout.size) / 2)
      expect(layout.top).toBe((height - layout.size) / 2)
      expect(layout.glassSize).toBeCloseTo(layout.size * 0.73)
    },
  )
})
