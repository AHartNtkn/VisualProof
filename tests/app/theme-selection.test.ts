import { describe, expect, it } from 'vitest'
import { defaultMotionPreferences } from '../../src/app/interact/motion'

describe('reduced-motion selection', () => {
  it('turns off transition ghosts and hover easing', () => {
    expect(defaultMotionPreferences(true)).toEqual({
      speed: 1,
      transitionGhosts: false,
      hoverEaseMs: 0,
    })
  })
})
