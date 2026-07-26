import { describe, expect, it } from 'vitest'
import * as motion from '../../src/app/interact/motion'

describe('generic diagram motion', () => {
  it('keeps only speed, transition ghosts, and hover timing preferences', () => {
    const prefs = motion.defaultMotionPreferences(false)
    expect(prefs).toEqual({ speed: 1, transitionGhosts: true, hoverEaseMs: 120 })
    motion.setMotionSpeed(prefs, 9)
    expect(prefs.speed).toBe(3)
    motion.setMotionSpeed(prefs, 0)
    expect(prefs.speed).toBe(0.25)
    expect(motion.smoothstep(0.5)).toBe(0.5)
    expect('conversionFrames' in motion).toBe(false)
    expect('conversionAnimation' in motion).toBe(false)
  })

  it('eases hover independently of proof semantics', () => {
    const prefs = motion.defaultMotionPreferences(false)
    const coordinator = new motion.MotionCoordinator({
      preferences: () => prefs,
      engine: () => ({ bodies: new Map(), scale: 1 }) as never,
      theme: () => ({}) as never,
    })
    coordinator.setHover('n0', 10)
    expect(coordinator.hoverFraction(70)).toBe(0.5)
    coordinator.cancel()
    expect(coordinator.hoverFraction(100)).toBe(0)
  })
})
