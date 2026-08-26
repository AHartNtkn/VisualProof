import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { planBetaMotion, sampleBetaMotion } from '../../src/view/lambda-motion'
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

  it('samples one structural beta plan for scrub, play, step, and history motion', () => {
    const source = parseTerm('(\\f. \\x. f (f x)) (\\z. z)').term
    const step = { kind: 'beta', path: [] } as const
    const baseColor = '#26343a'
    const coordinator = new motion.MotionCoordinator({
      preferences: () => motion.defaultMotionPreferences(false),
      engine: () => ({ bodies: new Map(), scale: 1 }) as never,
      theme: () => ({}) as never,
    })
    const plan = coordinator.beginBeta(source, step, baseColor)
    expect(plan).toEqual(planBetaMotion(source, step))

    const expected = sampleBetaMotion(plan, 0.54, baseColor)
    expect(coordinator.scrubBeta(0.54)).toEqual(expected)
    expect(coordinator.playBeta(0.54)).toEqual(expected)
    expect(coordinator.historyBeta(0.54)).toEqual(expected)
    expect(coordinator.stepBeta()).toEqual(sampleBetaMotion(plan, 1, baseColor))

    coordinator.cancel()
    expect(coordinator.scrubBeta(0.54)).toBeNull()
    expect(coordinator.playBeta(0.54)).toBeNull()
    expect(coordinator.historyBeta(0.54)).toBeNull()
    expect(coordinator.stepBeta()).toBeNull()
  })
})
