import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyConversion } from '../../src/kernel/rules/conversion'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import {
  MotionCoordinator,
  conversionFrames,
  defaultMotionPreferences,
  setMotionSpeed,
  smoothstep,
} from '../../src/app/interact/motion'

const fixture = () => {
  const builder = new DiagramBuilder()
  const node = builder.termNode(builder.root, parseTerm('(\\x. x) y'))
  const diagram = builder.build()
  const converted = applyConversion(diagram, node, parseTerm('s0'), 32)
  const step = { rule: 'conversion' as const, node, term: parseTerm('s0'), certificate: converted.certificate, attachments: {} }
  return { diagram, node, step }
}

describe('motion preferences and conversion frames', () => {
  it('initializes normal and reduced preferences independently', () => {
    expect(defaultMotionPreferences(false)).toEqual({
      conversionAnimation: true,
      connectedMorph: true,
      speed: 1,
      transitionGhosts: true,
      hoverEaseMs: 120,
    })
    expect(defaultMotionPreferences(true)).toEqual({
      conversionAnimation: false,
      connectedMorph: true,
      speed: 1,
      transitionGhosts: false,
      hoverEaseMs: 0,
    })
  })

  it('clamps speed and preserves the other independent choices', () => {
    const preferences = defaultMotionPreferences(false)
    preferences.connectedMorph = false
    setMotionSpeed(preferences, 99)
    expect(preferences.speed).toBe(3)
    expect(preferences.connectedMorph).toBe(false)
    setMotionSpeed(preferences, 0)
    expect(preferences.speed).toBe(0.25)
  })

  it('derives source through common reduct to target and uses C1 easing', () => {
    const { diagram, step } = fixture()
    expect(conversionFrames(diagram, step).map((term) => JSON.stringify(term))).toEqual([
      JSON.stringify(parseTerm('(\\x. x) s0')),
      JSON.stringify(parseTerm('s0')),
    ])
    expect(smoothstep(0)).toBe(0)
    expect(smoothstep(0.5)).toBe(0.5)
    expect(smoothstep(1)).toBe(1)
  })
})

describe('motion coordinator', () => {
  it('defers conversion, samples geometry, and commits exactly once at the endpoint', () => {
    const { diagram, node, step } = fixture()
    const preferences = defaultMotionPreferences(false)
    const engine = mkEngine(diagram, [])
    let commits = 0
    const coordinator = new MotionCoordinator({
      preferences: () => preferences,
      diagram: () => diagram,
      engine: () => engine,
      theme: () => LIGHT,
    })
    const before = engine.bodies.get(node)!.geometry
    expect(coordinator.run(step, () => { commits++ }, 100)).toBe(true)
    expect(coordinator.playing).toBe(true)
    expect(commits).toBe(0)

    coordinator.frame(360)
    expect(engine.bodies.get(node)!.geometry).not.toBe(before)
    expect(commits).toBe(0)
    coordinator.frame(620)
    expect(commits).toBe(1)
    expect(coordinator.playing).toBe(false)
    coordinator.frame(1000)
    expect(commits).toBe(1)
  })

  it('commits immediately when disabled and cancels without commit', () => {
    const { diagram, step } = fixture()
    const preferences = defaultMotionPreferences(false)
    const engine = mkEngine(diagram, [])
    let commits = 0
    const coordinator = new MotionCoordinator({ preferences: () => preferences, diagram: () => diagram, engine: () => engine, theme: () => LIGHT })
    preferences.conversionAnimation = false
    expect(coordinator.run(step, () => { commits++ }, 0)).toBe(false)
    expect(commits).toBe(1)
    preferences.conversionAnimation = true
    coordinator.run(step, () => { commits++ }, 0)
    coordinator.cancel()
    coordinator.frame(1000)
    expect(commits).toBe(1)
  })

  it('keeps ghosts and pulses paint-only and expires them at approved lifetimes', () => {
    const first = new DiagramBuilder()
    const removed = first.termNode(first.root, parseTerm('a'))
    const beforeDiagram = first.build()
    const afterDiagram = new DiagramBuilder().build()
    const before = mkEngine(beforeDiagram, [])
    const after = mkEngine(afterDiagram, [])
    const beforeDiagramValue = JSON.stringify(beforeDiagram)
    const afterDiagramValue = JSON.stringify(afterDiagram)
    let current = after
    const preferences = defaultMotionPreferences(false)
    const coordinator = new MotionCoordinator({ preferences: () => preferences, diagram: () => afterDiagram, engine: () => current, theme: () => LIGHT })
    const beforeKeys = [...before.bodies.keys()]
    const afterKeys = [...after.bodies.keys()]
    coordinator.observeSwap(before, after, 100)
    current = before
    coordinator.observeSwap(after, before, 100)
    expect(coordinator.overlays(101).length).toBeGreaterThan(0)
    expect([...before.bodies.keys()]).toEqual(beforeKeys)
    expect([...after.bodies.keys()]).toEqual(afterKeys)
    expect(JSON.stringify(beforeDiagram)).toBe(beforeDiagramValue)
    expect(JSON.stringify(afterDiagram)).toBe(afterDiagramValue)
    expect(before.bodies.has(removed)).toBe(true)
    expect(coordinator.overlays(551)).toEqual([])
  })

  it('eases hover over 120ms or applies it immediately', () => {
    const { diagram } = fixture()
    const preferences = defaultMotionPreferences(false)
    const engine = mkEngine(diagram, [])
    const coordinator = new MotionCoordinator({ preferences: () => preferences, diagram: () => diagram, engine: () => engine, theme: () => LIGHT })
    coordinator.setHover('node:n0', 10)
    expect(coordinator.hoverFraction(10)).toBe(0)
    expect(coordinator.hoverFraction(70)).toBe(0.5)
    expect(coordinator.hoverFraction(130)).toBe(1)
    preferences.hoverEaseMs = 0
    coordinator.setHover('node:n1', 200)
    expect(coordinator.hoverFraction(200)).toBe(1)
  })
})
