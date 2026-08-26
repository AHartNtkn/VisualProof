import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { planBetaMotion, sampleBetaMotion } from '../../src/view/lambda-motion'
import * as motion from '../../src/app/interact/motion'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { singleStepAction } from '../../src/kernel/proof/action'
import { convertToWeakHeadNormal } from '../../src/app/tactics'
import { carryOver, mkEngine } from '../../src/view/engine'
import { LIGHT, paint, type Shape } from '../../src/view/paint'
import { seedProject, settle } from '../../src/view/relax'

const lambdaOutline = (shapes: readonly Shape[]): readonly unknown[] => shapes.flatMap<unknown>((shape) => {
  const rounded = (value: number): number => Number(value.toFixed(10))
  const point = ({ x, y }: { readonly x: number; readonly y: number }): object => ({
    x: rounded(x),
    y: rounded(y),
  })
  if (shape.kind === 'arc') {
    return [{
      kind: shape.kind,
      center: point(shape.center),
      radius: rounded(shape.r),
      start: rounded(shape.a0),
      end: rounded(shape.a1),
    }]
  }
  if (shape.kind === 'segment') {
    return [{ kind: shape.kind, from: point(shape.from), to: point(shape.to) }]
  }
  return []
})

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

  it('starts from an actual beta conversion and routes every lifecycle sampler into production paint', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\x. x) a')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    const beforeDiagram = builder.build()
    const conversion = convertToWeakHeadNormal(beforeDiagram, node, 8)
    const before = mkEngine(beforeDiagram, [])
    const after = mkEngine(conversion.diagram, [])
    seedProject(before)
    seedProject(after)
    let current = after
    const coordinator = new motion.MotionCoordinator({
      preferences: () => motion.defaultMotionPreferences(false),
      engine: () => current,
      theme: () => LIGHT,
    })

    coordinator.observeSwap(
      before,
      after,
      100,
      singleStepAction('beta', conversion.step),
    )
    expect(coordinator.debugState(100).beta).toEqual({ node })

    for (const sample of [
      () => coordinator.scrubBeta(0.075),
      () => coordinator.playBeta(0.54),
      () => coordinator.historyBeta(0.82),
      () => coordinator.stepBeta(),
    ]) {
      const frame = sample()
      expect(frame).not.toBeNull()
      const painted = coordinator.paint(100)
      const structural = painted.flatMap((shape) => (
        shape.kind === 'arc' || shape.kind === 'segment' ? [shape] : []
      ))
      expect(structural).toHaveLength(frame!.strokes.length)
      expect(structural.map((shape) => shape.stroke))
        .toEqual(frame!.strokes.map(({ color }) => color))
    }

    coordinator.settleBeta()
    expect(coordinator.debugState(100).beta).toBeNull()
    coordinator.observeSwap(before, after, 100, singleStepAction('beta', conversion.step))
    coordinator.cancel()
    expect(coordinator.debugState(100).beta).toBeNull()

    coordinator.observeSwap(before, after, 100, singleStepAction('beta', conversion.step))
    coordinator.paint(10_000)
    expect(coordinator.debugState(10_000).beta).toBeNull()

    current = before
    coordinator.observeSwap(
      after,
      before,
      100,
      singleStepAction('beta', conversion.step),
      'reverse',
    )
    expect(coordinator.debugState(100).beta).toEqual({ node })
    const plan = planBetaMotion(parsed.term, { kind: 'beta', path: [] })
    expect(coordinator.historyBeta(0))
      .toEqual(sampleBetaMotion(plan, 1, LIGHT.wire))
    expect(coordinator.scrubBeta(0.25))
      .toEqual(sampleBetaMotion(plan, 0.75, LIGHT.wire))
    expect(coordinator.playBeta(0.54))
      .toEqual(sampleBetaMotion(plan, 1 - 0.54, LIGHT.wire))
    expect(coordinator.historyBeta(1))
      .toEqual(sampleBetaMotion(plan, 0, LIGHT.wire))
    expect(coordinator.stepBeta())
      .toEqual(sampleBetaMotion(plan, 0, LIGHT.wire))
    const historyFrame = coordinator.historyBeta(0.54)!
    const historyPaint = coordinator.paint(100).flatMap((shape) => (
      shape.kind === 'arc' || shape.kind === 'segment' ? [shape] : []
    ))
    expect(historyPaint.map((shape) => shape.stroke))
      .toEqual(historyFrame.strokes.map(({ color }) => color))
  })

  it('paints the structural motion at the source and target body transforms at its endpoints', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\f. \\x. f (f x)) (\\z. z)')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    const beforeDiagram = builder.build()
    const conversion = convertToWeakHeadNormal(beforeDiagram, node, 8)
    const before = mkEngine(beforeDiagram, [])
    seedProject(before)
    settle(before, 4_000)
    const after = mkEngine(conversion.diagram, [])
    const carried = carryOver(before, after)
    seedProject(after, false, carried)
    settle(after, 4_000)
    const coordinator = new motion.MotionCoordinator({
      preferences: () => motion.defaultMotionPreferences(false),
      engine: () => after,
      theme: () => LIGHT,
    })
    coordinator.observeSwap(
      before,
      after,
      100,
      singleStepAction('beta', conversion.step),
    )

    coordinator.scrubBeta(0)
    expect(lambdaOutline(coordinator.paint(100)))
      .toEqual(lambdaOutline(paint(before, LIGHT)))

    coordinator.scrubBeta(1)
    expect(lambdaOutline(coordinator.paint(100)))
      .toEqual(lambdaOutline(paint(after, LIGHT)))
  })

  it('keeps incident 2D wires attached to moving Lambda interface ports', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\x. x) a')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    const beforeDiagram = builder.build()
    const conversion = convertToWeakHeadNormal(beforeDiagram, node, 8)
    const boundary: string[] = []
    const before = mkEngine(beforeDiagram, boundary)
    seedProject(before)
    settle(before, 4_000)
    const after = mkEngine(conversion.diagram, boundary)
    const carried = carryOver(before, after)
    seedProject(after, false, carried)
    settle(after, 4_000)
    const coordinator = new motion.MotionCoordinator({
      preferences: () => motion.defaultMotionPreferences(false),
      engine: () => after,
      theme: () => LIGHT,
    })
    coordinator.observeSwap(
      before,
      after,
      100,
      singleStepAction('beta', conversion.step),
    )

    for (const progress of [0, 0.34, 0.54, 0.82, 1]) {
      const frame = coordinator.scrubBeta(progress)!
      const shapes = coordinator.paint(100)
      const lambda = shapes.filter((shape) => shape.kind === 'arc' || shape.kind === 'segment')
      const endpoints = shapes.flatMap((shape) => shape.kind === 'bezierPath'
        ? [shape.cubics[0]!.a, shape.cubics.at(-1)!.b]
        : [])
      for (const role of ['free-port', 'output-line'] as const) {
        const portIndex = frame.strokes.findIndex((stroke) => stroke.role === role)
        expect(portIndex).toBeGreaterThanOrEqual(0)
        const port = lambda[portIndex]
        expect(port?.kind).toBe('segment')
        if (port?.kind !== 'segment') throw new Error(`${role} did not paint as a segment`)
        expect(Math.min(...endpoints.map(({ x, y }) => Math.hypot(x - port.to.x, y - port.to.y))))
          .toBeLessThan(1e-8)
      }
    }
  })
})
