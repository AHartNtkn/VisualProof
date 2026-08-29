import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { ARGUMENT_COLOR, COPY_HUES, REDEX_COLOR } from '../../src/view/lambda-motion'
import * as motion from '../../src/app/interact/motion'
import { lambdaMotionFromAction } from '../../src/view/lambda-transition'
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
  it('derives one beta motion description from the committed action, including interface shrinkage', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\x. kept) discarded')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    const before = builder.build()
    const conversion = convertToWeakHeadNormal(before, node, 8)

    const transition = lambdaMotionFromAction(
      before,
      conversion.diagram,
      singleStepAction('beta', conversion.step),
      'forward',
    )

    expect(transition).not.toBeNull()
    expect(transition?.node).toBe(node)
    expect(transition?.plan.sourceInterfaceArity).toBe(2)
    expect(transition?.plan.targetInterfaceArity).toBe(1)
    expect(transition?.plan.target).toEqual(parseTerm('kept').term)
  })

  it('clamps and rounds user-selected animation speed', () => {
    const prefs = motion.defaultMotionPreferences(false)
    motion.setMotionSpeed(prefs, 9)
    expect(prefs.speed).toBe(3)
    motion.setMotionSpeed(prefs, 0)
    expect(prefs.speed).toBe(0.25)
    motion.setMotionSpeed(prefs, 1.37)
    expect(prefs.speed).toBe(1.25)
    motion.setMotionSpeed(prefs, Number.NaN)
    expect(prefs.speed).toBe(1)
    expect(motion.smoothstep(0.5)).toBe(0.5)
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

  it('paints a committed beta action through identification, copying, completion, cancellation, and undo', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\f. \\x. f (f x)) (\\z. z)')
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
    coordinator.scrubBeta(0.149)
    const identifiedColors = coordinator.paint(100).flatMap((shape) => (
      shape.kind === 'arc' || shape.kind === 'segment' ? [shape.stroke] : []
    ))
    expect(identifiedColors).toContain(REDEX_COLOR)
    expect(identifiedColors).toContain(ARGUMENT_COLOR)

    coordinator.scrubBeta(0.54)
    const copyingColors = coordinator.paint(100).flatMap((shape) => (
      shape.kind === 'arc' || shape.kind === 'segment' ? [shape.stroke] : []
    ))
    expect(copyingColors).toContain(COPY_HUES[0])

    coordinator.scrubBeta(1)
    expect(lambdaOutline(coordinator.paint(100))).toEqual(lambdaOutline(paint(after, LIGHT)))

    coordinator.observeSwap(before, after, 100, singleStepAction('beta', conversion.step))
    coordinator.scrubBeta(0.075)
    coordinator.cancel()
    expect(lambdaOutline(coordinator.paint(100))).toEqual(lambdaOutline(paint(after, LIGHT)))

    coordinator.observeSwap(before, after, 100, singleStepAction('beta', conversion.step))
    coordinator.paint(10_000)
    expect(lambdaOutline(coordinator.paint(10_000))).toEqual(lambdaOutline(paint(after, LIGHT)))

    current = before
    coordinator.observeSwap(
      after,
      before,
      100,
      singleStepAction('beta', conversion.step),
      'reverse',
    )
    coordinator.scrubBeta(0)
    expect(lambdaOutline(coordinator.paint(100))).toEqual(lambdaOutline(paint(after, LIGHT)))
    coordinator.scrubBeta(1)
    expect(lambdaOutline(coordinator.paint(100))).toEqual(lambdaOutline(paint(before, LIGHT)))
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
