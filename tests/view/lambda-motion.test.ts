import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyStepAt, type ReductionStep } from '../../src/kernel/term/reduce'
import { termEq, type Term } from '../../src/kernel/term/term'
import {
  ARGUMENT_COLOR,
  COPY_HUES,
  REDEX_COLOR,
  planBetaMotion,
  sampleBetaMotion,
  type LambdaStroke,
  type LambdaStrokeFrame,
} from '../../src/view/lambda-motion'
import { lambdaFrameGeometry } from '../../src/view/morph'
import { paintLambdaFrame } from '../../src/view/paint'
import { termGeometry, type NodeGeometry } from '../../src/view/bend'

const ROOT_BETA: ReductionStep = { kind: 'beta', path: [] }
const BASE = '#26343a'
const IDENTIFY = 0.149
const DUPLICATE = 0.34
const MAKE_SPACE = 0.44
const DOCK = 0.82
const CLEANUP = 0.965

const term = (source: string): Term => parseTerm(source).term

const cases = [
  { name: 'one use', source: '(\\x. x) a', target: 'a' },
  { name: 'duplication', source: '(\\f. \\x. f (f x)) (\\z. z)', target: '\\x. (\\z. z) ((\\z. z) x)' },
  { name: 'deletion', source: '(\\x. kept) ((\\z. z) discarded)', target: 'kept' },
  { name: 'nested binders', source: '(\\x. \\y. x y) (\\w. w)', target: '\\y. (\\w. w) y' },
  { name: 'capture avoidance', source: '(\\x. \\y. x) y', target: '\\z. y' },
] as const

const strokesWithColor = (frame: LambdaStrokeFrame, color: string): LambdaStroke[] => (
  frame.strokes.filter((stroke) => stroke.color === color)
)

const coloredCopies = (frame: LambdaStrokeFrame): LambdaStroke[] => (
  frame.strokes.filter((stroke) => COPY_HUES.includes(stroke.color as typeof COPY_HUES[number]))
)

const centerOf = (strokes: readonly LambdaStroke[]): { readonly x: number; readonly y: number } => {
  const points = strokes.flatMap(({ points }) => points)
  return {
    x: points.reduce((sum, point) => sum + point.x, 0) / points.length,
    y: points.reduce((sum, point) => sum + point.y, 0) / points.length,
  }
}

const clean = (value: number): number => Number(value.toFixed(10))
const cleanAngle = (value: number): number => clean((value % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI))
const paintGeometry = (geometry: NodeGeometry): unknown => ({
  outerRadius: clean(geometry.outerRadius),
  arcs: geometry.arcs.map(({ r, a0, a1, kind }) => ({ r: clean(r), a0: cleanAngle(a0), a1: cleanAngle(a1), kind })),
  radials: geometry.radials.map(({ angle, r0, r1 }) => ({ angle: cleanAngle(angle), r0: clean(r0), r1: clean(r1) })),
  portAnchors: Object.fromEntries(Object.entries(geometry.portAnchors)
    .map(([key, { x, y }]) => [key, { x: clean(x), y: clean(y) }])),
  exitArc: geometry.exitArc === null ? null : {
    r: clean(geometry.exitArc.r),
    a0: cleanAngle(geometry.exitArc.a0),
    a1: cleanAngle(geometry.exitArc.a1),
  },
  exitLine: geometry.exitLine?.map(({ x, y }) => ({ x: clean(x), y: clean(y) })) ?? null,
})

describe('corrected structural beta motion', () => {
  for (const fixture of cases) {
    it(`${fixture.name}: presents the checked reduction and reaches ordinary target geometry`, () => {
      const parsed = parseTerm(fixture.source)
      const plan = planBetaMotion(parsed.term, ROOT_BETA, parsed.freeIdentifiers.length)

      expect(termEq(plan.target, term(fixture.target))).toBe(true)
      expect(termEq(plan.target, applyStepAt(parsed.term, ROOT_BETA))).toBe(true)
      expect(new Set(sampleBetaMotion(plan, 0, BASE).strokes.map(({ color }) => color)))
        .toEqual(new Set([BASE]))
      expect(strokesWithColor(sampleBetaMotion(plan, IDENTIFY, BASE), REDEX_COLOR).length)
        .toBeGreaterThan(0)
      expect(paintGeometry(lambdaFrameGeometry(sampleBetaMotion(plan, 1, BASE))))
        .toEqual(paintGeometry(termGeometry(plan.target, plan.targetInterfaceArity)))
      expect(new Set(sampleBetaMotion(plan, 1, BASE).strokes.map(({ color }) => color)))
        .toEqual(new Set([BASE]))
    })
  }

  it('duplicates the complete argument into separated, consistently colored copies before docking', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const identifiedArgumentCount = strokesWithColor(
      sampleBetaMotion(plan, IDENTIFY, BASE),
      ARGUMENT_COLOR,
    ).length
    expect(identifiedArgumentCount).toBeGreaterThan(0)

    for (const progress of [DUPLICATE, MAKE_SPACE, DOCK]) {
      const frame = sampleBetaMotion(plan, progress, BASE)
      expect(strokesWithColor(frame, COPY_HUES[0]), `first copy at ${progress}`).toHaveLength(identifiedArgumentCount)
      expect(strokesWithColor(frame, COPY_HUES[1]), `second copy at ${progress}`).toHaveLength(identifiedArgumentCount)
    }

    const spaced = sampleBetaMotion(plan, MAKE_SPACE, BASE)
    const firstCenter = centerOf(strokesWithColor(spaced, COPY_HUES[0]))
    const secondCenter = centerOf(strokesWithColor(spaced, COPY_HUES[1]))
    expect(Math.hypot(firstCenter.x - secondCenter.x, firstCenter.y - secondCenter.y))
      .toBeGreaterThan(0.01)
  })

  it('docks copied geometry onto visible sockets and then clears the sockets', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const docking = sampleBetaMotion(plan, DOCK, BASE)
    expect(docking.sockets.some(({ amount }) => amount > 0)).toBe(true)
    const copyEndpoints = coloredCopies(docking).flatMap(({ points }) => points)
    for (const socket of docking.sockets.filter(({ amount }) => amount > 0)) {
      expect(copyEndpoints.some((point) => (
        Math.hypot(point.x - socket.point.x, point.y - socket.point.y) < 1e-9
      ))).toBe(true)
    }
    expect(sampleBetaMotion(plan, CLEANUP, BASE).sockets.every(({ amount }) => amount === 0))
      .toBe(true)
  })

  it('contracts a discarded argument without producing a colored copy', () => {
    const plan = planBetaMotion(term(cases[2].source), ROOT_BETA)
    expect(strokesWithColor(sampleBetaMotion(plan, IDENTIFY, BASE), ARGUMENT_COLOR).length)
      .toBeGreaterThan(0)
    const contracting = sampleBetaMotion(plan, 0.51, BASE)
    expect(strokesWithColor(contracting, ARGUMENT_COLOR)).toEqual([])
    expect(coloredCopies(contracting)).toEqual([])
  })

  it('renders copied lambda bars as nonzero circular strokes in 2D', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const frame = sampleBetaMotion(plan, MAKE_SPACE, BASE)
    const copyBars = coloredCopies(frame).filter(({ role }) => role === 'lambda')
    expect(copyBars).toHaveLength(2)
    for (const bar of copyBars) {
      expect(bar.geometry.kind).toBe('arc')
      if (bar.geometry.kind !== 'arc') throw new Error('copy lambda bar is not circular')
      expect(bar.geometry.a1).toBeGreaterThan(bar.geometry.a0)
      expect(bar.geometry.r * (bar.geometry.a1 - bar.geometry.a0)).toBeGreaterThan(2)
    }

    const painted = paintLambdaFrame(frame, { x: 0, y: 0 }, 0, 1, 3, false)
    expect(painted.filter((shape) => (
      shape.kind === 'arc' && COPY_HUES.includes(shape.stroke as typeof COPY_HUES[number])
    ))).toHaveLength(2)
  })

  it('colors the consumed binder and argument during identification', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const frame = sampleBetaMotion(plan, IDENTIFY, BASE)
    expect(frame.strokes.some(({ role, subtermPath, color }) => (
      role === 'lambda' && subtermPath.length === 1 && subtermPath[0] === 'fn' && color === REDEX_COLOR
    ))).toBe(true)
    expect(strokesWithColor(frame, ARGUMENT_COLOR).length).toBeGreaterThan(0)
  })

  it('uses all five copy hues and repeats the palette for later copies', () => {
    const plan = planBetaMotion(term('(\\x. x x x x x x) (\\z. z)'), ROOT_BETA)
    const frame = sampleBetaMotion(plan, MAKE_SPACE, BASE)
    const counts = COPY_HUES.map((color) => strokesWithColor(frame, color).length)
    expect(counts.every((count) => count > 0)).toBe(true)
    expect(counts[0]).toBe(2 * counts[1]!)
    expect(new Set(counts.slice(1))).toEqual(new Set([counts[1]]))
  })

  it('feeds circular geometry and stage colors into the 2D painter', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const frame = sampleBetaMotion(plan, MAKE_SPACE, BASE)
    const geometry = lambdaFrameGeometry(frame)
    expect(geometry.arcs.length).toBeGreaterThan(0)
    expect(geometry.radials.length).toBeGreaterThan(0)
    expect(geometry.exitArc).not.toBeNull()
    expect(geometry.exitLine).not.toBeNull()

    const shapes = paintLambdaFrame(frame, { x: 10, y: 20 }, Math.PI / 3, 2, 3, false)
    const paintedColors = shapes.flatMap((shape) => (
      shape.kind === 'arc' || shape.kind === 'segment' ? [shape.stroke] : []
    ))
    expect(paintedColors).toEqual(frame.strokes.map(({ color }) => color))
  })

  it('rejects eta steps and paths that do not select a beta redex', () => {
    expect(() => planBetaMotion(term('\\x. x'), { kind: 'eta', path: [] })).toThrow(/beta/i)
    expect(() => planBetaMotion(term('a b'), ROOT_BETA)).toThrow(/beta redex/i)
  })
})
