import { describe, expect, it, vi } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyStepAt, type ReductionStep } from '../../src/kernel/term/reduce'
import { termEq, type Term } from '../../src/kernel/term/term'
import {
  ARGUMENT_COLOR,
  COPY_HUES,
  REDEX_COLOR,
  planBetaMotion,
  sampleBetaMotion,
  type LambdaMotionPlan,
  type LambdaPhase,
  type LambdaStroke,
} from '../../src/view/lambda-motion'
import { lambdaFrameGeometry } from '../../src/view/morph'
import { paintLambdaFrame } from '../../src/view/paint'

const ROOT_BETA: ReductionStep = { kind: 'beta', path: [] }
const BASE = '#26343a'
const EPSILON = 1e-6

const term = (source: string): Term => parseTerm(source).term

const cases = [
  { name: 'one use', source: '(\\x. x) a', target: 'a', copies: 1 },
  { name: 'duplication', source: '(\\f. \\x. f (f x)) (\\z. z)', target: '\\x. (\\z. z) ((\\z. z) x)', copies: 2 },
  { name: 'deletion', source: '(\\x. kept) ((\\z. z) discarded)', target: 'kept', copies: 0 },
  { name: 'nested binders', source: '(\\x. \\y. x y) (\\w. w)', target: '\\y. (\\w. w) y', copies: 1 },
  { name: 'capture avoidance', source: '(\\x. \\y. x) y', target: '\\z. y', copies: 1 },
] as const

const expectedPhases = (copyCount: number): readonly (readonly [number, LambdaPhase])[] => (
  copyCount > 0
    ? [
        [0, 'identify'],
        [0.15 - EPSILON, 'identify'], [0.15, 'duplicate'],
        [0.34 - EPSILON, 'duplicate'], [0.34, 'make-space'],
        [0.54 - EPSILON, 'make-space'], [0.54, 'substitute'],
        [0.82 - EPSILON, 'substitute'], [0.82, 'cleanup'],
        [0.965 - EPSILON, 'cleanup'], [0.965, 'settle'],
        [1, 'settle'],
      ]
    : [
        [0, 'identify'],
        [0.15 - EPSILON, 'identify'], [0.15, 'discard'],
        [0.38 - EPSILON, 'discard'], [0.38, 'make-space'],
        [0.64 - EPSILON, 'make-space'], [0.64, 'cleanup'],
        [0.93 - EPSILON, 'cleanup'], [0.93, 'settle'],
        [1, 'settle'],
      ]
)

const origins = (strokes: readonly LambdaStroke[]): string[] => (
  [...new Set(strokes.map((stroke) => stroke.originId))].sort()
)

const copiesAt = (plan: LambdaMotionPlan, progress: number): Map<number, LambdaStroke[]> => {
  const copies = new Map<number, LambdaStroke[]>()
  for (const stroke of sampleBetaMotion(plan, progress, BASE).strokes) {
    if (stroke.copyIndex === null) continue
    const group = copies.get(stroke.copyIndex) ?? []
    group.push(stroke)
    copies.set(stroke.copyIndex, group)
  }
  return copies
}

const endpointPositions = (strokes: readonly LambdaStroke[]): Map<string, { x: number; y: number }> => {
  const points = new Map<string, { x: number; y: number }>()
  for (const stroke of strokes) {
    for (const point of stroke.points) {
      const existing = points.get(point.junction)
      if (existing !== undefined) {
        expect(point.x).toBeCloseTo(existing.x, 10)
        expect(point.y).toBeCloseTo(existing.y, 10)
      } else {
        points.set(point.junction, point)
      }
    }
  }
  return points
}

const colorsOf = (frame: ReturnType<typeof sampleBetaMotion>, lineage: LambdaStroke['lineage']): Set<string> => (
  new Set(frame.strokes.filter((stroke) => stroke.lineage === lineage).map((stroke) => stroke.color))
)

describe('corrected structural beta motion', () => {
  for (const fixture of cases) {
    it(`${fixture.name}: uses the corrected stages and reaches the capture-avoiding target`, () => {
      const source = term(fixture.source)
      const plan = planBetaMotion(source, ROOT_BETA)

      expect(plan.copyCount).toBe(fixture.copies)
      expect(termEq(plan.target, term(fixture.target))).toBe(true)
      expect(termEq(plan.target, applyStepAt(source, ROOT_BETA))).toBe(true)
      for (const [progress, phase] of expectedPhases(fixture.copies)) {
        expect(sampleBetaMotion(plan, progress, BASE).phase, `phase at ${progress}`).toBe(phase)
      }
    })

    it(`${fixture.name}: preserves hue identity immediately before and after every boundary`, () => {
      const plan = planBetaMotion(term(fixture.source), ROOT_BETA)
      const boundaries = [
        plan.times.split,
        plan.times.liftEnd,
        plan.times.spaceEnd,
        ...(plan.times.dockEnd === plan.times.spaceEnd ? [] : [plan.times.dockEnd]),
        ...(plan.times.stemEnd === plan.times.dockEnd ? [] : [plan.times.stemEnd]),
        plan.times.barEnd,
      ]
      for (const boundary of boundaries) {
        for (const progress of [boundary - EPSILON, boundary + EPSILON]) {
          const frame = sampleBetaMotion(plan, progress, BASE)
          const persistent = colorsOf(frame, 'persistent')
          if (persistent.size > 0) expect(persistent, `persistent at ${progress}`).toEqual(new Set([BASE]))
          const redex = colorsOf(frame, 'redex')
          if (redex.size > 0) expect(redex, `redex at ${progress}`).toEqual(new Set([REDEX_COLOR]))
          const argument = colorsOf(frame, 'argument')
          if (argument.size > 0) {
            expect(argument, `argument at ${progress}`).toEqual(new Set([
              progress < plan.times.split || progress <= plan.times.split + EPSILON
                ? ARGUMENT_COLOR
                : REDEX_COLOR,
            ]))
          }
          const copies = copiesAt(plan, progress)
          for (const [copyIndex, strokes] of copies) {
            const expected = progress <= plan.times.split + EPSILON
              ? ARGUMENT_COLOR
              : COPY_HUES[copyIndex % COPY_HUES.length]
            expect(new Set(strokes.map(({ color }) => color)), `copy ${copyIndex} at ${progress}`)
              .toEqual(new Set([expected]))
          }
        }
      }
    })
  }

  for (const fixture of cases.filter(({ copies }) => copies > 0)) {
    it(`${fixture.name}: duplicates every argument stroke as complete origin-keyed copies`, () => {
      const plan = planBetaMotion(term(fixture.source), ROOT_BETA)
      const sourceArgument = sampleBetaMotion(plan, 0.15 - EPSILON, BASE).strokes
        .filter((stroke) => stroke.lineage === 'argument')
      const expectedOrigins = origins(sourceArgument)
      expect(expectedOrigins.length).toBeGreaterThan(0)

      const copies = copiesAt(plan, 0.34)
      expect([...copies.keys()]).toEqual(Array.from({ length: fixture.copies }, (_, index) => index))
      for (const copy of copies.values()) {
        expect(origins(copy)).toEqual(expectedOrigins)
      }
    })
  }

  it('deletion creates no copy and contracts the complete unused argument', () => {
    const plan = planBetaMotion(term(cases[2].source), ROOT_BETA)
    const sourceArgument = sampleBetaMotion(plan, 0.15 - EPSILON, BASE).strokes
      .filter((stroke) => stroke.lineage === 'argument')
    expect(sourceArgument.length).toBeGreaterThan(0)
    expect(copiesAt(plan, 0.15).size).toBe(0)
    expect(sampleBetaMotion(plan, 0.38, BASE).strokes.some((stroke) => stroke.lineage === 'argument')).toBe(false)
  })

  it('parks complete copies separately, docks them at their sockets, then retracts stems before the binder', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const parked = copiesAt(plan, plan.times.liftEnd)
    const centers = [...parked.values()].map((strokes) => {
      const points = strokes.flatMap(({ points: endpoints }) => endpoints)
      return {
        x: points.reduce((sum, point) => sum + point.x, 0) / points.length,
        y: points.reduce((sum, point) => sum + point.y, 0) / points.length,
      }
    })
    expect(Math.hypot(centers[0]!.x - centers[1]!.x, centers[0]!.y - centers[1]!.y)).toBeGreaterThan(0.01)

    const docked = sampleBetaMotion(plan, plan.times.dockEnd, BASE)
    for (const socket of docked.sockets) {
      const endpoints = docked.strokes
        .filter(({ copyIndex }) => copyIndex === socket.copyIndex)
        .flatMap(({ points }) => points)
      expect(endpoints.some((point) => Math.hypot(point.x - socket.point.x, point.y - socket.point.y) < 1e-9)).toBe(true)
    }
    const stemsRetracting = sampleBetaMotion(plan, (plan.times.dockEnd + plan.times.stemEnd) / 2, BASE)
    expect(stemsRetracting.sockets.every(({ amount }) => amount > 0)).toBe(true)
    expect(stemsRetracting.strokes.some(({ role, lineage }) => role === 'variable' && lineage === 'redex')).toBe(true)
    const binderRetracting = sampleBetaMotion(plan, (plan.times.stemEnd + plan.times.barEnd) / 2, BASE)
    expect(binderRetracting.sockets.every(({ amount }) => amount === 0)).toBe(true)
    expect(binderRetracting.strokes.some(({ role, lineage }) => role === 'variable' && lineage === 'redex')).toBe(false)
    expect(binderRetracting.strokes.some(({ role, lineage }) => role === 'lambda' && lineage === 'redex')).toBe(true)
  })

  for (const fixture of cases) {
    it(`${fixture.name}: moves each persistent junction to its one offered destination before docking`, () => {
      const plan = planBetaMotion(term(fixture.source), ROOT_BETA)
      expect(plan.persistentJunctions.length).toBeGreaterThan(0)
      const destinationFrame = sampleBetaMotion(plan, plan.times.spaceEnd, BASE)
      const points = endpointPositions(destinationFrame.strokes)
      for (const correspondence of plan.persistentJunctions) {
        const point = points.get(correspondence.sourceId)
        expect(point, correspondence.sourceId).toBeDefined()
        expect(point!.x).toBeCloseTo(correspondence.target.x, 10)
        expect(point!.y).toBeCloseTo(correspondence.target.y, 10)
      }
    })
  }

  it('keeps source, redex, argument, and repeating copy hues attached to lineage across every used boundary', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const initial = sampleBetaMotion(plan, 0, BASE)
    expect(new Set(initial.strokes.map(({ color }) => color))).toEqual(new Set([BASE]))

    const identified = sampleBetaMotion(plan, 0.15 - EPSILON, BASE)
    expect(new Set(identified.strokes.filter(({ lineage }) => lineage === 'redex').map(({ color }) => color)))
      .toEqual(new Set([REDEX_COLOR]))
    expect(new Set(identified.strokes.filter(({ lineage }) => lineage === 'argument').map(({ color }) => color)))
      .toEqual(new Set([ARGUMENT_COLOR]))

    const copyStart = copiesAt(plan, 0.15)
    for (const copy of copyStart.values()) expect(new Set(copy.map(({ color }) => color))).toEqual(new Set([ARGUMENT_COLOR]))

    for (const progress of [0.34, 0.54, 0.82, 0.965]) {
      const copies = copiesAt(plan, progress)
      for (const [copyIndex, copy] of copies) {
        expect(new Set(copy.map(({ color }) => color)), `copy ${copyIndex} at ${progress}`)
          .toEqual(new Set([COPY_HUES[copyIndex % COPY_HUES.length]]))
      }
    }

    const settled = copiesAt(plan, 1)
    for (const copy of settled.values()) expect(new Set(copy.map(({ color }) => color))).toEqual(new Set([BASE]))
  })

  it('colors the consumed binder redex pink throughout the interior identify stage', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const frame = sampleBetaMotion(plan, plan.times.split / 2, BASE)
    const binder = frame.strokes.find(({ role, ownerId }) => (
      role === 'lambda' && ownerId === 'root/fn'
    ))
    expect(binder).toBeDefined()
    expect(binder!.color).toBe(REDEX_COLOR)
  })

  it('requires every consumed stroke to be explicitly classified or structurally paired', () => {
    for (const fixture of cases) {
      const plan = planBetaMotion(term(fixture.source), ROOT_BETA)
      const paired = new Set(plan.model.pairs.map(({ source }) => source.id))
      const classified = new Set([
        ...plan.model.sourceArgument,
        ...plan.model.boundStrokes,
        ...plan.model.redexScaffolding,
        plan.model.lambdaStroke,
      ].map(({ id }) => id))
      const unclassified = plan.model.source.strokes.filter((stroke) => (
        !paired.has(stroke.id) && !classified.has(stroke.id)
      ))
      expect(unclassified, fixture.name).toEqual([])
      expect('reflowed' in plan.model, fixture.name).toBe(false)
    }
  })

  it('settles to exactly the canonical target stroke set after structural joining', () => {
    const plan = planBetaMotion(term(cases[2].source), ROOT_BETA)
    const settled = sampleBetaMotion(plan, 1, BASE)
    expect(settled.strokes.map(({ id }) => id))
      .toEqual(plan.model.target.strokes.map(({ id }) => id))
  })

  it('rejects a consumed surviving-owner stroke outside the explicit classifications', async () => {
    vi.resetModules()
    let calls = 0
    vi.doMock('../../src/view/tromp', async (importOriginal) => {
      const actual = await importOriginal<typeof import('../../src/view/tromp')>()
      return {
        ...actual,
        trompGrid: (...args: Parameters<typeof actual.trompGrid>) => {
          const grid = actual.trompGrid(...args)
          if (calls++ !== 0) return grid
          return {
            ...grid,
            bars: [
              ...grid.bars,
              { row: 0, colStart: 0, colEnd: 0, kind: 'lam' as const },
            ],
            barOwners: [...grid.barOwners, ['fn', 'body'] as const],
          }
        },
      }
    })
    const mocked = await import('../../src/view/lambda-motion')
    expect(() => mocked.planBetaMotion(
      term(cases[2].source),
      ROOT_BETA,
    )).toThrow(/unclassified consumed strokes.*root\/fn\/body:lambda/i)
    vi.doUnmock('../../src/view/tromp')
    vi.resetModules()
  })

  it('uses the fifth hue and repeats the corrected palette without changing complete-copy identity', () => {
    const sixUses = '(\\x. x x x x x x) (\\z. z)'
    const plan = planBetaMotion(term(sixUses), ROOT_BETA)
    const copies = copiesAt(plan, plan.times.liftEnd)
    expect([...copies.keys()]).toEqual([0, 1, 2, 3, 4, 5])
    expect([...copies].map(([index, strokes]) => [index, new Set(strokes.map(({ color }) => color))]))
      .toEqual(COPY_HUES.concat(COPY_HUES[0]!).map((color, index) => [index, new Set([color])]))
  })

  it('drives the circular geometry and colored 2D paint consumers from the sampled frame', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const frame = sampleBetaMotion(plan, plan.times.spaceEnd, BASE)
    const geometry = lambdaFrameGeometry(frame)
    const ordinaryArcs = frame.strokes.filter(({ geometry: shape, role }) => (
      shape.kind === 'arc' && role !== 'output-arc'
    ))
    const ordinarySegments = frame.strokes.filter(({ geometry: shape, role }) => (
      shape.kind === 'segment' && role !== 'output-line'
    ))
    expect(geometry.arcs).toHaveLength(ordinaryArcs.length)
    expect(geometry.radials).toHaveLength(ordinarySegments.length)
    expect(geometry.exitArc).not.toBeNull()
    expect(geometry.exitLine).not.toBeNull()
    expect(Object.keys(geometry.portAnchors)).toEqual(['out'])

    const shapes = paintLambdaFrame(frame, { x: 10, y: 20 }, Math.PI / 3, 2, 3, false)
    expect(shapes).toHaveLength(frame.strokes.length + frame.sockets.length)
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
