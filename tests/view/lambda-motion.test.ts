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
  type LambdaStroke,
} from '../../src/view/lambda-motion'
import { lambdaFrameGeometry } from '../../src/view/morph'
import { paintLambdaFrame } from '../../src/view/paint'
import { termGeometry, type NodeGeometry } from '../../src/view/bend'

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

const origins = (strokes: readonly { readonly originId: string }[]): string[] => (
  [...new Set(strokes.map(({ originId }) => originId))].sort()
)

const copiesAt = (plan: LambdaMotionPlan, progress: number): Map<number, LambdaStroke[]> => {
  const copies = new Map<number, LambdaStroke[]>()
  for (const stroke of sampleBetaMotion(plan, progress, BASE).strokes) {
    const match = /^copy:(\d+):/.exec(stroke.id)
    if (match === null) continue
    const copyIndex = Number(match[1])
    const group = copies.get(copyIndex) ?? []
    group.push(stroke)
    copies.set(copyIndex, group)
  }
  return copies
}

const colorsOf = (
  frame: ReturnType<typeof sampleBetaMotion>,
  ids: ReadonlySet<string>,
): Set<string> => (
  new Set(frame.strokes.filter((stroke) => ids.has(stroke.id)).map((stroke) => stroke.color))
)

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
    it(`${fixture.name}: reaches the capture-avoiding target with the expected copy count`, () => {
      const source = term(fixture.source)
      const plan = planBetaMotion(source, ROOT_BETA)

      expect(plan.copyCount).toBe(fixture.copies)
      expect(termEq(plan.target, term(fixture.target))).toBe(true)
      expect(termEq(plan.target, applyStepAt(source, ROOT_BETA))).toBe(true)
    })

    it(`${fixture.name}: preserves hue identity immediately before and after every boundary`, () => {
      const plan = planBetaMotion(term(fixture.source), ROOT_BETA)
      const persistentIds = new Set(plan.model.pairs.map(({ source }) => source.id))
      const redexIds = new Set([
        plan.model.lambdaStroke,
        ...plan.model.boundStrokes,
        ...plan.model.redexScaffolding,
      ].map(({ id }) => id))
      const argumentIds = new Set(plan.model.sourceArgument.map(({ id }) => id))
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
          const persistent = colorsOf(frame, persistentIds)
          if (persistent.size > 0) expect(persistent, `persistent at ${progress}`).toEqual(new Set([BASE]))
          const redex = colorsOf(frame, redexIds)
          if (redex.size > 0) expect(redex, `redex at ${progress}`).toEqual(new Set([REDEX_COLOR]))
          const argument = colorsOf(frame, argumentIds)
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
      const expectedOrigins = origins(plan.model.sourceArgument)
      expect(expectedOrigins.length).toBeGreaterThan(0)

      const copies = copiesAt(plan, 0.34)
      expect([...copies.keys()]).toEqual(Array.from({ length: fixture.copies }, (_, index) => index))
      for (const [copyIndex, copy] of copies) {
        const planned = plan.model.targetCopies.get(copyIndex) ?? []
        expect(origins(planned)).toEqual(expectedOrigins)
        expect(copy.map(({ id }) => id).sort()).toEqual(planned.map(({ id }) => id).sort())
      }
    })
  }

  it('deletion creates no copy and contracts the complete unused argument', () => {
    const plan = planBetaMotion(term(cases[2].source), ROOT_BETA)
    const argumentIds = new Set(plan.model.sourceArgument.map(({ id }) => id))
    const sourceArgument = sampleBetaMotion(plan, 0.15 - EPSILON, BASE).strokes
      .filter((stroke) => argumentIds.has(stroke.id))
    expect(sourceArgument.length).toBeGreaterThan(0)
    expect(copiesAt(plan, 0.15).size).toBe(0)
    expect(sampleBetaMotion(plan, 0.38, BASE).strokes.some((stroke) => argumentIds.has(stroke.id))).toBe(false)
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
    const dockedCopies = copiesAt(plan, plan.times.dockEnd)
    for (const socket of docked.sockets) {
      const copyIndex = Number(/^socket:(\d+)$/.exec(socket.id)?.[1])
      const endpoints = (dockedCopies.get(copyIndex) ?? [])
        .flatMap(({ points }) => points)
      expect(endpoints.some((point) => Math.hypot(point.x - socket.point.x, point.y - socket.point.y) < 1e-9)).toBe(true)
    }
    const stemsRetracting = sampleBetaMotion(plan, (plan.times.dockEnd + plan.times.stemEnd) / 2, BASE)
    const boundIds = new Set(plan.model.boundStrokes.map(({ id }) => id))
    expect(stemsRetracting.sockets.every(({ amount }) => amount > 0)).toBe(true)
    expect(stemsRetracting.strokes.some(({ id, role }) => role === 'variable' && boundIds.has(id))).toBe(true)
    const binderRetracting = sampleBetaMotion(plan, (plan.times.stemEnd + plan.times.barEnd) / 2, BASE)
    expect(binderRetracting.sockets.every(({ amount }) => amount === 0)).toBe(true)
    expect(binderRetracting.strokes.some(({ id, role }) => role === 'variable' && boundIds.has(id))).toBe(false)
    expect(binderRetracting.strokes.some(({ id }) => id === plan.model.lambdaStroke.id)).toBe(true)
  })

  it('keeps coincident application-copy lambda bars as complete visible arcs in 2D at parking and settle', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const expectedSweep = 5 * Math.PI / 42

    for (const progress of [plan.times.spaceEnd, 1]) {
      const frame = sampleBetaMotion(plan, progress, BASE)
      const copyBars = frame.strokes.filter(({ id, role }) => id.startsWith('copy:') && role === 'lambda')
      expect(copyBars).toHaveLength(2)
      for (const bar of copyBars) {
        expect(bar.geometry.kind).toBe('arc')
        if (bar.geometry.kind !== 'arc') throw new Error('copy lambda bar is not circular')
        expect(bar.geometry.a1 - bar.geometry.a0).toBeCloseTo(expectedSweep, 12)
        expect(bar.geometry.r * (bar.geometry.a1 - bar.geometry.a0)).toBeGreaterThan(2)
      }

      const painted = paintLambdaFrame(frame, { x: 0, y: 0 }, 0, 1, 3, false)
      const paintedBars = painted.filter((shape, index) => (
        copyBars.some(({ id }) => id === frame.strokes[index]?.id) && shape.kind === 'arc'
      ))
      expect(paintedBars).toHaveLength(2)
      expect(paintedBars.every((shape) => shape.kind === 'arc' && shape.a1 > shape.a0)).toBe(true)
    }
  })

  it('keeps source, redex, argument, and repeating copy hues attached to lineage across every used boundary', () => {
    const plan = planBetaMotion(term(cases[1].source), ROOT_BETA)
    const initial = sampleBetaMotion(plan, 0, BASE)
    expect(new Set(initial.strokes.map(({ color }) => color))).toEqual(new Set([BASE]))

    const identified = sampleBetaMotion(plan, 0.15 - EPSILON, BASE)
    const redexIds = new Set([
      plan.model.lambdaStroke,
      ...plan.model.boundStrokes,
      ...plan.model.redexScaffolding,
    ].map(({ id }) => id))
    const argumentIds = new Set(plan.model.sourceArgument.map(({ id }) => id))
    expect(colorsOf(identified, redexIds))
      .toEqual(new Set([REDEX_COLOR]))
    expect(colorsOf(identified, argumentIds))
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
    const binder = frame.strokes.find(({ id }) => id === plan.model.lambdaStroke.id)
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

  it('reaches the ordinary canonical target paint geometry before structural motion settles', () => {
    for (const fixture of cases) {
      const parsed = parseTerm(fixture.source)
      const plan = planBetaMotion(parsed.term, ROOT_BETA, parsed.freeIdentifiers.length)
      expect(paintGeometry(lambdaFrameGeometry(sampleBetaMotion(plan, 1, BASE))), fixture.name)
        .toEqual(paintGeometry(termGeometry(plan.target, parsed.freeIdentifiers.length)))
    }
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
