import { readFileSync, readdirSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import {
  analyzeSeyricPropositionalShape,
  analyzeSeyricStart,
  auditSeyricWitness,
} from '../../src/game/content/seyric-authority'
import { boundaryForm } from '../../src/kernel/diagram/canonical/explore'
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { stepFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const redesignedIds = [
  'marked-echo-deiteration',
  'atomic-content-insertion',
  'structural-recognition-routing-choice',
  'weakening-injection-weave',
  'sey-red-c01',
  'grouped-branch-construction',
] as const

type PuzzleFile = { readonly id: string; readonly diagram: unknown }
type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}

const context = { theorems: new Map(), relations: new Map() }

const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T

const puzzle = (id: string): Diagram =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)

const witness = (id: string): readonly ProofStep[] =>
  content<ValidationFile>(`validation/${id}.json`).solution.map(stepFromJson)

const replay = (start: Diagram, steps: readonly ProofStep[]): Diagram =>
  steps.reduce(
    (diagram, step) => applyStep(diagram, step, context, 'backward'),
    start,
  )

const directItems = (diagram: Diagram, region: RegionId) => [
  ...Object.entries(diagram.regions)
    .filter(([, candidate]) => candidate.kind !== 'sheet' && candidate.parent === region)
    .map(([id]) => ({ kind: 'region' as const, id })),
  ...Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => ({ kind: 'node' as const, id })),
]

const complementShortcutDepth = (diagram: Diagram): 0 | 1 | null => {
  if (analyzeSeyricPropositionalShape(diagram).immediateComplement) return 0
  for (const [region, value] of Object.entries(diagram.regions)) {
    if (value.kind !== 'cut') continue
    try {
      const opened = applyStep(diagram, { rule: 'doubleCutElim', region }, context, 'backward')
      if (analyzeSeyricStart(opened).ok
        && analyzeSeyricPropositionalShape(opened).immediateComplement) return 1
    } catch {
      // Not an eliminable annulus.
    }
  }
  return null
}

const closureSize = (diagram: Diagram, root: RegionId): { regions: number; nodes: number } => {
  const regions = new Set([root])
  let changed = true
  while (changed) {
    changed = false
    for (const [id, region] of Object.entries(diagram.regions)) {
      if (region.kind === 'sheet' || regions.has(id) || !regions.has(region.parent)) continue
      regions.add(id)
      changed = true
    }
  }
  return {
    regions: regions.size,
    nodes: Object.values(diagram.nodes).filter((node) => regions.has(node.region)).length,
  }
}

const compoundCutPattern = (arity: 1 | 2 | 3) => {
  const builder = new DiagramBuilder()
  const binders: RegionId[] = []
  let parent = builder.root
  for (let index = 0; index < arity; index += 1) {
    const binder = builder.bubble(parent, 0)
    binders.push(binder)
    parent = binder
  }
  const group = builder.cut(parent)
  for (const binder of binders) builder.atom(group, binder)
  return { pattern: { diagram: builder.build(), boundary: [] }, binders }
}

describe('redesigned Seyric shortcut puzzles', () => {
  it('removes the accidental exposed-complement routes and classifies the one retained exception', () => {
    for (const id of redesignedIds.filter((candidate) => candidate !== 'sey-red-c01')) {
      expect(complementShortcutDepth(puzzle(id)), id).toBeNull()
    }
    expect(complementShortcutDepth(puzzle('sey-red-c01'))).toBe(0)
  })

  it('keeps the intimidating exception as one simple core beside one coherent large junk fragment', () => {
    const diagram = puzzle('sey-red-c01')
    const matrix = analyzeSeyricStart(diagram).matrixRoot!
    const items = directItems(diagram, matrix)
    expect(items).toHaveLength(3)

    const junk = items.find(({ kind, id }) =>
      kind === 'region'
      && diagram.regions[id]?.kind === 'cut'
      && closureSize(diagram, id).regions >= 6)
    expect(junk).toBeDefined()
    expect(closureSize(diagram, junk!.id)).toEqual({ regions: 6, nodes: 6 })
  })

  it('keeps grouped construction outside the two-variable compound excluded-middle family', () => {
    const grouped = boundaryForm({ diagram: puzzle('grouped-branch-construction'), boundary: [] })
    const compoundLem = boundaryForm({ diagram: puzzle('sey-lem-i01'), boundary: [] })
    expect(grouped).not.toBe(compoundLem)
  })

  it('uses an exact marked ancestor fragment rather than an atom inside that fragment', () => {
    const diagram = puzzle('marked-echo-deiteration')
    const exact = applyStep(diagram, witness('marked-echo-deiteration')[0]!, context, 'backward')
    expect(exact).not.toEqual(diagram)
    expect(() => applyStep(diagram, stepFromJson({
      rule: 'deiteration',
      sel: { region: 'r6', regions: [], nodes: ['n1'], wires: [] },
      fuel: 100,
    }), context, 'backward')).toThrow()
  })

  it('makes atomic insertion create the exact source consumed by the next step', () => {
    const diagram = puzzle('atomic-content-insertion')
    const [insert, consume] = witness('atomic-content-insertion')
    const exact = applyStep(diagram, insert!, context, 'backward')
    expect(() => applyStep(exact, consume!, context, 'backward')).not.toThrow()
    expect(() => applyStep(diagram, consume!, context, 'backward')).toThrow()

    const wrong = compoundCutPattern(2)
    const withWrongShape = applyStep(diagram, {
      rule: 'insertion', region: 'r5', pattern: wrong.pattern, attachments: [],
      binders: { [wrong.binders[0]!]: 'r2', [wrong.binders[1]!]: 'r3' },
    }, context, 'backward')
    expect(() => applyStep(withWrongShape, consume!, context, 'backward')).toThrow()
  })

  it('routes an intact marked source before the downstream atomic route exists', () => {
    const diagram = puzzle('structural-recognition-routing-choice')
    const steps = witness('structural-recognition-routing-choice')
    expect(() => applyStep(diagram, steps[0]!, context, 'backward')).not.toThrow()
    expect(() => applyStep(diagram, stepFromJson({
      rule: 'deiteration',
      sel: { region: 'r8', regions: [], nodes: ['n2'], wires: [] },
      fuel: 100,
    }), context, 'backward')).toThrow()
    expect(() => applyStep(diagram, steps[3]!, context, 'backward')).toThrow()
    const routed = replay(diagram, steps.slice(0, 4))
    expect(() => applyStep(routed, steps[4]!, context, 'backward')).not.toThrow()
  })

  it('makes weakening create the whole source placed by injection and consumed downstream', () => {
    const diagram = puzzle('weakening-injection-weave')
    const steps = witness('weakening-injection-weave')
    const [weakenSource, placeSource, removeSpare, exposeChoice, exposeT, consumeT] = steps

    expect(weakenSource).toMatchObject({
      rule: 'erasure',
      sel: { region: 'r9', regions: [], nodes: ['n2'] },
    })
    expect(placeSource).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r12', regions: ['r13'], nodes: [] },
    })
    expect(removeSpare).toMatchObject({
      rule: 'erasure',
      sel: { region: 'r11', regions: ['r15'], nodes: [] },
    })

    expect(complementShortcutDepth(diagram)).toBeNull()
    expect(() => applyStep(diagram, placeSource!, context, 'backward')).toThrow()
    const weakened = applyStep(diagram, weakenSource!, context, 'backward')
    const sourcePlaced = applyStep(weakened, placeSource!, context, 'backward')
    const branchSelected = applyStep(sourcePlaced, removeSpare!, context, 'backward')
    const choiceExposed = applyStep(branchSelected, exposeChoice!, context, 'backward')
    const tExposed = applyStep(choiceExposed, exposeT!, context, 'backward')
    expect(() => applyStep(diagram, consumeT!, context, 'backward')).toThrow()
    expect(() => applyStep(tExposed, consumeT!, context, 'backward')).not.toThrow()

    const oldBoundaryOpened = applyStep(
      diagram,
      stepFromJson({ rule: 'doubleCutElim', region: 'r8' }),
      context,
      'backward',
    )
    expect(() => applyStep(oldBoundaryOpened, stepFromJson({
      rule: 'deiteration',
      sel: { region: 'r6', regions: ['r7'], nodes: ['n2'], wires: [] },
      fuel: 100,
    }), context, 'backward')).toThrow()
  })

  it('requires the intact grouped insertion rather than loose, partial, larger, or wrong-host content', () => {
    const diagram = puzzle('grouped-branch-construction')
    const [exactInsert, consume] = witness('grouped-branch-construction')
    const exact = applyStep(diagram, exactInsert!, context, 'backward')
    expect(() => applyStep(exact, consume!, context, 'backward')).not.toThrow()

    const pair = compoundCutPattern(2)
    const partial = compoundCutPattern(1)
    const larger = compoundCutPattern(3)
    const candidates: readonly { readonly label: string; readonly step: ProofStep }[] = [
      { label: 'loose atoms', step: {
        rule: 'insertion', region: 'r6',
        pattern: (() => {
          const builder = new DiagramBuilder()
          const p = builder.bubble(builder.root, 0)
          const q = builder.bubble(p, 0)
          builder.atom(q, p)
          builder.atom(q, q)
          return { diagram: builder.build(), boundary: [] }
        })(),
        attachments: [], binders: { r1: 'r2', r2: 'r3' },
      } },
      { label: 'partial group', step: {
        rule: 'insertion', region: 'r6', pattern: partial.pattern, attachments: [],
        binders: { [partial.binders[0]!]: 'r2' },
      } },
      { label: 'larger group', step: {
        rule: 'insertion', region: 'r6', pattern: larger.pattern, attachments: [],
        binders: {
          [larger.binders[0]!]: 'r2', [larger.binders[1]!]: 'r3', [larger.binders[2]!]: 'r4',
        },
      } },
      { label: 'wrong host', step: {
        rule: 'insertion', region: 'r7', pattern: pair.pattern, attachments: [],
        binders: { [pair.binders[0]!]: 'r2', [pair.binders[1]!]: 'r3' },
      } },
    ]

    for (const { label, step } of candidates) {
      const near = applyStep(diagram, step, context, 'backward')
      expect(() => applyStep(near, consume!, context, 'backward'), label).toThrow()
    }
  })

  it('keeps every redesigned puzzle structurally Seyric, replayable, witness-clean, and canonically unique', () => {
    const allPaths = readdirSync(resolve(process.cwd(), 'content/puzzles'))
      .filter((name) => name.endsWith('.json'))
    const otherForms = new Map<string, string>()
    for (const name of allPaths) {
      const id = name.slice(0, -5)
      if (redesignedIds.includes(id as typeof redesignedIds[number])) continue
      otherForms.set(boundaryForm({ diagram: puzzle(id), boundary: [] }), id)
    }

    const redesignedForms = new Set<string>()
    for (const id of redesignedIds) {
      const diagram = puzzle(id)
      const steps = witness(id)
      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(isBlank(replay(diagram, steps)), id).toBe(true)
      const form = boundaryForm({ diagram, boundary: [] })
      expect(otherForms.get(form), `${id} duplicates current start`).toBeUndefined()
      expect(redesignedForms.has(form), `${id} duplicates another redesign`).toBe(false)
      redesignedForms.add(form)
    }
  })
})
