import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import {
  analyzeSeyricPropositionalShape,
  analyzeSeyricStart,
  auditSeyricWitness,
} from '../../src/game/content/seyric-authority'
import { boundaryForm } from '../../src/kernel/diagram/canonical/explore'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import type { SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import { stepFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const repairedIds = [
  'compound-disjunction-exchange',
  'double-cut-copy-license',
  'double-cut-insertion-workspace',
] as const

type PuzzleFile = { readonly id: string; readonly diagram: unknown }
type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}
type Item = { readonly kind: 'region' | 'node'; readonly id: string }

const context = { theorems: new Map(), relations: new Map() }
const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T
const puzzle = (id: string): Diagram =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)
const witness = (id: string): readonly ProofStep[] =>
  content<ValidationFile>(`validation/${id}.json`).solution.map(stepFromJson)
const replay = (diagram: Diagram, steps: readonly ProofStep[]): Diagram =>
  steps.reduce((state, step) => applyStep(state, step, context, 'backward'), diagram)

const directItems = (diagram: Diagram, region: RegionId): readonly Item[] => [
  ...Object.entries(diagram.regions)
    .filter(([, value]) => value.kind !== 'sheet' && value.parent === region)
    .map(([id]) => ({ kind: 'region' as const, id })),
  ...Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => ({ kind: 'node' as const, id })),
]

const selection = (region: RegionId, items: readonly Item[]): SubgraphSelection => ({
  region,
  regions: items.filter(({ kind }) => kind === 'region').map(({ id }) => id),
  nodes: items.filter(({ kind }) => kind === 'node').map(({ id }) => id),
  wires: [],
})

const graphicalKey = (diagram: Diagram, selected: SubgraphSelection): string => {
  const extracted = extractSubgraph(diagram, selected)
  return JSON.stringify([boundaryForm(extracted.pattern), extracted.binderAttachments])
}

const subsets = function* <T>(values: readonly T[]): Generator<readonly T[]> {
  for (let mask = 1; mask < (1 << values.length); mask += 1) {
    const selected: T[] = []
    for (let index = 0; index < values.length; index += 1) {
      if ((mask & (1 << index)) !== 0) selected.push(values[index]!)
    }
    yield selected
  }
}

const hasExactSiblingComplement = (diagram: Diagram): boolean => {
  const matrix = analyzeSeyricStart(diagram).matrixRoot
  if (matrix === null) return false
  const items = directItems(diagram, matrix)
  for (const item of items) {
    if (item.kind !== 'region' || diagram.regions[item.id]?.kind !== 'cut') continue
    const contents = directItems(diagram, item.id)
    if (contents.length === 0) continue
    const contentKey = graphicalKey(diagram, selection(item.id, contents))
    const siblings = items.filter(({ id }) => id !== item.id)
    for (const candidate of subsets(siblings)) {
      if (graphicalKey(diagram, selection(matrix, candidate)) === contentKey) return true
    }
  }
  return false
}

const deiterate = (region: RegionId, regions: readonly RegionId[]): ProofStep => ({
  rule: 'deiteration',
  sel: { region, regions, nodes: [], wires: [] },
  fuel: 100,
})

const doubleCutPairPattern = (arity: 1 | 2) => {
  const builder = new DiagramBuilder()
  const binders: RegionId[] = []
  let parent = builder.root
  for (let index = 0; index < arity; index += 1) {
    const binder = builder.bubble(parent, 0)
    binders.push(binder)
    parent = binder
  }
  const outer = builder.cut(parent)
  const inner = builder.cut(outer)
  for (const binder of binders) builder.atom(inner, binder)
  return { pattern: { diagram: builder.build(), boundary: [] }, binders }
}

describe('Seyric workspace shortcut repairs', () => {
  it('provides shortcut-free, replayable Seyric starts', () => {
    const fingerprints = new Set<string>()
    for (const id of repairedIds) {
      const diagram = puzzle(id)
      const steps = witness(id)
      const validation = content<ValidationFile>(`validation/${id}.json`)
      const shape = analyzeSeyricPropositionalShape(diagram)

      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(shape.immediateComplement, id).toBe(false)
      expect(hasExactSiblingComplement(diagram), id).toBe(false)
      expect(fingerprints.has(shape.quantifierOrderFingerprint), id).toBe(false)
      fingerprints.add(shape.quantifierOrderFingerprint)
      expect(validation.availableArtifacts, id).toEqual([])
      expect(validation.recognizedStates, id).toEqual([])
      expect(validation.expectedRules, id).toEqual([...new Set(steps.map(({ rule }) => rule))])
      expect(isBlank(replay(diagram, steps)), `${id} witness must reach blank`).toBe(true)
    }
  })

  it('makes the whole exchanged disjunction acquire its required boundary only in the workspace', () => {
    const diagram = puzzle('compound-disjunction-exchange')
    const exactIntro: ProofStep = {
      rule: 'doubleCutIntro',
      sel: { region: 'r10', regions: ['r11', 'r12'], nodes: [], wires: [] },
    }
    const consume = deiterate('dc', ['dc_0'])

    expect(() => applyStep(diagram, deiterate('r10', ['r11', 'r12']), context, 'backward'))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(diagram, { rule: 'doubleCutElim', region: 'r6' }, context, 'backward'))
      .toThrow(/annulus/)
    expect(() => applyStep(diagram, consume, context, 'backward')).toThrow()

    const exact = applyStep(diagram, exactIntro, context, 'backward')
    expect(() => applyStep(exact, consume, context, 'backward')).not.toThrow()

    for (const regions of [['r11'], ['r12']] as const) {
      const partial = applyStep(diagram, {
        rule: 'doubleCutIntro',
        sel: { region: 'r10', regions, nodes: [], wires: [] },
      }, context, 'backward')
      expect(() => applyStep(partial, consume, context, 'backward')).toThrow(/no justifying occurrence/)
    }
    const oversized = applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: 'r10', regions: ['r11', 'r12'], nodes: ['n6'], wires: [] },
    }, context, 'backward')
    expect(() => applyStep(oversized, consume, context, 'backward'))
      .toThrow(/no justifying occurrence/)
  })

  it('makes the atomic copy direction legal only after the double cut changes its ancestry', () => {
    const diagram = puzzle('double-cut-copy-license')
    const targetBefore = {
      rule: 'deiteration' as const,
      sel: { region: 'r6', regions: [], nodes: ['n1'], wires: [] },
      fuel: 100,
    }
    const sourceBefore = {
      rule: 'deiteration' as const,
      sel: { region: 'r4', regions: [], nodes: ['n0'], wires: [] },
      fuel: 100,
    }
    const consume = deiterate('dc', ['dc_0'])

    expect(() => applyStep(diagram, targetBefore, context, 'backward'))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(diagram, sourceBefore, context, 'backward'))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(diagram, { rule: 'doubleCutElim', region: 'r4' }, context, 'backward'))
      .toThrow(/annulus/)

    const exact = applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n1'], wires: [] },
    }, context, 'backward')
    expect(() => applyStep(exact, consume, context, 'backward')).not.toThrow()

    for (const nodes of [['n2'], ['n1', 'n2']] as const) {
      const wrong = applyStep(diagram, {
        rule: 'doubleCutIntro',
        sel: { region: 'r6', regions: [], nodes, wires: [] },
      }, context, 'backward')
      expect(() => applyStep(wrong, consume, context, 'backward'))
        .toThrow(/no justifying occurrence/)
    }
  })

  it('makes the introduced annulus the only useful host for the exact compound insertion', () => {
    const diagram = puzzle('double-cut-insertion-workspace')
    const exact = doubleCutPairPattern(2)
    const partial = doubleCutPairPattern(1)
    const insertion = (region: RegionId, candidate = exact): ProofStep => ({
      rule: 'insertion',
      region,
      pattern: candidate.pattern,
      attachments: [],
      binders: candidate.binders.length === 2
        ? { [candidate.binders[0]!]: 'r2', [candidate.binders[1]!]: 'r3' }
        : { [candidate.binders[0]!]: 'r2' },
    })
    const consume = deiterate('dc_0', ['r4'])

    expect(() => applyStep(diagram, consume, context, 'backward')).toThrow()
    expect(() => applyStep(diagram, insertion('r3'), context, 'backward'))
      .toThrow(/requires a positive region/)
    const openedWorkspace = applyStep(
      diagram,
      { rule: 'doubleCutElim', region: 'r4' },
      context,
      'backward',
    )
    expect(hasExactSiblingComplement(openedWorkspace)).toBe(false)

    for (const host of ['r4', 'r6'] as const) {
      const wrongHost = applyStep(diagram, insertion(host), context, 'backward')
      expect(() => applyStep(wrongHost, deiterate('r3', ['r4']), context, 'backward'))
        .toThrow(/no justifying occurrence/)
    }

    const introduced = applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: 'r3', regions: ['r4'], nodes: [], wires: [] },
    }, context, 'backward')
    expect(() => applyStep(introduced, consume, context, 'backward'))
      .toThrow(/no justifying occurrence/)
    const inserted = applyStep(introduced, insertion('dc'), context, 'backward')
    expect(() => applyStep(inserted, consume, context, 'backward')).not.toThrow()

    const withPartial = applyStep(introduced, insertion('dc', partial), context, 'backward')
    expect(() => applyStep(withPartial, consume, context, 'backward'))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(introduced, insertion('dc_0'), context, 'backward'))
      .toThrow(/requires a positive region/)

    const sibling = applyStep(introduced, insertion('r6'), context, 'backward')
    expect(() => applyStep(sibling, consume, context, 'backward'))
      .toThrow(/no justifying occurrence/)
  })
})
