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
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import type { SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { actionFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const redesignedIds = [
  'sey-dm-ec-i01',
  'sey-dm-fc-i01',
  'sey-dm-ec-c01',
  'compound-conjunction-de-morgan',
  'sey-dm-ed-i01',
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

const context = EMPTY_PROOF_CONTEXT
const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T
const puzzle = (id: string): Diagram =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)
const witness = (id: string): readonly ProofStep[] =>
  content<ValidationFile>(`validation/${id}.json`).solution
    .map((action, index) => actionFromJson(action, `${id} solution action ${index}`))
    .flatMap((action) => action.steps)
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
  const limit = 1 << values.length
  for (let mask = 1; mask < limit; mask += 1) {
    const selected: T[] = []
    for (let index = 0; index < values.length; index += 1) {
      if ((mask & (1 << index)) !== 0) selected.push(values[index]!)
    }
    yield selected
  }
}

/** Exact selectable sibling groups are shortcut authority; NNF equivalence is not. */
const hasExactSiblingComplement = (diagram: Diagram): boolean => {
  const matrix = analyzeSeyricStart(diagram).matrixRoot
  if (matrix === null) return false
  const items = directItems(diagram, matrix)
  for (const cutItem of items) {
    if (cutItem.kind !== 'region' || diagram.regions[cutItem.id]?.kind !== 'cut') continue
    const contents = directItems(diagram, cutItem.id)
    if (contents.length === 0) continue
    const contentKey = graphicalKey(diagram, selection(cutItem.id, contents))
    const siblings = items.filter(({ id }) => id !== cutItem.id)
    for (const candidate of subsets(siblings)) {
      if (graphicalKey(diagram, selection(matrix, candidate)) === contentKey) return true
    }
  }
  return false
}

const subtreeBinders = (diagram: Diagram, root: RegionId): readonly RegionId[] => {
  const regions = new Set<RegionId>([root])
  let changed = true
  while (changed) {
    changed = false
    for (const [id, region] of Object.entries(diagram.regions)) {
      if (region.kind === 'sheet' || regions.has(id) || !regions.has(region.parent)) continue
      regions.add(id)
      changed = true
    }
  }
  return Object.values(diagram.nodes).flatMap((node) =>
    node.kind === 'atom' && regions.has(node.region) ? [node.binder] : [])
}

const applying = (diagram: Diagram, steps: readonly ProofStep[]): Diagram => replay(diagram, steps)
const mustRefuse = (diagram: Diagram, step: ProofStep, label: string): void => {
  expect(() => applyStep(diagram, step, context, 'backward'), label).toThrow()
}

const consumerPlan: Readonly<Record<
  'sey-dm-ec-i01' | 'sey-dm-ec-c01' | 'compound-conjunction-de-morgan', {
  readonly buildCount: number
  readonly buildRule: 'doubleCutIntro' | 'doubleCutElim'
  readonly consumeIndex: number
}>> = {
  'sey-dm-ec-i01': {
    buildCount: 2,
    buildRule: 'doubleCutIntro',
    consumeIndex: 2,
  },
  'sey-dm-ec-c01': {
    buildCount: 3,
    buildRule: 'doubleCutIntro',
    consumeIndex: 3,
  },
  'compound-conjunction-de-morgan': {
    buildCount: 2,
    buildRule: 'doubleCutIntro',
    consumeIndex: 2,
  },
}

const forwardSourceOperands: Readonly<Record<keyof typeof consumerPlan, readonly (readonly string[])[]>> = {
  'sey-dm-ec-i01': [['p'], ['q']],
  'sey-dm-ec-c01': [['p'], ['q'], ['r']],
  'compound-conjunction-de-morgan': [['p', 'q'], ['r']],
}

const directBinderSignatures = (diagram: Diagram, region: RegionId): readonly (readonly string[])[] =>
  directItems(diagram, region).map((item) => {
    if (item.kind === 'node') {
      const node = diagram.nodes[item.id]
      if (node?.kind !== 'atom') throw new Error(`Expected direct atom ${item.id}`)
      return [node.binder]
    }
    return [...new Set(subtreeBinders(diagram, item.id))].sort()
  })

const expectDoubleCutOperands = (
  diagram: Diagram,
  source: RegionId,
  expectedBinders: readonly (readonly string[])[],
): void => {
  const operands = directItems(diagram, source)
  expect(operands.every(({ kind }) => kind === 'region'), `${source} double-cut operands`).toBe(true)
  expect(operands.map(({ id }) => {
    const outerContents = directItems(diagram, id)
    expect(outerContents, `${source}/${id} outer cut`).toHaveLength(1)
    expect(outerContents[0]?.kind, `${source}/${id} inner cut`).toBe('region')
    const inner = outerContents[0]!.id
    expect(diagram.regions[id]?.kind, `${source}/${id} outer kind`).toBe('cut')
    expect(diagram.regions[inner]?.kind, `${source}/${id} inner kind`).toBe('cut')
    return [...new Set(subtreeBinders(diagram, id))].sort()
  })).toEqual(expectedBinders)
}

describe('Seyric De Morgan family reconstruction', () => {
  it('provides five distinct, replayable, shortcut-free Seyric problems', () => {
    const fingerprints = new Set<string>()
    for (const id of redesignedIds) {
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
      expect(validation.expectedRules, id).toEqual([...new Set(steps.map((step) => step.rule))])
      expect(isBlank(replay(diagram, steps)), `${id} witness must reach blank`).toBe(true)
    }
  })

  it('does not hide an exact identity behind one opening double-cut elimination', () => {
    for (const id of redesignedIds) {
      const diagram = puzzle(id)
      for (const [region, value] of Object.entries(diagram.regions)) {
        if (value.kind !== 'cut') continue
        let opened: Diagram
        try {
          opened = applyStep(diagram, { rule: 'doubleCutElim', region }, context, 'backward')
        } catch {
          // Only legal initial openings are relevant.
          continue
        }
        expect(hasExactSiblingComplement(opened), `${id} opening ${region}`).toBe(false)
      }
    }
  })

  it('starts from and constructs the assigned De Morgan formula in one source cut', () => {
    for (const id of Object.keys(consumerPlan) as Array<keyof typeof consumerPlan>) {
      const diagram = puzzle(id)
      const steps = witness(id)
      const expected = forwardSourceOperands[id]

      expect(diagram.regions.source, `${id} source region`).toEqual({ kind: 'cut', parent: 'work' })
      expect(directBinderSignatures(diagram, 'source'), `${id} initial negated conjunction`).toEqual(expected)
      expect(steps.slice(0, expected.length).every((step) =>
        step.rule === 'doubleCutIntro' && step.sel.region === 'source'), `${id} source-local expansion`).toBe(true)

      const transformed = applying(diagram, steps.slice(0, expected.length))
      expectDoubleCutOperands(transformed, 'source', expected)
    }

    const reverse = puzzle('sey-dm-fc-i01')
    const reverseSteps = witness('sey-dm-fc-i01')
    expect(reverse.regions.source, 'reverse source region').toEqual({ kind: 'cut', parent: 'work' })
    expectDoubleCutOperands(reverse, 'source', [['p'], ['q']])
    expect(reverseSteps.slice(0, 2)).toMatchObject([
      { rule: 'doubleCutElim', region: 'source-p-outer' },
      { rule: 'doubleCutElim', region: 'source-q-outer' },
    ])
    const converged = applying(reverse, reverseSteps.slice(0, 2))
    expect(directBinderSignatures(converged, 'source'), 'reverse negated conjunction').toEqual([['p'], ['q']])
    expect(directItems(converged, 'source').every(({ kind }) => kind === 'node')).toBe(true)
  })

  it('makes the complete forward De Morgan result unlock its downstream consumer', () => {
    for (const id of Object.keys(consumerPlan) as Array<keyof typeof consumerPlan>) {
      const diagram = puzzle(id)
      const steps = witness(id)
      const plan = consumerPlan[id]
      const build = steps.slice(0, plan.buildCount)
      const consume = steps[plan.consumeIndex]!

      expect(build.map(({ rule }) => rule), `${id} graphical build`).toEqual(
        Array.from({ length: plan.buildCount }, () => plan.buildRule),
      )

      for (let completed = 0; completed < plan.buildCount; completed += 1) {
        mustRefuse(
          applying(diagram, build.slice(0, completed)),
          consume,
          `${id} consumer after only ${completed} source operands`,
        )
      }
      expect(() => applyStep(applying(diagram, build), consume, context, 'backward'), `${id} complete transform`)
        .not.toThrow()
    }
  })

  it('makes the complete reverse De Morgan result unlock its downstream consumer', () => {
    const id = 'sey-dm-fc-i01'
    const diagram = puzzle(id)
    const steps = witness(id)
    const consume = steps[2]!

    mustRefuse(diagram, consume, `${id} consumer before convergence`)
    mustRefuse(applyStep(diagram, steps[0]!, context, 'backward'), consume, `${id} consumer after one branch`)
    expect(() => applyStep(applying(diagram, steps.slice(0, 2)), consume, context, 'backward'),
      `${id} consumer after complete convergence`).not.toThrow()
  })

  it('keeps the compound source intact while transforming its atomic peer separately', () => {
    const diagram = puzzle('compound-conjunction-de-morgan')
    const steps = witness('compound-conjunction-de-morgan')
    expect(steps[0]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { region: 'source', regions: ['source-compound'], nodes: [] },
    })
    expect(new Set(subtreeBinders(diagram, 'source-compound')).size).toBe(2)
    expect(steps[1]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { region: 'source', regions: [], nodes: ['source-r'] },
    })
  })

  it('makes both compound-disjunction outputs independently feed the final conjunction', () => {
    const id = 'sey-dm-ed-i01'
    const diagram = puzzle(id)
    const steps = witness(id)

    expect(steps.slice(0, 7).map(({ rule }) => rule)).toEqual([
      'doubleCutElim',
      'deiteration', 'doubleCutElim',
      'deiteration', 'doubleCutElim',
      'deiteration', 'deiteration',
    ])

    const expanded = applying(diagram, steps.slice(0, 1))
    expect(new Set(subtreeBinders(expanded, (steps[1] as Extract<ProofStep, {
      rule: 'deiteration'
    }>).sel.regions[0]!)).size, 'compound left output').toBe(2)
    expect(new Set(subtreeBinders(expanded, (steps[3] as Extract<ProofStep, {
      rule: 'deiteration'
    }>).sel.regions[0]!)).size, 'atomic right output').toBe(1)
    const leftOnly = applying(expanded, steps.slice(1, 3))
    expect(() => applyStep(leftOnly, steps[5]!, context, 'backward')).not.toThrow()
    mustRefuse(leftOnly, steps[6]!, 'the right output must not exist after only the left branch')

    const rightOnly = applying(expanded, steps.slice(3, 5))
    expect(() => applyStep(rightOnly, steps[6]!, context, 'backward')).not.toThrow()
    mustRefuse(rightOnly, steps[5]!, 'the left output must not exist after only the right branch')

    expect(() => applying(diagram, steps.slice(0, 7)), 'both outputs feed the target')
      .not.toThrow()
  })
})
