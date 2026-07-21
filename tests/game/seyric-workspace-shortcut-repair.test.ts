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
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'
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

const deiterate = (
  diagram: Diagram,
  region: RegionId,
  regions: readonly RegionId[],
): ProofStep => {
  const sel = { region, regions, nodes: [], wires: [] }
  return { rule: 'deiteration', sel, ...findDeiterationEvidence(diagram, sel, 100) }
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
    expect(() => deiterate(diagram, 'r10', ['r11', 'r12']))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(diagram, { rule: 'doubleCutElim', region: 'r6' }, context, 'backward'))
      .toThrow(/annulus/)
    expect(() => deiterate(diagram, 'dc', ['dc_0'])).toThrow()

    const exact = applyStep(diagram, exactIntro, context, 'backward')
    const consume = deiterate(exact, 'dc', ['dc_0'])
    expect(() => applyStep(exact, consume, context, 'backward')).not.toThrow()

    for (const regions of [['r11'], ['r12']] as const) {
      const partial = applyStep(diagram, {
        rule: 'doubleCutIntro',
        sel: { region: 'r10', regions, nodes: [], wires: [] },
      }, context, 'backward')
      expect(() => deiterate(partial, 'dc', ['dc_0'])).toThrow(/no justifying occurrence/)
    }
    const oversized = applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: 'r10', regions: ['r11', 'r12'], nodes: ['n6'], wires: [] },
    }, context, 'backward')
    expect(() => deiterate(oversized, 'dc', ['dc_0'])).toThrow(/no justifying occurrence/)
  })

  it('makes the atomic copy direction legal only after the double cut changes its ancestry', () => {
    const diagram = puzzle('double-cut-copy-license')
    expect(() => findDeiterationEvidence(diagram, {
      region: 'r6', regions: [], nodes: ['n1'], wires: [],
    }, 100))
      .toThrow(/no justifying occurrence/)
    expect(() => findDeiterationEvidence(diagram, {
      region: 'r4', regions: [], nodes: ['n0'], wires: [],
    }, 100))
      .toThrow(/no justifying occurrence/)
    expect(() => applyStep(diagram, { rule: 'doubleCutElim', region: 'r4' }, context, 'backward'))
      .toThrow(/annulus/)

    const exact = applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n1'], wires: [] },
    }, context, 'backward')
    const consume = deiterate(exact, 'dc', ['dc_0'])
    expect(() => applyStep(exact, consume, context, 'backward')).not.toThrow()

    for (const nodes of [['n2'], ['n1', 'n2']] as const) {
      const wrong = applyStep(diagram, {
        rule: 'doubleCutIntro',
        sel: { region: 'r6', regions: [], nodes, wires: [] },
      }, context, 'backward')
      expect(() => deiterate(wrong, 'dc', ['dc_0'])).toThrow(/no justifying occurrence/)
    }
  })

  it('makes the introduced annulus the only useful host for the exact bound branch construction', () => {
    const diagram = puzzle('double-cut-insertion-workspace')
    const [introduceWorkspace, introduceBranch, spawnP, spawnQ, consume] = witness(
      'double-cut-insertion-workspace',
    )
    expect([introduceWorkspace?.rule, introduceBranch?.rule, spawnP?.rule, spawnQ?.rule, consume?.rule])
      .toEqual(['doubleCutIntro', 'doubleCutIntro', 'boundRelationSpawn', 'boundRelationSpawn', 'deiteration'])
    if (introduceWorkspace === undefined || introduceBranch === undefined
      || spawnP === undefined || spawnQ === undefined || consume === undefined
      || spawnP.rule !== 'boundRelationSpawn' || spawnQ.rule !== 'boundRelationSpawn'
      || consume.rule !== 'deiteration') {
      throw new Error('workspace witness must contain its complete bound-branch construction')
    }

    expect(() => applyStep(diagram, introduceBranch, context, 'backward')).toThrow()
    const openedWorkspace = applyStep(
      diagram,
      { rule: 'doubleCutElim', region: 'r4' },
      context,
      'backward',
    )
    expect(hasExactSiblingComplement(openedWorkspace)).toBe(false)

    const introduced = applyStep(diagram, introduceWorkspace, context, 'backward')
    expect(() => findDeiterationEvidence(introduced, consume.sel, 100))
      .toThrow(/no justifying occurrence/)
    const branch = applyStep(introduced, introduceBranch, context, 'backward')
    expect(() => findDeiterationEvidence(branch, consume.sel, 100))
      .toThrow(/no justifying occurrence/)
    const oneBinder = applyStep(branch, spawnP, context, 'backward')
    expect(() => findDeiterationEvidence(oneBinder, consume.sel, 100))
      .toThrow(/no justifying occurrence/)
    const exact = applyStep(oneBinder, spawnQ, context, 'backward')
    expect(() => applyStep(exact, consume, context, 'backward')).not.toThrow()

    expect(() => applyStep(branch, { ...spawnP, region: 'r6' }, context, 'backward'))
      .not.toThrow()
    const sibling = applyStep(branch, { ...spawnP, region: 'r6' }, context, 'backward')
    expect(() => findDeiterationEvidence(sibling, consume.sel, 100)).toThrow(/no justifying occurrence/)
  })
})
