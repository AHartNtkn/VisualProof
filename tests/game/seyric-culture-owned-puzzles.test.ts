import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import { analyzeSeyricStart, auditSeyricWitness } from '../../src/game/content/seyric-authority'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { actionFromJson, stepFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'

const seyricOwnedIds = [
  'seyric-field-edit-contrast',
  'seyric-compound-copy-authority',
  'seyric-atomic-double-cut-selection',
  'seyric-extraction-continuation',
] as const

type PuzzleFile = {
  readonly id: string
  readonly diagram: unknown
}

type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}

const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T

const context = EMPTY_PROOF_CONTEXT

const puzzleDiagram = (id: string) =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)

const replay = (id: string, steps: readonly ProofStep[]) => {
  let diagram = puzzleDiagram(id)
  for (const step of steps) diagram = applyStep(diagram, step, context, 'backward')
  return diagram
}

const attemptReplay = (id: string, steps: readonly ProofStep[]) => {
  try {
    return replay(id, steps)
  } catch {
    return null
  }
}

const attempt = (id: string, operation: (diagram: Diagram) => Diagram): Diagram | null => {
  try {
    return operation(puzzleDiagram(id))
  } catch {
    return null
  }
}

const deiterationStep = (diagram: Diagram, sel: SubgraphSelection): ProofStep => ({
  rule: 'deiteration',
  sel,
  ...findDeiterationEvidence(diagram, sel, 100),
})

const solutionSteps = (validation: ValidationFile): readonly ProofStep[] =>
  validation.solution
    .map((action, index) => actionFromJson(action, `${validation.puzzle} solution action ${index}`))
    .flatMap((action) => action.steps)

describe('culture-owned Seyric puzzles', () => {
  it('are replayable, structurally Seyric, witness-clean, and canonically distinct', () => {
    const ownedForms = new Map<string, string>()

    for (const id of seyricOwnedIds) {
      const puzzle = content<PuzzleFile>(`puzzles/${id}.json`)
      const validation = content<ValidationFile>(`validation/${id}.json`)
      expect(puzzle.id).toBe(id)
      expect(validation.puzzle).toBe(id)
      expect(validation.availableArtifacts).toEqual([])
      expect(validation.recognizedStates).toEqual([])

      const diagram = diagramFromJson(puzzle.diagram)
      const steps = solutionSteps(validation)
      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(validation.expectedRules).toEqual([...new Set(steps.map((step) => step.rule))])

      let replayed = diagram
      for (const step of steps) {
        replayed = applyStep(replayed, step, context, 'backward')
      }
      expect(isBlank(replayed), `${id} witness must end at blank`).toBe(true)
      ownedForms.set(id, exploreForm(diagram))
    }

    expect(new Set(ownedForms.values()).size).toBe(seyricOwnedIds.length)

    const progression = content<{
      readonly cultures: readonly { readonly id: string; readonly puzzles: readonly string[] }[]
    }>('progression/core.json')
    const existingSeyricIds = progression.cultures
      .find(({ id }) => id === 'seyric-horizon')!
      .puzzles
      .filter((id) => !seyricOwnedIds.includes(id as typeof seyricOwnedIds[number]))
    const existingForms = new Map(existingSeyricIds.map((id) => [
      exploreForm(diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)),
      id,
    ]))

    for (const [id, form] of ownedForms) {
      expect(existingForms.get(form), `${id} duplicates an existing Seyric start`).toBeUndefined()
    }
  })

  it('requires the field edit rather than allowing the surrounding continuation alone', () => {
    const steps = solutionSteps(content<ValidationFile>('validation/seyric-field-edit-contrast.json'))
      .filter((_, index) => index !== 0)
    const bypass = attemptReplay('seyric-field-edit-contrast', steps)
    expect(bypass === null || !isBlank(bypass)).toBe(true)

    const start = puzzleDiagram('seyric-field-edit-contrast')
    expect(() => applyStep(start, stepFromJson({
      rule: 'erasure',
      sel: { region: 'r10', regions: [], nodes: ['n3'], wires: [] },
    }), context, 'backward')).toThrow(/negative region/)

    const copiedWithoutEdit = applyStep(start, stepFromJson({
      rule: 'iteration',
      sel: { region: 'r18', regions: ['r5'], nodes: [], wires: [] },
      target: 'r9',
    }), context, 'backward')
    const copiedSelection = { region: 'r5_0', regions: ['r6_0'], nodes: [], wires: [] }
    expect(() => deiterationStep(copiedWithoutEdit, copiedSelection))
      .toThrow(/no justifying occurrence/)

    const edited = applyStep(start, stepFromJson({
      rule: 'erasure',
      sel: { region: 'r6', regions: [], nodes: ['n7'], wires: [] },
    }), context, 'backward')
    const copiedAfterEdit = applyStep(edited, stepFromJson({
      rule: 'iteration',
      sel: { region: 'r18', regions: ['r5'], nodes: [], wires: [] },
      target: 'r9',
    }), context, 'backward')
    expect(() => applyStep(
      copiedAfterEdit,
      deiterationStep(copiedAfterEdit, copiedSelection),
      context,
      'backward',
    )).not.toThrow()
  })

  it('does not admit elimination of the existing annulus as an atomic-wrapping bypass', () => {
    const bypass = attempt('seyric-atomic-double-cut-selection', (start) => {
      const staticSteps = [
        stepFromJson({ rule: 'doubleCutElim', region: 'r5' }),
        null,
        stepFromJson({
          rule: 'erasure',
          sel: { region: 'r3', regions: [], nodes: ['n2', 'n3', 'n4'], wires: [] },
        }),
        stepFromJson({ rule: 'vacuousElim', region: 'r3' }),
        stepFromJson({ rule: 'vacuousElim', region: 'r2' }),
        stepFromJson({ rule: 'doubleCutElim', region: 'r1' }),
      ] as const
      let diagram = applyStep(start, staticSteps[0], context, 'backward')
      diagram = applyStep(diagram, deiterationStep(diagram, {
        region: 'r4', regions: [], nodes: ['n0'], wires: [],
      }), context, 'backward')
      for (const step of staticSteps.slice(2)) diagram = applyStep(diagram, step!, context, 'backward')
      return diagram
    })
    expect(bypass === null || !isBlank(bypass)).toBe(true)

    const witness = solutionSteps(content<ValidationFile>('validation/seyric-atomic-double-cut-selection.json'))
      .filter((_, index) => index !== 1 && index !== 4)
    const noWrap = attemptReplay('seyric-atomic-double-cut-selection', witness)
    expect(noWrap === null || !isBlank(noWrap)).toBe(true)
  })

  it('makes only the exact atomic double-cut useful to the continuation', () => {
    const opened = applyStep(
      puzzleDiagram('seyric-atomic-double-cut-selection'),
      stepFromJson({ rule: 'doubleCutElim', region: 'r5' }),
      context,
      'backward',
    )
    const wrap = (nodes: readonly string[]) => applyStep(opened, stepFromJson({
      rule: 'doubleCutIntro',
      sel: { region: 'r8', regions: [], nodes, wires: [] },
    }), context, 'backward')
    const continueToAtomicUse = (diagram: ReturnType<typeof puzzleDiagram>) => {
      const targetOpened = applyStep(
        diagram,
        stepFromJson({ rule: 'doubleCutElim', region: 'r9' }),
        context,
        'backward',
      )
      const supportSelection = { region: 'r11', regions: ['r12'], nodes: [], wires: [] }
      const supportPrepared = applyStep(
        targetOpened,
        deiterationStep(targetOpened, supportSelection),
        context,
        'backward',
      )
      const atomicSelection = { region: 'r8', regions: ['dc'], nodes: [], wires: [] }
      return applyStep(
        supportPrepared,
        deiterationStep(supportPrepared, atomicSelection),
        context,
        'backward',
      )
    }

    expect(() => continueToAtomicUse(wrap(['n1']))).not.toThrow()
    expect(() => continueToAtomicUse(wrap(['n2']))).toThrow(/no justifying occurrence/)
    expect(() => continueToAtomicUse(wrap(['n1', 'n2']))).toThrow(/no justifying occurrence/)
  })

  it('makes intact compound copying semantically different from atom-by-atom copying', () => {
    const start = puzzleDiagram('seyric-compound-copy-authority')
    const exact = applyStep(start, stepFromJson({
      rule: 'iteration',
      sel: { region: 'r18', regions: ['r5'], nodes: [], wires: [] },
      target: 'r9',
    }), context, 'backward')
    const nearby = applyStep(start, stepFromJson({
      rule: 'iteration',
      sel: { region: 'r18', regions: ['r5'], nodes: [], wires: [] },
      target: 'r12',
    }), context, 'backward')

    expect(exploreForm(exact)).not.toBe(exploreForm(nearby))
    for (const [region, node] of [['r15', 'n0'], ['r7', 'n1']] as const) {
      expect(() => applyStep(start, stepFromJson({
        rule: 'iteration',
        sel: { region, regions: [], nodes: [node], wires: [] },
        target: 'r9',
      }), context, 'backward')).toThrow(/must lie within the source region/)
    }
    expect(() => applyStep(start, stepFromJson({
      rule: 'iteration',
      sel: { region: 'r5', regions: ['r6'], nodes: [], wires: [] },
      target: 'r9',
    }), context, 'backward')).toThrow(/must lie within the source region/)

    const exactSelection = { region: 'r5_0', regions: ['r6_0'], nodes: [], wires: [] }
    expect(() => applyStep(
      exact,
      deiterationStep(exact, exactSelection),
      context,
      'backward',
    )).not.toThrow()

    const withoutFirstCopy = solutionSteps(content<ValidationFile>('validation/seyric-compound-copy-authority.json'))
      .filter((_, index) => index > 5)
    const bypass = attemptReplay('seyric-compound-copy-authority', withoutFirstCopy)
    expect(bypass === null || !isBlank(bypass)).toBe(true)
  })
})
