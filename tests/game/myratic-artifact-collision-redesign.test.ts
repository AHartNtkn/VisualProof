import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { artifactTheoremContext, artifactTheoremName } from '../../src/game/artifact-theorem'
import { isBlank } from '../../src/game/blank'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { puzzleId } from '../../src/game/types'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { polarity } from '../../src/kernel/diagram/regions'
import { stepFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}

const catalog = loadGameContent(gameContentFiles)
const readValidation = (id: string): ValidationFile => JSON.parse(readFileSync(
  resolve(process.cwd(), 'content', 'validation', `${id}.json`),
  'utf8',
)) as ValidationFile
const witness = (id: string): readonly ProofStep[] => readValidation(id).solution.map(stepFromJson)
const contextFor = (artifacts: readonly string[]) => artifactTheoremContext(
  catalog,
  new Set(artifacts.map(puzzleId)),
)
const replay = (start: Diagram, steps: readonly ProofStep[], artifacts: readonly string[]): Diagram =>
  steps.reduce((diagram, step) => applyStep(diagram, step, contextFor(artifacts), 'backward'), start)
const replayAttempt = (
  start: Diagram,
  steps: readonly ProofStep[],
  artifacts: readonly string[],
): Diagram | null => {
  try {
    return replay(start, steps, artifacts)
  } catch {
    return null
  }
}
const failsOrRemains = (attempt: Diagram | null): boolean => attempt === null || !isBlank(attempt)

const theoremStep = (
  name: string,
  direction: 'forward' | 'reverse',
  region: string,
  regions: readonly string[] = [],
): ProofStep => stepFromJson({
  rule: 'theorem',
  name: artifactTheoremName(puzzleId(name)),
  at: { sel: { region, regions, nodes: [], wires: [] }, args: [] },
  direction,
})

describe('Myratic artifact collision redesigns', () => {
  it('derives the useful compound source by changing a proper subcomponent of the manifested artifact', () => {
    const id = 'compound-theorem-source-choice'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const validation = readValidation(id)
    const steps = witness(id)
    const theoremIndex = steps.findIndex((step) => step.rule === 'theorem')
    const sourceTransformation = steps[theoremIndex + 1]
    const sourceUse = steps[theoremIndex + 2]

    expect(validation.availableArtifacts).toEqual(['sey-lem-i01', 'sey-lem-c01'])
    expect(steps[theoremIndex]).toMatchObject({
      rule: 'theorem',
      name: artifactTheoremName(puzzleId('sey-lem-c01')),
      direction: 'forward',
    })
    expect(sourceTransformation).toMatchObject({ rule: 'doubleCutElim', region: 'r8' })
    expect(sourceUse).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'continuation-inner', regions: ['target-outer'] },
    })
    expect(isBlank(replay(start, steps, validation.availableArtifacts))).toBe(true)

    if (steps[theoremIndex]?.rule !== 'theorem' || sourceTransformation === undefined || sourceUse === undefined) {
      throw new Error('expected a manifested source, proper-subcomponent transformation, and source use')
    }
    const manifested = applyStep(
      start,
      steps[theoremIndex],
      contextFor(validation.availableArtifacts),
      'backward',
    )
    expect(manifested.regions.r1?.kind).toBe('cut')
    const properComponent = manifested.regions.r8
    expect(properComponent?.kind).toBe('cut')
    if (properComponent === undefined || properComponent.kind === 'sheet') {
      throw new Error('expected the manifested source to contain proper region r8')
    }
    expect(properComponent.parent).not.toBe(manifested.root)
    expect(() => applyStep(
      manifested,
      sourceUse,
      contextFor(validation.availableArtifacts),
      'backward',
    )).toThrow()
    const transformed = applyStep(
      manifested,
      sourceTransformation,
      contextFor(validation.availableArtifacts),
      'backward',
    )
    expect(() => applyStep(
      transformed,
      sourceUse,
      contextFor(validation.availableArtifacts),
      'backward',
    )).not.toThrow()

    const withoutProperTransformation = steps.filter((_, index) => index !== theoremIndex + 1)
    expect(failsOrRemains(replayAttempt(start, withoutProperTransformation, validation.availableArtifacts))).toBe(true)

    const withNearSource = steps.map((step, index) => index === theoremIndex && step.rule === 'theorem'
      ? { ...step, name: artifactTheoremName(puzzleId('sey-lem-i01')) }
      : step)
    expect(failsOrRemains(replayAttempt(start, withNearSource, validation.availableArtifacts))).toBe(true)
  })

  it('accepts reconstructing the continuation target as an open-ended all-reverse solution', () => {
    const id = 'compound-theorem-source-choice'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const bypass = [
      stepFromJson({
        rule: 'doubleCutIntro',
        sel: {
          region: 'target-branch',
          regions: [],
          nodes: ['target-open-x', 'target-open-y', 'target-open-z'],
          wires: [],
        },
      }),
      theoremStep('sey-lem-c01', 'reverse', 'continuation-inner', ['target-outer']),
      stepFromJson({ rule: 'doubleCutElim', region: 'continuation-outer' }),
      stepFromJson({ rule: 'doubleCutElim', region: 'outer' }),
    ]

    expect(isBlank(replay(start, bypass, artifacts))).toBe(true)
  })

  it('offers an authored route using forward manifestation and reverse exact dissolution', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const validation = readValidation(id)
    const steps = witness(id)
    const forwardIndex = steps.findIndex((step) => step.rule === 'theorem' && step.direction === 'forward')
    const reverseIndex = steps.findIndex((step) => step.rule === 'theorem' && step.direction === 'reverse')

    expect(validation.availableArtifacts).toEqual(['two-mark-projection'])
    expect(forwardIndex).toBeGreaterThanOrEqual(0)
    expect(reverseIndex).toBeGreaterThan(forwardIndex)
    expect(steps.slice(forwardIndex + 1, reverseIndex).some((step) => step.rule === 'deiteration')).toBe(true)
    expect(steps[forwardIndex]).toMatchObject({
      rule: 'theorem',
      direction: 'forward',
      at: { sel: { region: 'manifest-host', regions: [] } },
    })
    expect(steps[forwardIndex + 1]).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r4', regions: [], nodes: ['n2'] },
    })
    expect(steps[forwardIndex + 2]).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'continuation-host', regions: ['repeat-outer'] },
    })
    expect(steps[reverseIndex]).toMatchObject({
      rule: 'theorem',
      direction: 'reverse',
      at: { sel: { region: 'workspace', regions: ['dissolve-outer'] } },
    })
    expect(start.regions['repeat-outer']).toMatchObject({ parent: 'continuation-host' })
    expect(start.regions['dissolve-outer']).toMatchObject({ parent: 'workspace' })
    expect(polarity(start, 'manifest-host')).toBe('negative')
    expect(polarity(start, 'continuation-host')).toBe('positive')
    expect(polarity(start, 'workspace')).toBe('positive')
    expect(isBlank(replay(start, steps, validation.availableArtifacts))).toBe(true)

    expect(() => applyStep(start, stepFromJson({
      rule: 'erasure',
      sel: { region: 'continuation-host', regions: ['repeat-outer'], nodes: [], wires: [] },
    }), contextFor(validation.availableArtifacts), 'backward')).toThrow()

    const forward = steps[forwardIndex]
    const sourceTransformation = steps[forwardIndex + 1]
    const sourceUse = steps[forwardIndex + 2]
    if (forward === undefined || sourceTransformation === undefined || sourceUse === undefined) {
      throw new Error('expected manifestation, internal transformation, and continuation use')
    }
    const manifested = applyStep(start, forward, contextFor(validation.availableArtifacts), 'backward')
    expect(() => applyStep(manifested, sourceUse, contextFor(validation.availableArtifacts), 'backward')).toThrow()
    const transformed = applyStep(manifested, sourceTransformation, contextFor(validation.availableArtifacts), 'backward')
    expect(() => applyStep(transformed, sourceUse, contextFor(validation.availableArtifacts), 'backward')).not.toThrow()

    const withoutForward = steps.filter((_, index) => index !== forwardIndex)
    const withoutSourceTransformation = steps.filter((_, index) => index !== forwardIndex + 1)
    const withoutReverse = steps.filter((_, index) => index !== reverseIndex)
    expect(failsOrRemains(replayAttempt(start, withoutForward, validation.availableArtifacts))).toBe(true)
    expect(failsOrRemains(replayAttempt(start, withoutSourceTransformation, validation.availableArtifacts))).toBe(true)
    expect(failsOrRemains(replayAttempt(start, withoutReverse, validation.availableArtifacts))).toBe(true)

    for (const index of [forwardIndex, reverseIndex]) {
      const swapped = steps.map((step, stepIndex) => stepIndex === index && step.rule === 'theorem'
        ? { ...step, direction: step.direction === 'forward' ? 'reverse' as const : 'forward' as const }
        : step)
      expect(failsOrRemains(replayAttempt(start, swapped, validation.availableArtifacts))).toBe(true)
    }
  })

  it('accepts a disposable forward ancestor copy as an open-ended all-forward solution', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const bypass = [
      theoremStep('two-mark-projection', 'forward', 'manifest-host'),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'r4', regions: [], nodes: ['n2'], wires: [] },
        fuel: 100,
      }),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'continuation-host', regions: ['repeat-outer'], nodes: [], wires: [] },
        fuel: 100,
      }),
      stepFromJson({
        rule: 'erasure',
        sel: { region: 'manifest-host', regions: ['r1'], nodes: [], wires: [] },
      }),
      stepFromJson({ rule: 'doubleCutElim', region: 'manifest-host' }),
      theoremStep('two-mark-projection', 'forward', 'outer'),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'workspace', regions: ['dissolve-outer'], nodes: [], wires: [] },
        fuel: 100,
      }),
      stepFromJson({
        rule: 'erasure',
        sel: { region: 'outer', regions: ['r1'], nodes: [], wires: [] },
      }),
      stepFromJson({ rule: 'doubleCutElim', region: 'outer' }),
    ]

    expect(isBlank(replay(start, bypass, artifacts))).toBe(true)
  })

  it('accepts rebuilding the forward-derived target as an open-ended all-reverse solution', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const bypass = [
      stepFromJson({
        rule: 'iteration',
        sel: { region: 'repeat-y', regions: [], nodes: ['repeat-x-open'], wires: [] },
        target: 'repeat-mark',
      }),
      theoremStep('two-mark-projection', 'reverse', 'continuation-host', ['repeat-outer']),
      stepFromJson({ rule: 'doubleCutElim', region: 'manifest-host' }),
      theoremStep('two-mark-projection', 'reverse', 'workspace', ['dissolve-outer']),
      stepFromJson({ rule: 'doubleCutElim', region: 'outer' }),
    ]

    expect(isBlank(replay(start, bypass, artifacts))).toBe(true)
  })

  it('keeps both starts canonically distinct from one another and the displaced target-choice problem', () => {
    const sourceChoice = catalog.puzzle(puzzleId('compound-theorem-source-choice')).diagram
    const polarity = catalog.puzzle(puzzleId('artifact-polarity-direction-contrast')).diagram
    const targetChoice = catalog.puzzle(puzzleId('useful-manifestation-target')).diagram

    expect(exploreForm(sourceChoice)).not.toBe(exploreForm(polarity))
    expect(exploreForm(polarity)).not.toBe(exploreForm(targetChoice))
  })
})
