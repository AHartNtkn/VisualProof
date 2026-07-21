import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { gameSessionActionFromJson } from '../../src/game/action'
import { isBlank } from '../../src/game/blank'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import {
  applyGameAction,
  currentDiagram,
  isArtifactAction,
  startPuzzle,
  type GameSessionAction,
} from '../../src/game/session'
import { puzzleId } from '../../src/game/types'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { polarity } from '../../src/kernel/diagram/regions'
import { singleStepAction } from '../../src/kernel/proof/action'
import type { ProofStep } from '../../src/kernel/proof/step'
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'

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
const actions = (id: string): readonly GameSessionAction[] => readValidation(id).solution
  .map((action, index) => gameSessionActionFromJson(action, `${id} solution action ${index}`))

const replay = (
  puzzle: string,
  start: Diagram,
  sequence: readonly GameSessionAction[],
  artifacts: readonly string[],
): Diagram => {
  const available = new Set(artifacts.map(puzzleId))
  let session = startPuzzle({ id: puzzleId(puzzle), diagram: start })
  for (const action of sequence) {
    session = applyGameAction(session, action, {
      context: catalog.context,
      artifact: (id) => available.has(id) ? catalog.puzzle(id) : undefined,
    }).session
  }
  return currentDiagram(session)
}

const replayAttempt = (
  puzzle: string,
  start: Diagram,
  sequence: readonly GameSessionAction[],
  artifacts: readonly string[],
): Diagram | null => {
  try { return replay(puzzle, start, sequence, artifacts) } catch { return null }
}

const failsOrRemains = (attempt: Diagram | null): boolean =>
  attempt === null || !isBlank(attempt)

const proof = (step: ProofStep): GameSessionAction => singleStepAction(step.rule, step)

describe('Myratic artifact collision redesigns', () => {
  it('derives the useful compound source by changing a proper subcomponent of a manifested catalog artifact', () => {
    const id = 'compound-theorem-source-choice'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const validation = readValidation(id)
    const sequence = actions(id)
    const manifestation = sequence[0]
    const sourceTransformation = sequence[1]
    const sourceUse = sequence[2]

    expect(validation.availableArtifacts).toEqual(['sey-lem-i01', 'sey-lem-c01'])
    expect(manifestation).toEqual({
      kind: 'artifactManifest', artifact: puzzleId('sey-lem-c01'), region: 'continuation-outer',
    })
    expect(sourceTransformation).toMatchObject({
      label: 'doubleCutElim', steps: [{ rule: 'doubleCutElim', region: 'r8' }],
    })
    expect(sourceUse).toMatchObject({
      label: 'deiteration',
      steps: [{
        rule: 'deiteration',
        sel: { region: 'continuation-inner', regions: ['target-outer'] },
      }],
    })
    expect(isBlank(replay(id, start, sequence, validation.availableArtifacts))).toBe(true)

    if (manifestation === undefined || sourceTransformation === undefined || sourceUse === undefined) {
      throw new Error('expected manifested source, transformation, and use')
    }
    const afterManifest = replay(id, start, [manifestation], validation.availableArtifacts)
    expect(afterManifest.regions.r8).toMatchObject({ kind: 'cut' })
    expect(() => replay(id, afterManifest, [sourceUse], validation.availableArtifacts)).toThrow()
    const transformed = replay(id, afterManifest, [sourceTransformation], validation.availableArtifacts)
    expect(() => replay(id, transformed, [sourceUse], validation.availableArtifacts)).not.toThrow()

    expect(failsOrRemains(replayAttempt(
      id,
      start,
      sequence.filter((_, index) => index !== 1),
      validation.availableArtifacts,
    ))).toBe(true)

    const nearSource = sequence.map((action, index): GameSessionAction =>
      index === 0 && isArtifactAction(action)
        ? { ...action, artifact: puzzleId('sey-lem-i01') }
        : action)
    expect(failsOrRemains(replayAttempt(id, start, nearSource, validation.availableArtifacts)))
      .toBe(true)
  })

  it('offers an authored route using game-owned manifestation and exact dissolution', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const validation = readValidation(id)
    const sequence = actions(id)
    const forwardIndex = sequence.findIndex((action) =>
      isArtifactAction(action) && action.kind === 'artifactManifest')
    const reverseIndex = sequence.findIndex((action) =>
      isArtifactAction(action) && action.kind === 'artifactDissolve')

    expect(validation.availableArtifacts).toEqual(['two-mark-projection'])
    expect(sequence[forwardIndex]).toEqual({
      kind: 'artifactManifest', artifact: puzzleId('two-mark-projection'), region: 'manifest-host',
    })
    expect(sequence[reverseIndex]).toMatchObject({
      kind: 'artifactDissolve',
      artifact: puzzleId('two-mark-projection'),
      selection: { region: 'workspace', regions: ['dissolve-outer'] },
    })
    expect(polarity(start, 'manifest-host')).toBe('negative')
    expect(polarity(start, 'workspace')).toBe('positive')
    expect(reverseIndex).toBeGreaterThan(forwardIndex)
    expect(isBlank(replay(id, start, sequence, validation.availableArtifacts))).toBe(true)

    for (const index of [forwardIndex, reverseIndex]) {
      expect(failsOrRemains(replayAttempt(
        id,
        start,
        sequence.filter((_, candidate) => candidate !== index),
        validation.availableArtifacts,
      ))).toBe(true)
    }
  })

  it('accepts reconstructing the continuation target as an open-ended all-dissolution solution', () => {
    const id = 'compound-theorem-source-choice'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const alternative: readonly GameSessionAction[] = [
      proof({
        rule: 'doubleCutIntro',
        sel: {
          region: 'target-branch',
          regions: [],
          nodes: ['target-open-x', 'target-open-y', 'target-open-z'],
          wires: [],
        },
      }),
      {
        kind: 'artifactDissolve',
        artifact: puzzleId('sey-lem-c01'),
        selection: {
          region: 'continuation-inner', regions: ['target-outer'], nodes: [], wires: [],
        },
      },
      proof({ rule: 'doubleCutElim', region: 'continuation-outer' }),
      proof({ rule: 'doubleCutElim', region: 'outer' }),
    ]

    expect(isBlank(replay(id, start, alternative, artifacts))).toBe(true)
  })

  it('accepts a disposable manifested ancestor copy as an open-ended alternative', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const available = new Set(artifacts.map(puzzleId))
    let session = startPuzzle({ id: puzzleId(id), diagram: start })
    const append = (action: GameSessionAction): void => {
      session = applyGameAction(session, action, {
        context: catalog.context,
        artifact: (artifact) => available.has(artifact) ? catalog.puzzle(artifact) : undefined,
      }).session
    }
    const deiterate = (sel: Extract<ProofStep, { rule: 'deiteration' }>['sel']): void => {
      const diagram = currentDiagram(session)
      append(proof({
        rule: 'deiteration', sel, ...findDeiterationEvidence(diagram, sel, 100),
      }))
    }

    append({
      kind: 'artifactManifest', artifact: puzzleId('two-mark-projection'), region: 'manifest-host',
    })
    deiterate({ region: 'r4', regions: [], nodes: ['n2'], wires: [] })
    deiterate({ region: 'continuation-host', regions: ['repeat-outer'], nodes: [], wires: [] })
    append(proof({
      rule: 'erasure',
      sel: { region: 'manifest-host', regions: ['r1'], nodes: [], wires: [] },
    }))
    append(proof({ rule: 'doubleCutElim', region: 'manifest-host' }))
    append({
      kind: 'artifactManifest', artifact: puzzleId('two-mark-projection'), region: 'outer',
    })
    deiterate({ region: 'workspace', regions: ['dissolve-outer'], nodes: [], wires: [] })
    append(proof({
      rule: 'erasure',
      sel: { region: 'outer', regions: ['r1'], nodes: [], wires: [] },
    }))
    append(proof({ rule: 'doubleCutElim', region: 'outer' }))

    expect(isBlank(currentDiagram(session))).toBe(true)
  })

  it('accepts rebuilding the manifested target as an open-ended all-dissolution solution', () => {
    const id = 'artifact-polarity-direction-contrast'
    const start = catalog.puzzle(puzzleId(id)).diagram
    const artifacts = readValidation(id).availableArtifacts
    const alternative: readonly GameSessionAction[] = [
      proof({
        rule: 'iteration',
        sel: { region: 'repeat-y', regions: [], nodes: ['repeat-x-open'], wires: [] },
        target: 'repeat-mark',
      }),
      {
        kind: 'artifactDissolve',
        artifact: puzzleId('two-mark-projection'),
        selection: {
          region: 'continuation-host', regions: ['repeat-outer'], nodes: [], wires: [],
        },
      },
      proof({ rule: 'doubleCutElim', region: 'manifest-host' }),
      {
        kind: 'artifactDissolve',
        artifact: puzzleId('two-mark-projection'),
        selection: {
          region: 'workspace', regions: ['dissolve-outer'], nodes: [], wires: [],
        },
      },
      proof({ rule: 'doubleCutElim', region: 'outer' }),
    ]

    expect(isBlank(replay(id, start, alternative, artifacts))).toBe(true)
  })

  it('keeps both starts canonically distinct from one another and the target-choice problem', () => {
    const sourceChoice = catalog.puzzle(puzzleId('compound-theorem-source-choice')).diagram
    const polarityDiagram = catalog.puzzle(puzzleId('artifact-polarity-direction-contrast')).diagram
    const targetChoice = catalog.puzzle(puzzleId('useful-manifestation-target')).diagram

    expect(exploreForm(sourceChoice)).not.toBe(exploreForm(polarityDiagram))
    expect(exploreForm(polarityDiagram)).not.toBe(exploreForm(targetChoice))
  })
})
