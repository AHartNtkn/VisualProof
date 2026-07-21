import { readFileSync, readdirSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { artifactTheoremContext, artifactTheoremName } from '../../src/game/artifact-theorem'
import { isBlank } from '../../src/game/blank'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { puzzleId, type CompletedArtifact, type PuzzleId } from '../../src/game/types'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { actionFromJson } from '../../src/kernel/proof/json'
import type { ProofStep } from '../../src/kernel/proof/step'

type ArtifactEvidence = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
}

const catalog = loadGameContent(gameContentFiles)
const allEvidence = readdirSync(resolve(process.cwd(), 'content/validation'))
  .filter((name) => name.endsWith('.json'))
  .map((name) => JSON.parse(readFileSync(
    resolve(process.cwd(), 'content/validation', name),
    'utf8',
  )) as ArtifactEvidence)
  .map((sidecar) => ({
    ...sidecar,
    actions: sidecar.solution.map((action) => actionFromJson(action)),
  }))

const evidence = allEvidence
  .filter(({ availableArtifacts, actions }) =>
    availableArtifacts.length > 0 || actions.some((action) =>
      action.steps.some((step) => step.rule === 'theorem')))
  .sort((left, right) => left.puzzle.localeCompare(right.puzzle))

const completedArtifacts = (ids: readonly string[]): ReadonlyMap<PuzzleId, CompletedArtifact> =>
  new Map(ids.map((rawId) => {
    const puzzle = puzzleId(rawId)
    const sidecar = allEvidence.find((candidate) => candidate.puzzle === rawId)
    if (sidecar === undefined) throw new Error(`missing validation evidence for completed artifact '${rawId}'`)
    return [puzzle, { puzzle, actions: sidecar.actions }] as const
  }))

const prerequisiteClosure = (id: PuzzleId): ReadonlySet<PuzzleId> => {
  const closure = new Set<PuzzleId>()
  const add = (next: PuzzleId): void => {
    if (closure.has(next)) return
    closure.add(next)
    for (const parent of catalog.placement(next).prerequisites) add(parent)
  }
  for (const parent of catalog.placement(id).prerequisites) add(parent)
  return closure
}

const theoremSteps = (actions: readonly ProofAction[]): readonly Extract<ProofStep, { rule: 'theorem' }>[] =>
  actions.flatMap(({ steps }) => steps)
    .filter((step): step is Extract<ProofStep, { rule: 'theorem' }> => step.rule === 'theorem')

describe('completed-artifact validation dependency replay', () => {
  it('keeps the complete artifact-bearing witness inventory dependency-closed', () => {
    expect(evidence.map(({ puzzle }) => puzzle)).toEqual([
      'artifact-creates-copy-authority',
      'artifact-polarity-direction-contrast',
      'artifact-preserves-copy-authority',
      'artifact-selected-downstream-bridge',
      'compound-context-dissolution',
      'compound-theorem-source-choice',
      'sey-ref-dis-i01',
      'sey-ref-sel-i01',
      'useful-manifestation-target',
    ])

    for (const sidecar of evidence) {
      const puzzle = puzzleId(sidecar.puzzle)
      const available = completedArtifacts(sidecar.availableArtifacts)
      const closure = prerequisiteClosure(puzzle)
      const context = artifactTheoremContext(catalog, available)

      for (const artifact of available.keys()) {
        expect(closure.has(artifact), `${puzzle} prerequisite closure contains ${artifact}`).toBe(true)
        expect(context.theorems.has(artifactTheoremName(artifact)), `${puzzle} exposes ${artifact}`).toBe(true)
      }
      for (const step of theoremSteps(sidecar.actions)) {
        expect(
          context.theorems.has(step.name),
          `${puzzle} declares theorem dependency ${step.name}`,
        ).toBe(true)
      }
    }
  })

  it('replays every artifact-bearing witness exactly against current completed artifacts', () => {
    for (const sidecar of evidence) {
      const puzzle = puzzleId(sidecar.puzzle)
      const available = completedArtifacts(sidecar.availableArtifacts)
      const context = artifactTheoremContext(catalog, available)
      let diagram = catalog.puzzle(puzzle).diagram

      for (const [index, action] of sidecar.actions.entries()) {
        expect(() => {
          diagram = applyAction(diagram, action, context, 'backward')
        }, `${puzzle} action ${index} (${action.label})`).not.toThrow()
      }
      expect(isBlank(diagram), `${puzzle} reaches canonical blank`).toBe(true)
    }
  })
})
