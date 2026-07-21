import { readFileSync, readdirSync } from 'node:fs'
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
} from '../../src/game/session'
import { puzzleId, type PuzzleId } from '../../src/game/types'

type ArtifactEvidence = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
}

const catalog = loadGameContent(gameContentFiles)
const evidence = readdirSync(resolve(process.cwd(), 'content/validation'))
  .filter((name) => name.endsWith('.json'))
  .map((name) => JSON.parse(readFileSync(
    resolve(process.cwd(), 'content/validation', name),
    'utf8',
  )) as ArtifactEvidence)
  .map((sidecar) => ({
    ...sidecar,
    actions: sidecar.solution.map((action, index) =>
      gameSessionActionFromJson(action, `${sidecar.puzzle} action ${index}`)),
  }))
  .filter(({ availableArtifacts, actions }) =>
    availableArtifacts.length > 0 || actions.some(isArtifactAction))
  .sort((left, right) => left.puzzle.localeCompare(right.puzzle))

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

describe('catalog artifact dependencies', () => {
  it('keeps every artifact-bearing authored witness dependency-closed and explicitly declared', () => {
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
      const available = new Set(sidecar.availableArtifacts.map(puzzleId))
      const closure = prerequisiteClosure(puzzle)
      for (const artifact of available) {
        expect(closure.has(artifact), `${puzzle} prerequisite closure contains ${artifact}`).toBe(true)
      }
      for (const action of sidecar.actions.filter(isArtifactAction)) {
        expect(
          available.has(action.artifact),
          `${puzzle} declares artifact dependency ${action.artifact}`,
        ).toBe(true)
      }
    }
  })

  it('replays every artifact-bearing authored witness using only its declared catalog artifacts', () => {
    for (const sidecar of evidence) {
      const puzzle = puzzleId(sidecar.puzzle)
      const available = new Set(sidecar.availableArtifacts.map(puzzleId))
      let session = startPuzzle(catalog.puzzle(puzzle))
      for (const [index, action] of sidecar.actions.entries()) {
        expect(() => {
          session = applyGameAction(session, action, {
            context: catalog.context,
            artifact: (id) => available.has(id) ? catalog.puzzle(id) : undefined,
          }).session
        }, `${puzzle} action ${index}`).not.toThrow()
      }
      expect(isBlank(currentDiagram(session)), `${puzzle} reaches canonical blank`).toBe(true)
    }
  })
})
