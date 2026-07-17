import type { GameCatalog } from './catalog'
import { stepFromJson, stepToJson } from '../kernel/proof/json'
import { artifactTheoremContext } from './artifact-theorem'
import { emptyProgress, isUnlocked, recordCompletion, type GameProgress } from './progress'
import { applyGameStep, moveCursor, startPuzzle, type GameRuntimeAuthority, type GameSession } from './session'
import { GameDomainError, type GameStep, type PuzzleId } from './types'

export type SerializedGameStep = Readonly<Record<string, unknown>>

export type GameSaveV2 = {
  readonly format: 'cursebreaker-save'
  readonly version: 2
  readonly puzzleFingerprints: Readonly<Record<string, string>>
  readonly completed: readonly PuzzleId[]
  readonly active?: {
    readonly puzzle: PuzzleId
    readonly steps: readonly SerializedGameStep[]
    readonly cursor: number
  }
}

export type LoadedGame = {
  readonly progress: GameProgress
  readonly active: GameSession | null
}

const record = (value: unknown, label: string): Record<string, unknown> => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  return value as Record<string, unknown>
}

const gameStepToJson = (step: GameStep): SerializedGameStep =>
  record(stepToJson(step), 'serialized kernel step')

const gameStepFromJson = (value: unknown, index: number): GameStep => {
  try {
    return stepFromJson(value)
  } catch (error) {
    throw new GameDomainError(
      `invalid game step at index ${index}: ${error instanceof Error ? error.message : String(error)}`,
    )
  }
}

export function saveGame(
  catalog: GameCatalog,
  progress: GameProgress,
  active: GameSession | null,
): GameSaveV2 {
  const referenced = new Set<PuzzleId>(progress.completed)
  if (active !== null) referenced.add(active.puzzle)
  const puzzleFingerprints = Object.fromEntries(
    [...referenced].sort().map((id) => [id, catalog.puzzleFingerprint(id)]),
  )
  const base = {
    format: 'cursebreaker-save' as const,
    version: 2 as const,
    puzzleFingerprints,
    completed: [...progress.completed].sort(),
  }
  return active === null ? base : {
    ...base,
    active: {
      puzzle: active.puzzle,
      steps: active.timeline.steps.map(gameStepToJson),
      cursor: active.timeline.cursor,
    },
  }
}

export function loadGame(catalog: GameCatalog, value: unknown): LoadedGame {
  const root = record(value, 'save')
  if (root.format !== 'cursebreaker-save' || root.version !== 2) {
    throw new GameDomainError('unsupported game save format or version')
  }
  const savedFingerprints = record(root.puzzleFingerprints, 'save puzzleFingerprints')
  const verifyFingerprint = (id: PuzzleId): void => {
    catalog.puzzle(id)
    if (savedFingerprints[id] !== catalog.puzzleFingerprint(id)) {
      throw new GameDomainError(`save puzzle logical fingerprint does not match '${id}'`)
    }
  }
  if (!Array.isArray(root.completed) || !root.completed.every((id) => typeof id === 'string')) {
    throw new GameDomainError('save completed must be an array of puzzle ids')
  }
  let progress = emptyProgress()
  for (const raw of root.completed) {
    const id = raw as PuzzleId
    verifyFingerprint(id)
    progress = recordCompletion(progress, id)
  }
  if (root.active === undefined) return { progress, active: null }

  const active = record(root.active, 'save active session')
  if (typeof active.puzzle !== 'string' || !Array.isArray(active.steps)
    || typeof active.cursor !== 'number' || !Number.isInteger(active.cursor)) {
    throw new GameDomainError('save active session has invalid puzzle, steps, or cursor')
  }
  const puzzle = catalog.puzzle(active.puzzle as PuzzleId)
  verifyFingerprint(puzzle.id)
  if (!isUnlocked(catalog, progress, puzzle.id)) {
    throw new GameDomainError(`active puzzle '${puzzle.id}' is locked by incomplete prerequisites`)
  }
  const steps = active.steps.map(gameStepFromJson)
  const authority: GameRuntimeAuthority = {
    context: artifactTheoremContext(
      catalog.source.puzzles,
      progress.completed,
      catalog.source.context,
    ),
  }
  let session = startPuzzle(puzzle)
  for (const step of steps) session = applyGameStep(session, step, authority).session
  const cursor = active.cursor as number
  if (cursor < 0 || cursor > steps.length) {
    throw new GameDomainError(`save active cursor ${cursor} is outside 0..${steps.length}`)
  }
  session = moveCursor(session, cursor)
  return { progress, active: session }
}
