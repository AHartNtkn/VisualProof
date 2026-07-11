import type { GameCatalog } from './catalog'
import { stepFromJson } from '../kernel/proof/json'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { emptyProgress, isUnlocked, recordCompletion, type GameProgress } from './progress'
import { applyGameStep, moveCursor, startPuzzle, type GameRuntimeAuthority, type GameSession } from './session'
import { GameDomainError, puzzleId, type GameStep, type PuzzleId } from './types'

export type GameSaveV1 = {
  readonly format: 'cursebreaker-save'
  readonly version: 1
  readonly catalogFingerprint: string
  readonly completed: readonly PuzzleId[]
  readonly active?: {
    readonly puzzle: PuzzleId
    readonly steps: readonly GameStep[]
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

const onlyKeys = (value: Record<string, unknown>, allowed: readonly string[], label: string): void => {
  for (const key of Object.keys(value)) {
    if (!allowed.includes(key)) throw new GameDomainError(`${label} has unknown field '${key}'`)
  }
}

const string = (value: unknown, label: string): string => {
  if (typeof value !== 'string') throw new GameDomainError(`${label} must be a string`)
  return value
}

const strings = (value: unknown, label: string): string[] => {
  if (!Array.isArray(value)) throw new GameDomainError(`${label} must be an array`)
  return value.map((item, index) => string(item, `${label}[${index}]`))
}

const selection = (value: unknown): SubgraphSelection => {
  const decoded = record(value, 'vellum selection')
  onlyKeys(decoded, ['region', 'regions', 'nodes', 'wires'], 'vellum selection')
  return {
    region: string(decoded.region, 'vellum selection.region'),
    regions: strings(decoded.regions, 'vellum selection.regions'),
    nodes: strings(decoded.nodes, 'vellum selection.nodes'),
    wires: strings(decoded.wires, 'vellum selection.wires'),
  }
}

const gameStepFromJson = (value: unknown, index: number): GameStep => {
  try {
    const step = record(value, 'game step')
    const rule = string(step.rule, 'game step.rule')
    if (rule === 'vellumManifest') {
      onlyKeys(step, ['rule', 'puzzle', 'region'], 'vellumManifest step')
      return {
        rule,
        puzzle: puzzleId(string(step.puzzle, 'vellumManifest step.puzzle')),
        region: string(step.region, 'vellumManifest step.region'),
      }
    }
    if (rule === 'vellumDissolve') {
      onlyKeys(step, ['rule', 'puzzle', 'selection'], 'vellumDissolve step')
      return {
        rule,
        puzzle: puzzleId(string(step.puzzle, 'vellumDissolve step.puzzle')),
        selection: selection(step.selection),
      }
    }
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
): GameSaveV1 {
  const base = {
    format: 'cursebreaker-save' as const,
    version: 1 as const,
    catalogFingerprint: catalog.fingerprint,
    completed: [...progress.completed].sort(),
  }
  return active === null ? base : {
    ...base,
    active: {
      puzzle: active.puzzle,
      steps: active.timeline.steps,
      cursor: active.timeline.cursor,
    },
  }
}

export function loadGame(catalog: GameCatalog, value: unknown): LoadedGame {
  const root = record(value, 'save')
  if (root.format !== 'cursebreaker-save' || root.version !== 1) {
    throw new GameDomainError('unsupported game save format or version')
  }
  if (root.catalogFingerprint !== catalog.fingerprint) {
    throw new GameDomainError('save catalog fingerprint does not match the bundled catalog')
  }
  if (!Array.isArray(root.completed) || !root.completed.every((id) => typeof id === 'string')) {
    throw new GameDomainError('save completed must be an array of puzzle ids')
  }
  let progress = emptyProgress()
  for (const raw of root.completed) {
    const id = raw as PuzzleId
    catalog.puzzle(id)
    progress = recordCompletion(progress, id)
  }
  if (root.active === undefined) return { progress, active: null }

  const active = record(root.active, 'save active session')
  if (typeof active.puzzle !== 'string' || !Array.isArray(active.steps)
    || typeof active.cursor !== 'number' || !Number.isInteger(active.cursor)) {
    throw new GameDomainError('save active session has invalid puzzle, steps, or cursor')
  }
  const puzzle = catalog.puzzle(active.puzzle as PuzzleId)
  if (!isUnlocked(catalog, progress, puzzle.id)) {
    throw new GameDomainError(`active puzzle '${puzzle.id}' is locked by incomplete prerequisites`)
  }
  const steps = active.steps.map(gameStepFromJson)
  const authority: GameRuntimeAuthority = {
    context: catalog.source.context,
    puzzle: (id) => catalog.puzzle(id),
    canUseVellum: (id) => progress.completed.has(id) && catalog.puzzle(id).grantsVellum,
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
