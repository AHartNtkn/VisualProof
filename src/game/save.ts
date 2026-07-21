import {
  gameSessionActionFromJson,
  gameSessionActionToJson,
  type SerializedGameSessionAction,
} from './action'
import type { GameCatalog } from './catalog'
import {
  createInitialGameState,
  type CompletionReceipt,
  type GameControllerState,
  type GamePrimaryMode,
  type GameSettings,
  type InterfaceTextSize,
} from './controller-state'
import { isCultureUnlocked, isUnlocked } from './progress'
import {
  applyGameAction,
  moveCursor,
  startPuzzle,
  type GameSession,
  type GameSessionAction,
} from './session'
import {
  GameDomainError,
  guidanceDeliveryIdentity,
  type CultureId,
  type GuidanceDeliveryIdentity,
  type PuzzleId,
} from './types'

export type SerializedGameTimeline = {
  readonly actions: readonly SerializedGameSessionAction[]
  readonly cursor: number
}

export type GameSave = {
  readonly format: 'cursebreaker-save'
  readonly version: 7
  readonly puzzleFingerprints: Readonly<Record<string, string>>
  readonly completedPuzzles: readonly PuzzleId[]
  readonly attempts: Readonly<Record<string, SerializedGameTimeline>>
  readonly replays: Readonly<Record<string, SerializedGameTimeline>>
  readonly deliveredGuidance: readonly GuidanceDeliveryIdentity[]
  readonly guidance: {
    readonly puzzle: PuzzleId
    readonly intervention: string
    readonly page: number
  } | null
  readonly mode: GamePrimaryMode
  readonly activePuzzle: PuzzleId | null
  readonly completionReceipt: CompletionReceipt | null
  readonly selectedCulture: CultureId
  readonly scrollByCulture: Readonly<Record<string, number>>
  readonly settings: GameSettings
}

const ROOT_FIELDS = [
  'format',
  'version',
  'puzzleFingerprints',
  'completedPuzzles',
  'attempts',
  'replays',
  'deliveredGuidance',
  'guidance',
  'mode',
  'activePuzzle',
  'completionReceipt',
  'selectedCulture',
  'scrollByCulture',
  'settings',
] as const

const strictRecord = (
  value: unknown,
  label: string,
  allowed?: readonly string[],
): Record<string, unknown> => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  const parsed = value as Record<string, unknown>
  if (allowed !== undefined) {
    for (const key of Object.keys(parsed)) {
      if (!allowed.includes(key)) throw new GameDomainError(`${label} has unknown field '${key}'`)
    }
  }
  return parsed
}

const serializeTimeline = (session: GameSession): SerializedGameTimeline => ({
  actions: session.timeline.actions.map(gameSessionActionToJson),
  cursor: session.timeline.cursor,
})

const sortedTimelineRecord = (
  sessions: ReadonlyMap<PuzzleId, GameSession>,
): Record<string, SerializedGameTimeline> => Object.fromEntries(
  [...sessions]
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([id, session]) => [id, serializeTimeline(session)]),
)

const referencedPuzzles = (
  completed: ReadonlySet<PuzzleId>,
  attempts: ReadonlyMap<PuzzleId, GameSession>,
  replays: ReadonlyMap<PuzzleId, GameSession>,
  receipt: CompletionReceipt | null,
): ReadonlySet<PuzzleId> => {
  const referenced = new Set(completed.keys())
  for (const id of attempts.keys()) referenced.add(id)
  for (const id of replays.keys()) referenced.add(id)
  if (receipt !== null) referenced.add(receipt.puzzle)
  return referenced
}

export function encodeGameSave(catalog: GameCatalog, state: GameControllerState): GameSave {
  const referenced = referencedPuzzles(
    state.completedPuzzles,
    state.firstAttempts,
    state.replays,
    state.completionReceipt,
  )
  const document: GameSave = {
    format: 'cursebreaker-save',
    version: 7,
    puzzleFingerprints: Object.fromEntries(
      [...referenced]
        .sort()
        .map((id) => [id, catalog.puzzleFingerprint(id)]),
    ),
    completedPuzzles: [...state.completedPuzzles],
    attempts: sortedTimelineRecord(state.firstAttempts),
    replays: sortedTimelineRecord(state.replays),
    deliveredGuidance: [...state.deliveredGuidance]
      .map((identity) => ({ ...identity })),
    guidance: state.guidance === null ? null : {
      puzzle: state.guidance.identity.puzzle,
      intervention: state.guidance.identity.intervention,
      page: state.guidance.page,
    },
    mode: state.mode,
    activePuzzle: state.activePuzzle,
    completionReceipt: state.completionReceipt,
    selectedCulture: state.selectedCulture,
    scrollByCulture: Object.fromEntries(
      catalog.cultureIds.map((culture) => [
        culture,
        state.scrollByCulture.get(culture),
      ]),
    ) as Readonly<Record<string, number>>,
    settings: state.settings,
  }
  return document
}

const readPuzzleId = (catalog: GameCatalog, value: unknown, label: string): PuzzleId => {
  if (typeof value !== 'string') throw new GameDomainError(`${label} must be a puzzle id`)
  const id = value as PuzzleId
  catalog.puzzle(id)
  return id
}

const readCultureId = (catalog: GameCatalog, value: unknown, label: string): CultureId => {
  if (typeof value !== 'string') throw new GameDomainError(`${label} must be a culture id`)
  const id = value as CultureId
  catalog.culture(id)
  return id
}

const readActions = (value: unknown, label: string): readonly GameSessionAction[] => {
  if (!Array.isArray(value)) throw new GameDomainError(`${label} must be an array`)
  return value.map((entry, index) => {
    try {
      return gameSessionActionFromJson(entry, `${label}[${index}]`)
    } catch (error) {
      throw new GameDomainError(
        `invalid ${label} action ${index}: ${error instanceof Error ? error.message : String(error)}`,
      )
    }
  })
}

const readCompletedPuzzles = (
  catalog: GameCatalog,
  value: unknown,
): ReadonlySet<PuzzleId> => {
  if (!Array.isArray(value)) throw new GameDomainError('save completedPuzzles must be an array')
  const completed = new Set<PuzzleId>()
  for (const [index, entry] of value.entries()) {
    const puzzle = readPuzzleId(catalog, entry, `save completed puzzle ${index}`)
    if (completed.has(puzzle)) {
      throw new GameDomainError(`save completedPuzzles repeats puzzle '${puzzle}'`)
    }
    if (!isUnlocked(catalog, { completed }, puzzle)) {
      throw new GameDomainError(
        `completed puzzle '${puzzle}' appears before its unlock prerequisites`,
      )
    }
    completed.add(puzzle)
  }
  return completed
}

const readTimeline = (
  catalog: GameCatalog,
  puzzle: PuzzleId,
  value: unknown,
  completed: ReadonlySet<PuzzleId>,
): GameSession => {
  const saved = strictRecord(value, `saved timeline '${puzzle}'`, ['actions', 'cursor'])
  if (!Number.isSafeInteger(saved.cursor)) {
    throw new GameDomainError(`saved timeline '${puzzle}' cursor must be an integer`)
  }
  const actions = readActions(saved.actions, `saved timeline '${puzzle}' actions`)
  let session = startPuzzle(catalog.puzzle(puzzle))
  const authority = {
    context: catalog.context,
    artifact: (id: PuzzleId) => completed.has(id) ? catalog.puzzle(id) : undefined,
  }
  try {
    for (const action of actions) {
      const transition = applyGameAction(session, action, authority)
      if (transition.completedNow) {
        throw new GameDomainError(`saved unfinished timeline '${puzzle}' reaches completion`)
      }
      session = transition.session
    }
  } catch (error) {
    if (error instanceof GameDomainError && /saved unfinished timeline/.test(error.message)) throw error
    throw new GameDomainError(
      `invalid saved timeline '${puzzle}': ${error instanceof Error ? error.message : String(error)}`,
    )
  }
  const cursor = saved.cursor as number
  if (cursor < 0 || cursor > actions.length) {
    throw new GameDomainError(`saved timeline '${puzzle}' cursor ${cursor} is outside 0..${actions.length}`)
  }
  return moveCursor(session, cursor)
}

const readTimelineMap = (
  catalog: GameCatalog,
  value: unknown,
  label: string,
  completed: ReadonlySet<PuzzleId>,
  classification: 'attempt' | 'replay',
): ReadonlyMap<PuzzleId, GameSession> => {
  const saved = strictRecord(value, label)
  const sessions = new Map<PuzzleId, GameSession>()
  for (const [rawId, timeline] of Object.entries(saved)) {
    const id = readPuzzleId(catalog, rawId, `${label} key`)
    const isCompleted = completed.has(id)
    if (classification === 'attempt' && isCompleted) {
      throw new GameDomainError(`first attempt '${id}' belongs to a completed puzzle`)
    }
    if (classification === 'attempt' && !isUnlocked(catalog, { completed }, id)) {
      throw new GameDomainError(`first attempt '${id}' belongs to a locked puzzle`)
    }
    if (classification === 'replay' && !isCompleted) {
      throw new GameDomainError(`replay '${id}' belongs to an incomplete puzzle`)
    }
    sessions.set(id, readTimeline(catalog, id, timeline, completed))
  }
  return sessions
}

const readSettings = (value: unknown): GameSettings => {
  const settings = strictRecord(
    value,
    'save settings',
    ['reducedMotion', 'fullscreen', 'textSize'],
  )
  if (typeof settings.reducedMotion !== 'boolean' || typeof settings.fullscreen !== 'boolean') {
    throw new GameDomainError('save settings reducedMotion and fullscreen must be booleans')
  }
  if (
    settings.textSize !== 'small'
    && settings.textSize !== 'medium'
    && settings.textSize !== 'large'
  ) {
    throw new GameDomainError('save settings textSize must be small, medium, or large')
  }
  return {
    reducedMotion: settings.reducedMotion,
    fullscreen: settings.fullscreen,
    textSize: settings.textSize as InterfaceTextSize,
  }
}

const readReceipt = (
  catalog: GameCatalog,
  value: unknown,
): CompletionReceipt | null => {
  if (value === null) return null
  const receipt = strictRecord(value, 'save completion receipt', ['puzzle', 'moves', 'replay'])
  const puzzle = readPuzzleId(catalog, receipt.puzzle, 'save completion receipt puzzle')
  if (!Number.isSafeInteger(receipt.moves) || (receipt.moves as number) <= 0) {
    throw new GameDomainError('save completion receipt moves must be a positive integer')
  }
  if (typeof receipt.replay !== 'boolean') {
    throw new GameDomainError('save completion receipt replay must be a boolean')
  }
  return { puzzle, moves: receipt.moves as number, replay: receipt.replay }
}

const readGuidanceDeliveries = (
  catalog: GameCatalog,
  value: unknown,
): readonly GuidanceDeliveryIdentity[] => {
  if (!Array.isArray(value)) {
    throw new GameDomainError('save delivered guidance must be an array')
  }
  const seen = new Set<string>()
  const delivered: GuidanceDeliveryIdentity[] = []
  for (const [index, entry] of value.entries()) {
    const saved = strictRecord(
      entry,
      `save delivered guidance ${index}`,
      ['puzzle', 'intervention'],
    )
    const puzzle = readPuzzleId(
      catalog,
      saved.puzzle,
      `save delivered guidance ${index} puzzle`,
    )
    if (typeof saved.intervention !== 'string') {
      throw new GameDomainError(
        `save delivered guidance ${index} intervention must be a string`,
      )
    }
    const intervention = catalog.guidance(puzzle).interventions.find((candidate) =>
      candidate.id === saved.intervention
      && candidate.repeat === 'once')
    if (intervention === undefined) continue
    const identity = guidanceDeliveryIdentity(puzzle, intervention.id)
    const key = JSON.stringify([identity.puzzle, identity.intervention])
    if (seen.has(key)) {
      throw new GameDomainError(
        `save delivered guidance has duplicate '${identity.puzzle}:${identity.intervention}'`,
      )
    }
    seen.add(key)
    delivered.push(identity)
  }
  return delivered
}

const validateMode = (
  catalog: GameCatalog,
  mode: GamePrimaryMode,
  activePuzzle: PuzzleId | null,
  receipt: CompletionReceipt | null,
  completed: ReadonlySet<PuzzleId>,
  attempts: ReadonlyMap<PuzzleId, GameSession>,
  replays: ReadonlyMap<PuzzleId, GameSession>,
): void => {
  if (mode === 'archive') {
    if (activePuzzle !== null || receipt !== null) {
      throw new GameDomainError('archive mode cannot have an active puzzle or completion receipt')
    }
    return
  }
  if (activePuzzle === null) throw new GameDomainError(`${mode} mode requires an active puzzle`)
  if (!isUnlocked(catalog, { completed }, activePuzzle)) {
    throw new GameDomainError(`active puzzle '${activePuzzle}' is locked`)
  }
  if (mode === 'puzzle') {
    if (receipt !== null) throw new GameDomainError('puzzle mode cannot have a completion receipt')
    const activeTimeline = completed.has(activePuzzle)
      ? replays.get(activePuzzle)
      : attempts.get(activePuzzle)
    if (activeTimeline === undefined) {
      throw new GameDomainError(`active puzzle '${activePuzzle}' has no matching timeline`)
    }
    return
  }
  if (receipt === null || receipt.puzzle !== activePuzzle) {
    throw new GameDomainError('completion mode requires a matching completion receipt')
  }
  if (!completed.has(activePuzzle)) {
    throw new GameDomainError('completion receipt puzzle must be durably completed')
  }
  if (attempts.has(activePuzzle) || replays.has(activePuzzle)) {
    throw new GameDomainError('completion receipt puzzle cannot retain its completed timeline')
  }
}

export function decodeGameSave(catalog: GameCatalog, value: unknown): GameControllerState {
  const root = strictRecord(value, 'save', ROOT_FIELDS)
  if (root.format !== 'cursebreaker-save' || root.version !== 7) {
    throw new GameDomainError('unsupported game save format or version')
  }
  const completedPuzzles = readCompletedPuzzles(catalog, root.completedPuzzles)

  const attempts = readTimelineMap(catalog, root.attempts, 'save attempts', completedPuzzles, 'attempt')
  const replays = readTimelineMap(catalog, root.replays, 'save replays', completedPuzzles, 'replay')
  const receipt = readReceipt(catalog, root.completionReceipt)

  const mode = root.mode
  if (mode !== 'archive' && mode !== 'puzzle' && mode !== 'completion') {
    throw new GameDomainError('save mode must be archive, puzzle, or completion')
  }
  const activePuzzle = root.activePuzzle === null
    ? null
    : readPuzzleId(catalog, root.activePuzzle, 'save active puzzle')
  validateMode(catalog, mode, activePuzzle, receipt, completedPuzzles, attempts, replays)

  const deliveredGuidance = readGuidanceDeliveries(catalog, root.deliveredGuidance)

  const guidance = (() => {
    if (root.guidance === null) return null
    const saved = strictRecord(
      root.guidance,
      'save guidance',
      ['puzzle', 'intervention', 'page'],
    )
    const puzzle = readPuzzleId(catalog, saved.puzzle, 'save guidance puzzle')
    if (mode !== 'puzzle' || activePuzzle !== puzzle) {
      throw new GameDomainError('save guidance must belong to the active puzzle')
    }
    if (typeof saved.intervention !== 'string') {
      throw new GameDomainError('save guidance intervention must be a string')
    }
    const intervention = catalog.guidance(puzzle).interventions.find((candidate) =>
      candidate.id === saved.intervention
      && candidate.trigger.kind !== 'completion')
    if (intervention === undefined) return null
    if (!Number.isSafeInteger(saved.page)) {
      throw new GameDomainError('save guidance page must be an integer')
    }
    const page = saved.page as number
    if (page < 0 || page >= intervention.pages.length) {
      return null
    }
    const identity = guidanceDeliveryIdentity(puzzle, intervention.id)
    if (intervention.repeat === 'once' && !deliveredGuidance.some((candidate) =>
      candidate.puzzle === identity.puzzle
      && candidate.intervention === identity.intervention)) {
      throw new GameDomainError('save once-only guidance must also be recorded as delivered')
    }
    return { identity, intervention, page }
  })()

  const selectedCulture = readCultureId(catalog, root.selectedCulture, 'save selected culture')
  const firstCulture = catalog.cultureIds[0]
  if (
    selectedCulture !== firstCulture
    && !isCultureUnlocked(catalog, { completed: completedPuzzles }, selectedCulture)
  ) {
    throw new GameDomainError(`selected culture '${selectedCulture}' is locked`)
  }
  const savedScroll = strictRecord(root.scrollByCulture, 'save scrollByCulture')
  const catalogCultures = new Set(catalog.cultureIds)
  if (
    Object.keys(savedScroll).length !== catalogCultures.size
    || [...catalogCultures].some((id) => !(id in savedScroll))
  ) {
    throw new GameDomainError('save scroll must contain every catalog culture exactly once')
  }
  const scrollByCulture = new Map<CultureId, number>()
  for (const [rawId, rawScroll] of Object.entries(savedScroll)) {
    const id = readCultureId(catalog, rawId, 'save scroll culture')
    if (!Number.isFinite(rawScroll) || (rawScroll as number) < 0) {
      throw new GameDomainError(`save scroll for '${id}' must be nonnegative finite`)
    }
    scrollByCulture.set(id, rawScroll as number)
  }

  const references = referencedPuzzles(completedPuzzles, attempts, replays, receipt)
  const fingerprints = strictRecord(root.puzzleFingerprints, 'save puzzleFingerprints')
  for (const id of references) {
    if (!(id in fingerprints)) throw new GameDomainError(`missing logical fingerprint for '${id}'`)
    if (fingerprints[id] !== catalog.puzzleFingerprint(id)) {
      throw new GameDomainError(`save puzzle logical fingerprint does not match '${id}'`)
    }
  }
  for (const [rawId, fingerprint] of Object.entries(fingerprints)) {
    const id = readPuzzleId(catalog, rawId, 'save fingerprint puzzle')
    if (!references.has(id)) throw new GameDomainError(`unreferenced logical fingerprint for '${id}'`)
    if (typeof fingerprint !== 'string') {
      throw new GameDomainError(`logical fingerprint for '${id}' must be a string`)
    }
  }

  return {
    mode,
    activePuzzle,
    completedPuzzles,
    firstAttempts: attempts,
    replays,
    deliveredGuidance,
    guidance,
    completionReceipt: receipt,
    selectedCulture,
    scrollByCulture,
    settings: readSettings(root.settings),
    transient: null,
  }
}

export type GameStartup = {
  readonly save: unknown | null
  readonly reducedMotion: boolean
}

export function startGame(catalog: GameCatalog, startup: GameStartup): GameControllerState {
  return startup.save === null
    ? createInitialGameState(catalog, { reducedMotion: startup.reducedMotion })
    : decodeGameSave(catalog, startup.save)
}
