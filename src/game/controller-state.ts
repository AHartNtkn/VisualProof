import type { GameCatalog } from './catalog'
import type { GameSession } from './session'
import type { PresentedGuidanceIntervention } from './teaching'
import {
  GameDomainError,
  type CultureId,
  type GuidanceDeliveryIdentity,
  type PuzzleId,
} from './types'

export type GamePrimaryMode = 'archive' | 'puzzle' | 'completion'

export type InterfaceTextSize = 'small' | 'medium' | 'large'

export type GameSettings = {
  readonly reducedMotion: boolean
  readonly fullscreen: boolean
  readonly textSize: InterfaceTextSize
}

export type CompletionReceipt = {
  readonly puzzle: PuzzleId
  readonly moves: number
  readonly replay: boolean
}

export type GameTransient =
  | { readonly kind: 'pause'; readonly presentation: 'menu' | 'settings' }
  | { readonly kind: 'editor' }

export type ActiveGuidance = PresentedGuidanceIntervention & {
  readonly page: number
}

export type GameControllerState = {
  readonly mode: GamePrimaryMode
  readonly activePuzzle: PuzzleId | null
  readonly completedPuzzles: ReadonlySet<PuzzleId>
  readonly firstAttempts: ReadonlyMap<PuzzleId, GameSession>
  readonly replays: ReadonlyMap<PuzzleId, GameSession>
  readonly deliveredGuidance: readonly GuidanceDeliveryIdentity[]
  readonly guidance: ActiveGuidance | null
  readonly completionReceipt: CompletionReceipt | null
  readonly selectedCulture: CultureId
  readonly scrollByCulture: ReadonlyMap<CultureId, number>
  readonly settings: GameSettings
  readonly transient: GameTransient | null
}

export type InitialGamePreferences = {
  readonly reducedMotion: boolean
}

/** Detached diagnostic view; mutating it cannot alter controller authority. */
export function snapshotGameControllerState(state: GameControllerState): GameControllerState {
  return structuredClone(state)
}

export function createInitialGameState(
  catalog: GameCatalog,
  preferences: InitialGamePreferences,
): GameControllerState {
  const firstCulture = catalog.cultureIds[0]
  if (firstCulture === undefined) throw new GameDomainError('game catalog must contain a culture')
  return {
    mode: 'archive',
    activePuzzle: null,
    completedPuzzles: new Set(),
    firstAttempts: new Map(),
    replays: new Map(),
    deliveredGuidance: [],
    guidance: null,
    completionReceipt: null,
    selectedCulture: firstCulture,
    scrollByCulture: new Map(catalog.cultureIds.map((culture) => [culture, 0] as const)),
    settings: {
      reducedMotion: preferences.reducedMotion,
      fullscreen: true,
      textSize: 'medium',
    },
    transient: null,
  }
}
