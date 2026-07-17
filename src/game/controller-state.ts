import type { GameCatalog } from './catalog'
import type { GameSession } from './session'
import type { PresentedTeacherIntervention } from './teaching'
import {
  GameDomainError,
  type CultureId,
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
  | ({ readonly kind: 'teacher' } & PresentedTeacherIntervention)
  | { readonly kind: 'editor' }

export type GameControllerState = {
  readonly mode: GamePrimaryMode
  readonly activePuzzle: PuzzleId | null
  readonly completed: ReadonlySet<PuzzleId>
  readonly firstAttempts: ReadonlyMap<PuzzleId, GameSession>
  readonly replays: ReadonlyMap<PuzzleId, GameSession>
  readonly acknowledgedTeachers: ReadonlySet<string>
  readonly completionReceipt: CompletionReceipt | null
  readonly selectedCulture: CultureId
  readonly scrollByCulture: ReadonlyMap<CultureId, number>
  readonly settings: GameSettings
  readonly transient: GameTransient | null
}

export type InitialGamePreferences = {
  readonly reducedMotion: boolean
}

export function createInitialGameState(
  catalog: GameCatalog,
  preferences: InitialGamePreferences,
): GameControllerState {
  const firstCulture = catalog.source.cultures[0]
  if (firstCulture === undefined) throw new GameDomainError('game catalog must contain a culture')
  return {
    mode: 'archive',
    activePuzzle: null,
    completed: new Set(),
    firstAttempts: new Map(),
    replays: new Map(),
    acknowledgedTeachers: new Set(),
    completionReceipt: null,
    selectedCulture: firstCulture.id,
    scrollByCulture: new Map(catalog.source.cultures.map((culture) => [culture.id, 0] as const)),
    settings: {
      reducedMotion: preferences.reducedMotion,
      fullscreen: true,
      textSize: 'medium',
    },
    transient: null,
  }
}
