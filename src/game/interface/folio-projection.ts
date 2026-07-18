import type { GameCatalog } from '../catalog'
import type { GameControllerState, GamePrimaryMode } from '../controller-state'
import { isCultureUnlocked, isUnlocked } from '../progress'
import type { CultureId, PuzzleId } from '../types'

export type FolioRecordStatus = 'locked' | 'unlocked' | 'completed'
export type FolioRecordAffordance = 'select' | 'resist' | 'drag-theorem' | 'inert'

export type FolioRecordProjection = {
  readonly id: PuzzleId
  readonly name: string
  readonly accession: string | null
  readonly summary: string
  readonly status: FolioRecordStatus
  readonly affordance: FolioRecordAffordance
}

export type FolioCultureProjection = {
  readonly id: CultureId
  readonly name: string
  readonly historicalSummary: string
  readonly unlocked: boolean
  readonly scroll: number
  readonly records: readonly FolioRecordProjection[]
}

export type FolioProjection = {
  readonly mode: Extract<GamePrimaryMode, 'archive' | 'puzzle'>
  readonly selectedCulture: CultureId
  readonly selectedScroll: number
  readonly reducedMotion: boolean
  readonly cultures: readonly FolioCultureProjection[]
}

const recordAffordance = (
  mode: FolioProjection['mode'],
  status: FolioRecordStatus,
): FolioRecordAffordance => {
  if (mode === 'puzzle') return status === 'completed' ? 'drag-theorem' : 'inert'
  return status === 'locked' ? 'resist' : 'select'
}

export function projectFolio(
  catalog: GameCatalog,
  state: GameControllerState,
  mode: FolioProjection['mode'],
): FolioProjection {
  const progress = { completed: state.completed }
  const cultures = catalog.source.cultures.map((culture) => ({
    id: culture.id,
    name: culture.name,
    historicalSummary: culture.historicalSummary,
    unlocked: isCultureUnlocked(catalog, progress, culture.id),
    scroll: state.scrollByCulture.get(culture.id) ?? 0,
    records: catalog.source.puzzles
      .filter((puzzle) => puzzle.culture === culture.id)
      .map((puzzle): FolioRecordProjection => {
        const status: FolioRecordStatus = state.completed.has(puzzle.id)
          ? 'completed'
          : isUnlocked(catalog, progress, puzzle.id) ? 'unlocked' : 'locked'
        return {
          id: puzzle.id,
          name: puzzle.name.professional,
          accession: puzzle.name.accession ?? null,
          summary: puzzle.provenance.summary,
          status,
          affordance: recordAffordance(mode, status),
        }
      }),
  }))
  const selected = cultures.find((culture) => culture.id === state.selectedCulture)
  return {
    mode,
    selectedCulture: state.selectedCulture,
    selectedScroll: selected?.scroll ?? 0,
    reducedMotion: state.settings.reducedMotion,
    cultures,
  }
}
