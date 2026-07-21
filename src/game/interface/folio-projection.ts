import type { GameCatalog } from '../catalog'
import type { GameControllerState, GamePrimaryMode } from '../controller-state'
import { isCultureUnlocked, isUnlocked } from '../progress'
import type { CultureId, PuzzleId } from '../types'

export type FolioRecordStatus = 'locked' | 'unlocked' | 'completed'
export type FolioRecordAffordance = 'select' | 'resist' | 'drag-theorem' | 'inert'

export type FolioRecordProjection = {
  readonly id: PuzzleId
  readonly levelNumber: number
  readonly name: string
  readonly accession: string | null
  readonly summary: string
  readonly status: FolioRecordStatus
  readonly affordance: FolioRecordAffordance
  readonly priority: boolean
  readonly restrictedPacket: boolean
}

export type FolioCultureProjection = {
  readonly id: CultureId
  readonly name: string
  readonly shortName: string
  readonly historicalSummary: string
  readonly unlocked: boolean
  readonly scroll: number
  readonly records: readonly FolioRecordProjection[]
}

export type FolioProjection = {
  readonly mode: GamePrimaryMode
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
  if (mode === 'completion') return 'inert'
  return status === 'locked' ? 'resist' : 'select'
}

export function projectFolio(
  catalog: GameCatalog,
  state: GameControllerState,
  mode: FolioProjection['mode'],
): FolioProjection {
  const progress = { completed: state.completedArtifacts }
  const cultures = catalog.cultureIds.map((id) => catalog.culture(id)).map((culture) => ({
    id: culture.id,
    name: culture.name,
    shortName: culture.shortName,
    historicalSummary: culture.historicalSummary,
    unlocked: isCultureUnlocked(catalog, progress, culture.id),
    scroll: state.scrollByCulture.get(culture.id) ?? 0,
    records: catalog.puzzlesInCulture(culture.id)
      .map((id, index): FolioRecordProjection => {
        const artifact = catalog.artifact(id)
        const status: FolioRecordStatus = state.completedArtifacts.has(id)
          ? 'completed'
          : isUnlocked(catalog, progress, id) ? 'unlocked' : 'locked'
        return {
          id,
          levelNumber: index + 1,
          name: artifact.name.professional,
          accession: artifact.name.accession ?? null,
          summary: artifact.provenance.summary,
          status,
          affordance: recordAffordance(mode, status),
          priority: id === culture.gateway,
          restrictedPacket:
            culture.unlocksAfter.length > 0 && id === culture.gateway,
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
