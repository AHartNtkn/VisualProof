import type { MountedFolioView } from '../../src/game/interface/folio-view'
import { mountFolioView } from '../../src/game/interface/folio-view'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { cultureId, puzzleId } from '../../src/game/types'

const culture = cultureId('browser-culture')
const completed = puzzleId('browser-completed-record')
const projection: FolioProjection = {
  mode: 'puzzle',
  selectedCulture: culture,
  selectedScroll: 0,
  reducedMotion: true,
  cultures: [{
    id: culture,
    name: 'Browser culture',
    historicalSummary: 'Runtime geometry fixture.',
    unlocked: true,
    scroll: 0,
    records: [{
      id: completed,
      name: 'Completed browser record',
      accession: 'B-1',
      summary: 'A completed record used to verify drag geometry.',
      status: 'completed',
      affordance: 'drag-theorem',
    }],
  }],
}

const lensHost = document.querySelector<HTMLElement>('#lens-host')!
const dragHost = document.querySelector<HTMLElement>('#drag-host')!
const lens = mountLensEnvironment({
  host: lensHost,
  substrateSeed: 'first:0001',
  width: window.innerWidth,
  height: window.innerHeight,
})
mountFolioView({
  host: lens.folioHost,
  projection,
  onSelectPuzzle: () => {},
  onRefusePuzzle: () => {},
  onSelectCulture: () => {},
  onRefuseCulture: () => {},
  onScroll: () => {},
  onTheoremDragStart: () => {},
  onTheoremDragMove: () => {},
  onTheoremDragEnd: () => {},
  onTheoremDragCancel: () => {},
})

const cancellations: string[] = []
let draggedRecord: HTMLElement | null = null
let pointerId: number | null = null
const options = {
  host: dragHost,
  projection,
  onSelectPuzzle: () => {},
  onRefusePuzzle: () => {},
  onSelectCulture: () => {},
  onRefuseCulture: () => {},
  onScroll: () => {},
  onTheoremDragStart: (_puzzle: typeof completed, sample: { pointerId: number }) => {
    draggedRecord = dragHost.querySelector(`[data-puzzle="${completed}"]`)
    pointerId = sample.pointerId
  },
  onTheoremDragMove: () => {},
  onTheoremDragEnd: () => {},
  onTheoremDragCancel: () => cancellations.push('cancel'),
}
let dragView: MountedFolioView = mountFolioView(options)

declare global {
  interface Window {
    __productionInterfaceFixture: {
      setSeed(seed: string): void
      replaceDragView(): void
      disposeDragView(): void
      dragCleanup(): {
        cancellations: number
        connected: boolean
        lifted: boolean
        x: string
        y: string
        captured: boolean
      }
    }
  }
}

window.__productionInterfaceFixture = {
  setSeed: (seed) => lens.setSubstrateSeed(seed),
  replaceDragView: () => dragView.update(projection),
  disposeDragView: () => dragView.dispose(),
  dragCleanup: () => ({
    cancellations: cancellations.length,
    connected: draggedRecord?.isConnected ?? false,
    lifted: draggedRecord?.classList.contains('is-theorem-lifted') ?? false,
    x: draggedRecord?.style.getPropertyValue('--folio-drag-x') ?? '',
    y: draggedRecord?.style.getPropertyValue('--folio-drag-y') ?? '',
    captured: draggedRecord !== null && pointerId !== null
      ? draggedRecord.hasPointerCapture(pointerId)
      : false,
  }),
}
