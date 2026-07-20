import type { MountedFolioView } from '../../src/game/interface/folio-view'
import { mountFolioView } from '../../src/game/interface/folio-view'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { cultureId, puzzleId } from '../../src/game/types'

const culture = cultureId('browser-culture')
const completed = puzzleId('browser-completed-record')
const preview = {
  key: 'fixture:browser-completed-record',
  fingerprint: 'browser-completed-record',
  diagram: null,
  width: 640 as const,
  height: 400 as const,
}
const projection: FolioProjection = {
  mode: 'puzzle',
  selectedCulture: culture,
  selectedScroll: 0,
  reducedMotion: true,
  cultures: [{
    id: culture,
    name: 'Browser culture',
    shortName: 'Browser',
    historicalSummary: 'Runtime geometry fixture.',
    unlocked: true,
    scroll: 0,
    records: [{
      id: completed,
      levelNumber: 1,
      name: 'Completed browser record',
      accession: 'B-1',
      summary: 'A completed record used to verify drag geometry.',
      status: 'completed',
      affordance: 'drag-theorem',
      priority: false,
      restrictedPacket: false,
      preview,
    }],
  }],
}

const lensHost = document.querySelector<HTMLElement>('#lens-host')!
const lens = mountLensEnvironment({
  host: lensHost,
  substrateSeed: 'first:0001',
  width: window.innerWidth,
  height: window.innerHeight,
})
const cancellations: string[] = []
let draggedRecord: HTMLElement | null = null
let pointerId: number | null = null
const options = {
  host: lens.folioHost,
  projection,
  onSelectPuzzle: () => {},
  onRefusePuzzle: () => {},
  onSelectCulture: () => {},
  onRefuseCulture: () => {},
  onScroll: () => {},
  onTheoremDragStart: (_puzzle: typeof completed, sample: { pointerId: number }) => {
    draggedRecord = lens.folioHost.querySelector(`[data-puzzle="${completed}"]`)
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
      setLayout(width: number, height: number): void
      setFolioLeft(left: number): void
      replaceDragView(): void
      disposeDragView(): void
      dragCleanup(): {
        cancellations: number
        connected: boolean
        lifted: boolean
        returning: boolean
        sourceHidden: boolean
        recordMotionKind: string
        x: string
        y: string
        captured: boolean
      }
    }
  }
}

window.__productionInterfaceFixture = {
  setSeed: (seed) => lens.setSubstrateSeed(seed),
  setLayout: (width, height) => lens.setLayout(width, height),
  setFolioLeft: (left) => lens.folioHost.style.setProperty('--curse-folio-left', `${left}px`),
  replaceDragView: () => dragView.update(projection),
  disposeDragView: () => dragView.dispose(),
  dragCleanup: () => ({
    cancellations: cancellations.length,
    connected: draggedRecord?.isConnected ?? false,
    lifted: lens.folioHost.querySelector('.inspection-positioner')
      ?.classList.contains('is-theorem-lifted') ?? false,
    returning: lens.folioHost.querySelector('.inspection-positioner')
      ?.classList.contains('is-returning') ?? false,
    sourceHidden: draggedRecord?.classList.contains('is-inspection-source') ?? false,
    recordMotionKind: lens.folioHost.querySelector<HTMLElement>('.curse-folio')
      ?.dataset.motionRecordKind ?? '',
    x: lens.folioHost.querySelector<HTMLElement>('.inspection-positioner')
      ?.style.getPropertyValue('--folio-drag-x') ?? '',
    y: lens.folioHost.querySelector<HTMLElement>('.inspection-positioner')
      ?.style.getPropertyValue('--folio-drag-y') ?? '',
    captured: draggedRecord !== null && pointerId !== null
      ? draggedRecord.hasPointerCapture(pointerId)
      : false,
  }),
}
