import { mountFolioView } from '../../src/game/interface/folio-view'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { cultureId, puzzleId } from '../../src/game/types'

const firstCulture = cultureId('seyric-horizon')
const secondCulture = cultureId('myratic-tradition')
const completed = puzzleId('completed-seal')
const locked = puzzleId('locked-seal')
const packet = puzzleId('restricted-packet')

const record = (
  id: ReturnType<typeof puzzleId>,
  status: 'completed' | 'locked' | 'unlocked',
  restrictedPacket = false,
) => ({
  id,
  name: id === completed ? 'Completed seal' : id === packet ? 'Restricted packet' : 'Locked seal',
  accession: 'TEST-01',
  summary: 'Production motion and geometry evidence.',
  status,
  affordance: id === completed ? 'drag-theorem' as const : 'inert' as const,
  priority: false,
  restrictedPacket,
})

const baseProjection = (): FolioProjection => ({
  mode: 'puzzle',
  selectedCulture: firstCulture,
  selectedScroll: 0,
  reducedMotion: false,
  cultures: [
    {
      id: firstCulture,
      name: 'The Seyric Horizon',
      historicalSummary: 'Earliest securely excavated sealing horizon; chronology remains under catalog revision.',
      unlocked: true,
      scroll: 0,
      records: [record(completed, 'completed'), record(locked, 'locked')],
    },
    {
      id: secondCulture,
      name: 'The Myratic Tradition',
      historicalSummary: 'Later archive tradition under conservation review.',
      unlocked: true,
      scroll: 0,
      records: [record(packet, 'locked', true)],
    },
  ],
})

const host = document.querySelector<HTMLElement>('#host')!
const environment = mountLensEnvironment({
  host,
  substrateSeed: 'approved-presentation',
  width: innerWidth,
  height: innerHeight,
})
let projection = baseProjection()
const folio = mountFolioView({
  host: environment.folioHost,
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

const update = (next: FolioProjection): void => {
  projection = next
  folio.update(projection)
}

const fixture = {
  ready: true,
  dossier: () => update({ ...projection, selectedCulture: secondCulture }),
  packet: () => update({
    ...projection,
    selectedCulture: secondCulture,
    cultures: projection.cultures.map((culture) => culture.id !== secondCulture ? culture : {
      ...culture,
      records: culture.records.map((entry) => entry.id === packet
        ? { ...entry, status: 'unlocked' as const }
        : entry),
    }),
  }),
  restriction: () => folio.resistPuzzle(locked),
}

declare global {
  interface Window { __approvedPresentationFixture: typeof fixture }
}
window.__approvedPresentationFixture = fixture
