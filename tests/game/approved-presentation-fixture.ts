import { mountFolioView } from '../../src/game/interface/folio-view'
import { FolioMotion } from '../../src/game/interface/folio-motion'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { cultureId, puzzleId } from '../../src/game/types'

const firstCulture = cultureId('seyric-horizon')
const secondCulture = cultureId('myratic-tradition')
const completed = puzzleId('completed-seal')
const locked = puzzleId('locked-seal')
const packet = puzzleId('restricted-packet')
const additionalRecords = [
  puzzleId('catalog-seal-1'),
  puzzleId('catalog-seal-2'),
  puzzleId('catalog-seal-3'),
  puzzleId('catalog-seal-4'),
] as const

const preview = (id: string) => ({
  key: `fixture:${id}`,
  fingerprint: id,
  diagram: null,
  width: 640 as const,
  height: 400 as const,
})

const record = (
  id: ReturnType<typeof puzzleId>,
  status: 'completed' | 'locked' | 'unlocked',
  restrictedPacket = false,
) => ({
  id,
  levelNumber: 1,
  name: id === completed
    ? 'Completed seal'
    : id === packet ? 'Restricted packet' : id === locked ? 'Locked seal' : 'Catalog seal',
  accession: 'TEST-01',
  summary: 'Production motion and geometry evidence.',
  status,
  affordance: id === completed ? 'drag-artifact' as const : 'inert' as const,
  priority: false,
  restrictedPacket,
  preview: preview(id),
})

const baseProjection = (): FolioProjection => ({
  mode: 'puzzle',
  selectedCulture: firstCulture,
  selectedScroll: 0,
  reducedMotion: new URLSearchParams(location.search).has('reduced'),
  cultures: [
    {
      id: firstCulture,
      name: 'The Seyric Horizon',
      shortName: 'Seyric',
      historicalSummary: 'Earliest securely excavated sealing horizon; chronology remains under catalog revision.',
      unlocked: true,
      scroll: 0,
      records: [
        record(completed, 'completed'),
        record(locked, 'locked'),
        ...additionalRecords.map((id) => record(id, 'unlocked')),
      ],
    },
    {
      id: secondCulture,
      name: 'The Myratic Tradition',
      shortName: 'Myratic',
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
  onArtifactDragStart: () => {},
  onArtifactDragMove: () => {},
  onArtifactDragEnd: () => {},
  onArtifactDragCancel: () => {},
})
const recordMotionProbe = new FolioMotion(folio.element)

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
  recordMotion: (inspecting: boolean) => {
    void recordMotionProbe.recordInspection(completed, inspecting, false)
  },
  settleRecordMotion: () => recordMotionProbe.settleAll(),
  setLayout: (width: number, height: number) => environment.setLayout(width, height),
  setFolioDrawerOpen: (open: boolean) => environment.setFolioDrawerOpen(open),
}

declare global {
  interface Window { __approvedPresentationFixture: typeof fixture }
}
window.__approvedPresentationFixture = fixture
