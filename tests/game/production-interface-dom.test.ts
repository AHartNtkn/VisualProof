import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { mountFolioView } from '../../src/game/interface/folio-view'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import { cultureId, puzzleId } from '../../src/game/types'
import { eventWith, FakeDocument, FakeElement } from './interface-fake-dom'

const FIRST_CULTURE = cultureId('first-culture')
const SECOND_CULTURE = cultureId('second-culture')
const COMPLETED = puzzleId('completed-record')
const AVAILABLE = puzzleId('available-record')
const LOCKED = puzzleId('locked-record')

const projection = (mode: FolioProjection['mode']): FolioProjection => ({
  mode,
  selectedCulture: FIRST_CULTURE,
  selectedScroll: 85,
  reducedMotion: false,
  cultures: [
    {
      id: FIRST_CULTURE,
      name: 'First culture',
      historicalSummary: 'Recovered records from the first field season.',
      unlocked: true,
      scroll: 85,
      records: [
        { id: COMPLETED, name: 'Completed', accession: 'A-1', summary: 'Cleared.', status: 'completed', affordance: mode === 'archive' ? 'select' : 'drag-theorem' },
        { id: AVAILABLE, name: 'Available', accession: null, summary: 'Available.', status: 'unlocked', affordance: mode === 'archive' ? 'select' : 'inert' },
        { id: LOCKED, name: 'Locked', accession: null, summary: 'Restricted.', status: 'locked', affordance: mode === 'archive' ? 'resist' : 'inert' },
      ],
    },
    {
      id: SECOND_CULTURE,
      name: 'Second culture',
      historicalSummary: 'Restricted records.',
      unlocked: false,
      scroll: 0,
      records: [],
    },
  ],
})

describe('production excavation folio DOM view', () => {
  it('keeps one active dossier, a continuous accessible sheet, and immediate archive affordances', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const selected: string[] = []
    const refused: string[] = []
    const cultures: string[] = []
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('archive'),
      motionClock: { wait: async () => {} },
      onSelectPuzzle: (id) => selected.push(id),
      onRefusePuzzle: (id) => refused.push(id),
      onSelectCulture: (id) => cultures.push(id),
      onRefuseCulture: (id) => refused.push(id),
      onScroll: () => {},
      onTheoremDragStart: () => {},
      onTheoremDragMove: () => {},
      onTheoremDragEnd: () => {},
      onTheoremDragCancel: () => {},
    })
    const root = view.element as unknown as FakeElement
    const dossier = root.querySelector('.curse-folio-dossier')!
    const sheet = root.querySelector('.curse-folio-sheet')!
    expect(root.querySelectorAll('.curse-folio-dossier')).toHaveLength(1)
    expect(sheet.getAttribute('role')).toBe('list')
    expect(sheet.getAttribute('tabindex')).toBe('0')
    expect(root.querySelectorAll('.curse-folio-page')).toHaveLength(0)
    expect(sheet.scrollTop).toBe(85)

    root.querySelector(`[data-puzzle="${COMPLETED}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-puzzle="${LOCKED}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-culture="${SECOND_CULTURE}"]`)!.dispatchEvent(new Event('click'))
    expect(selected).toEqual([COMPLETED, AVAILABLE])
    expect(refused).toEqual([LOCKED, SECOND_CULTURE])
    expect(cultures).toEqual([])

    view.update({ ...projection('archive'), selectedCulture: SECOND_CULTURE, selectedScroll: 0 })
    expect(root.querySelector('.curse-folio-dossier')).toBe(dossier)
    expect(root.querySelectorAll('.curse-folio-dossier')).toHaveLength(1)
  })

  it('never navigates in puzzle mode and exposes drag lifecycle only for completed records', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const calls: string[] = []
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('puzzle'),
      onSelectPuzzle: () => calls.push('navigate'),
      onRefusePuzzle: () => calls.push('refuse'),
      onSelectCulture: () => {},
      onRefuseCulture: () => {},
      onScroll: () => {},
      onTheoremDragStart: (id) => calls.push(`start:${id}`),
      onTheoremDragMove: (id) => calls.push(`move:${id}`),
      onTheoremDragEnd: (id) => calls.push(`end:${id}`),
      onTheoremDragCancel: (id) => calls.push(`cancel:${id}`),
    })
    const root = view.element as unknown as FakeElement
    const completed = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    const available = root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!

    available.dispatchEvent(new Event('click'))
    available.dispatchEvent(eventWith('pointerdown', { button: 0, pointerId: 4, clientX: 10, clientY: 20 }))
    completed.dispatchEvent(eventWith('pointerdown', { button: 0, pointerId: 7, clientX: 30, clientY: 40 }))
    completed.dispatchEvent(eventWith('pointermove', { pointerId: 7, clientX: 44, clientY: 55 }))
    expect(completed.classList.contains('is-theorem-lifted')).toBe(true)
    expect(completed.style.getPropertyValue('--folio-drag-x')).toBe('44px')
    completed.dispatchEvent(eventWith('pointerup', { pointerId: 7, clientX: 50, clientY: 60 }))
    expect(completed.classList.contains('is-theorem-lifted')).toBe(false)
    expect(calls).toEqual([
      `start:${COMPLETED}`,
      `move:${COMPLETED}`,
      `end:${COMPLETED}`,
    ])
  })
})

describe('production lens DOM ownership and approved assets', () => {
  it('owns the exact dark-substrate/canvas/gasket/timeline layer order and drawer host', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const lens = mountLensEnvironment({
      host: host as unknown as HTMLElement,
      substrateSeed: 'fixture-seed',
      width: 1600,
      height: 1000,
    })
    const root = lens.element as unknown as FakeElement
    const stage = root.querySelector('.curse-production-lens')!
    expect(stage.children.map(({ className }) => className)).toEqual([
      'curse-production-substrate curse-decoration',
      'curse-production-proof-slot',
      'curse-production-gasket curse-decoration',
      'curse-production-timeline',
    ])
    expect(root.children.map(({ className }) => className)).toEqual([
      'curse-production-desk',
      'curse-production-lens',
      'curse-production-folio-host',
    ])
    expect(lens.proofCanvasSlot).toBe(stage.children[1])
    expect(lens.folioHost).toBe(root.children[2])
    expect(root.querySelector('.curse-production-timeline-handle-slot')).not.toBeNull()
  })

  it('references only the approved lens assets and imports production CSS from runtime modules', () => {
    const lensSource = readFileSync('src/game/interface/lens-environment.ts', 'utf8')
    const folioCss = readFileSync('src/game/interface/folio.css', 'utf8')
    const lensCss = readFileSync('src/game/interface/lens-environment.css', 'utf8')
    for (const asset of [
      'desk/natural-indigo-hardwood.png',
      'central-lens/gasket-frame.png',
      'central-lens/timeline-housing.png',
      'central-lens/timeline-handle.png',
      'substrates/static-review-substrate.png',
    ]) expect(lensSource).toContain(asset)
    expect(lensSource).not.toMatch(/central-lens\/(?:frame|glass|shadow|lever-housing|lever-handle)\.png/)
    expect(lensSource).toContain("import './lens-environment.css'")
    expect(folioCss).toContain('scrollbar-width: none')
    expect(folioCss).toContain('clearance-slip.png')
    expect(folioCss).toContain('restricted-sleeve.png')
    expect(lensCss).toContain('background: #07090c')
  })
})
