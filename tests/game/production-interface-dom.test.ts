import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import type { FolioProjection } from '../../src/game/interface/folio-projection'
import { mountFolioView } from '../../src/game/interface/folio-view'
import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import type {
  PuzzlePreviewService,
  PuzzlePreviewState,
} from '../../src/game/interface/puzzle-preview-service'
import { cultureId, puzzleId } from '../../src/game/types'
import { eventWith, FakeDocument, FakeElement } from './interface-fake-dom'

const FIRST_CULTURE = cultureId('first-culture')
const SECOND_CULTURE = cultureId('second-culture')
const COMPLETED = puzzleId('completed-record')
const AVAILABLE = puzzleId('available-record')
const LOCKED = puzzleId('locked-record')

const preview = (id: string) => ({
  key: `fixture:${id}`,
  fingerprint: id,
  diagram: null,
  width: 640 as const,
  height: 400 as const,
})

type PendingMotionWait = {
  readonly milliseconds: number
  readonly signal: AbortSignal
}

class PendingMotionClock {
  readonly waits: PendingMotionWait[] = []

  wait(milliseconds: number, signal: AbortSignal): Promise<void> {
    return new Promise((resolve) => {
      const wait = { milliseconds, signal }
      this.waits.push(wait)
      signal.addEventListener('abort', () => {
        const index = this.waits.indexOf(wait)
        if (index >= 0) this.waits.splice(index, 1)
        resolve()
      }, { once: true })
    })
  }
}

class PreviewFixture implements PuzzlePreviewService {
  readonly listeners = new Map<string, Set<(state: PuzzlePreviewState) => void>>()
  readonly subscriptions = new Map<string, number>()
  readonly invalidated: string[] = []
  readonly urls = new Map<string, string>()

  subscribe(
    request: { readonly key: string },
    listener: (state: PuzzlePreviewState) => void,
  ): () => void {
    this.subscriptions.set(request.key, (this.subscriptions.get(request.key) ?? 0) + 1)
    let listeners = this.listeners.get(request.key)
    if (listeners === undefined) {
      listeners = new Set()
      this.listeners.set(request.key, listeners)
    }
    listeners.add(listener)
    listener({ kind: 'preparing' })
    return () => listeners?.delete(listener)
  }

  publish(id: string, state: PuzzlePreviewState): void {
    const key = `fixture:${id}`
    if (state.kind === 'ready') this.urls.set(key, state.url)
    else if (state.kind === 'error') this.urls.delete(key)
    for (const listener of this.listeners.get(key) ?? []) listener(state)
  }

  currentUrl(key: string): string | null { return this.urls.get(key) ?? null }

  evict(id: string): void { this.urls.delete(`fixture:${id}`) }

  invalidate(key: string): void {
    this.invalidated.push(key)
    this.urls.delete(key)
  }

  dispose(): void {}
}

class PreviewObserverFixture {
  static latest: PreviewObserverFixture | null = null
  readonly observed = new Set<Element>()

  constructor(readonly callback: IntersectionObserverCallback) {
    PreviewObserverFixture.latest = this
  }

  observe(target: Element): void { this.observed.add(target) }
  unobserve(target: Element): void { this.observed.delete(target) }
  disconnect(): void { this.observed.clear() }

  emit(target: Element, isIntersecting: boolean): void {
    if (!this.observed.has(target)) return
    this.callback([{ target, isIntersecting }] as IntersectionObserverEntry[], this as unknown as IntersectionObserver)
  }
}

const projection = (mode: FolioProjection['mode']): FolioProjection => ({
  mode,
  selectedCulture: FIRST_CULTURE,
  selectedScroll: 85,
  reducedMotion: false,
  cultures: [
    {
      id: FIRST_CULTURE,
      name: 'First culture',
      shortName: 'First',
      historicalSummary: 'Recovered records from the first field season.',
      unlocked: true,
      scroll: 85,
      records: [
        { id: COMPLETED, levelNumber: 1, name: 'Completed', accession: 'A-1', summary: 'Cleared.', status: 'completed', affordance: mode === 'archive' ? 'select' : 'drag-artifact', priority: false, restrictedPacket: false, preview: preview(COMPLETED) },
        { id: AVAILABLE, levelNumber: 2, name: 'Available', accession: null, summary: 'Available.', status: 'unlocked', affordance: mode === 'archive' ? 'select' : 'inert', priority: true, restrictedPacket: false, preview: preview(AVAILABLE) },
        { id: LOCKED, levelNumber: 3, name: 'Locked', accession: null, summary: 'Restricted.', status: 'locked', affordance: mode === 'archive' ? 'resist' : 'inert', priority: false, restrictedPacket: true, preview: preview(LOCKED) },
      ],
    },
    {
      id: SECOND_CULTURE,
      name: 'Second culture',
      shortName: 'Second',
      historicalSummary: 'Restricted records.',
      unlocked: false,
      scroll: 0,
      records: [],
    },
  ],
})

describe('production excavation folio DOM view', () => {
  it('renders numbered canonical thumbnail states without a floating inspection', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const previews = new PreviewFixture()
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('puzzle'),
      previewService: previews,
      motionClock: { wait: async () => {} },
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
    const root = view.element as unknown as FakeElement
    const completed = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    const frame = completed.querySelector('.curse-folio-puzzle-preview-frame')!
    expect(completed.querySelector('.curse-folio-record-name')!.textContent).toBe('1. Completed')
    expect(completed.getAttribute('aria-label')).toContain('1. Completed')
    expect(frame.dataset.previewState).toBe('preparing')
    expect(frame.querySelector('.curse-folio-puzzle-preview-status')!.textContent)
      .toBe('Preparing preview…')
    frame.querySelector('.curse-folio-puzzle-preview')!.dispatchEvent(new Event('error'))
    expect(previews.invalidated).toEqual([])
    expect(frame.dataset.previewState).toBe('preparing')

    previews.publish(COMPLETED, { kind: 'ready', url: 'blob:completed' })
    expect(frame.dataset.previewState).toBe('ready')
    expect(frame.querySelector('.curse-folio-puzzle-preview')!.src).toBe('blob:completed')
    completed.dispatchEvent(new Event('focus'))
    expect(root.querySelector('.curse-folio-puzzle-preview-inspection')).toBe(null)

    frame.querySelector('.curse-folio-puzzle-preview')!.dispatchEvent(new Event('error'))
    expect(previews.invalidated).toEqual([`fixture:${COMPLETED}`])
    expect(frame.dataset.previewState).toBe('error')

    previews.publish(AVAILABLE, { kind: 'error', message: 'bad diagram' })
    const available = root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!
    expect(available.querySelector('.curse-folio-puzzle-preview-status')!.textContent)
      .toBe('Preview unavailable')
    view.dispose()
  })

  it('retries an unavailable preview only after it leaves and re-enters visibility', () => {
    const document = new FakeDocument()
    ;(document as unknown as { defaultView: { IntersectionObserver: typeof IntersectionObserver } })
      .defaultView = { IntersectionObserver: PreviewObserverFixture as unknown as typeof IntersectionObserver }
    const host = new FakeElement(document)
    const previews = new PreviewFixture()
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('archive'),
      previewService: previews,
      motionClock: { wait: async () => {} },
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
    const root = view.element as unknown as FakeElement
    const frame = root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!
      .querySelector('.curse-folio-puzzle-preview-frame')! as unknown as Element
    const observer = PreviewObserverFixture.latest!

    observer.emit(frame, true)
    expect(previews.subscriptions.get(`fixture:${AVAILABLE}`)).toBe(1)
    previews.publish(AVAILABLE, { kind: 'error', message: 'render failed' })
    observer.emit(frame, true)
    expect(previews.subscriptions.get(`fixture:${AVAILABLE}`)).toBe(1)
    observer.emit(frame, false)
    observer.emit(frame, true)
    expect(previews.subscriptions.get(`fixture:${AVAILABLE}`)).toBe(2)
    view.dispose()
  })

  it('refreshes an evicted decoded URL on visibility re-entry', () => {
    const document = new FakeDocument()
    ;(document as unknown as { defaultView: { IntersectionObserver: typeof IntersectionObserver } })
      .defaultView = { IntersectionObserver: PreviewObserverFixture as unknown as typeof IntersectionObserver }
    const host = new FakeElement(document)
    const previews = new PreviewFixture()
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('archive'),
      previewService: previews,
      motionClock: { wait: async () => {} },
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
    const root = view.element as unknown as FakeElement
    const record = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    const frame = record.querySelector('.curse-folio-puzzle-preview-frame')! as unknown as Element
    const observer = PreviewObserverFixture.latest!

    observer.emit(frame, true)
    previews.publish(COMPLETED, { kind: 'ready', url: 'blob:first' })
    previews.evict(COMPLETED)
    observer.emit(frame, false)
    observer.emit(frame, true)
    expect(previews.subscriptions.get(`fixture:${COMPLETED}`)).toBe(2)
    previews.publish(COMPLETED, { kind: 'ready', url: 'blob:second' })
    expect(record.querySelector('.curse-folio-puzzle-preview')!.src).toBe('blob:second')
    expect(root.querySelector('.curse-folio-puzzle-preview-inspection')).toBe(null)
    view.dispose()
  })

  it('owns the approved physical folio hierarchy and immediate archive affordances', () => {
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
      onArtifactDragStart: () => {},
      onArtifactDragMove: () => {},
      onArtifactDragEnd: () => {},
      onArtifactDragCancel: () => {},
    })
    const root = view.element as unknown as FakeElement
    const dossier = root.querySelector('.active-dossier')!
    const sheet = root.querySelector('.record-grid')!
    const lockedRecord = root.querySelector(`[data-puzzle="${LOCKED}"]`)!
    const lockedCulture = root.querySelector(`[data-culture="${SECOND_CULTURE}"]`)!
    expect(root.querySelectorAll('.folio-board-lower')).toHaveLength(1)
    expect(root.querySelectorAll('.dossier-underlay')).toHaveLength(2)
    expect(root.querySelectorAll('.guard-leaf-layer')).toHaveLength(1)
    expect(root.querySelectorAll('.active-dossier')).toHaveLength(1)
    expect(root.querySelectorAll('.folio-cover')).toHaveLength(1)
    expect(root.querySelectorAll('.inspection-stage')).toHaveLength(1)
    expect(root.querySelectorAll('.record-grid')).toHaveLength(1)
    expect(root.querySelectorAll('.curse-folio-dossier')).toHaveLength(0)
    expect(root.querySelectorAll('.curse-folio-sheet')).toHaveLength(0)
    expect(lockedRecord.querySelector('.record-guard')).not.toBeNull()
    expect(lockedCulture.querySelector('.record-guard')).not.toBeNull()
    expect(sheet.getAttribute('role')).toBe('list')
    expect(sheet.tagName).toBe('UL')
    expect(sheet.getAttribute('tabindex')).toBe('0')
    expect(root.querySelectorAll('.curse-folio-page')).toHaveLength(0)
    expect(sheet.scrollTop).toBe(85)
    expect(root.querySelector('.dossier-title')!.textContent)
      .toBe('Excavation archive · First dossier')
    expect(root.querySelector('.dossier-title')!.tagName).toBe('H2')
    expect(lockedRecord.tagName).toBe('BUTTON')
    expect(lockedRecord.getAttribute('role')).toBeNull()
    expect(root.querySelector(`[data-culture="${FIRST_CULTURE}"]`)!
      .querySelector('.curse-folio-culture-label')!.textContent).toBe('First')

    root.querySelector(`[data-puzzle="${COMPLETED}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-puzzle="${LOCKED}"]`)!.dispatchEvent(new Event('click'))
    root.querySelector(`[data-culture="${SECOND_CULTURE}"]`)!.dispatchEvent(new Event('click'))
    expect(selected).toEqual([COMPLETED, AVAILABLE])
    expect(refused).toEqual([LOCKED, SECOND_CULTURE])
    expect(cultures).toEqual([])

    view.update({ ...projection('archive'), selectedCulture: SECOND_CULTURE, selectedScroll: 0 })
    expect(root.querySelector('.active-dossier')).toBe(dossier)
    expect(root.querySelectorAll('.active-dossier')).toHaveLength(1)
  })

  it('never navigates in puzzle mode and exposes drag lifecycle only for completed records', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const calls: string[] = []
    const clock = new PendingMotionClock()
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('puzzle'),
      motionClock: clock,
      onSelectPuzzle: () => calls.push('navigate'),
      onRefusePuzzle: () => calls.push('refuse'),
      onSelectCulture: () => {},
      onRefuseCulture: () => {},
      onScroll: () => {},
      onArtifactDragStart: (id) => calls.push(`start:${id}`),
      onArtifactDragMove: (id) => calls.push(`move:${id}`),
      onArtifactDragEnd: (id) => calls.push(`end:${id}`),
      onArtifactDragCancel: (id) => calls.push(`cancel:${id}`),
    })
    const root = view.element as unknown as FakeElement
    const completed = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    const available = root.querySelector(`[data-puzzle="${AVAILABLE}"]`)!
    const positioner = root.querySelector('.inspection-positioner')!

    available.dispatchEvent(new Event('click'))
    available.dispatchEvent(eventWith('pointerdown', { button: 0, pointerId: 4, clientX: 10, clientY: 20 }))
    completed.dispatchEvent(eventWith('pointerdown', { button: 0, pointerId: 7, clientX: 30, clientY: 40 }))
    completed.dispatchEvent(eventWith('pointermove', { pointerId: 7, clientX: 44, clientY: 55 }))
    expect(completed.classList.contains('is-inspection-source')).toBe(true)
    expect(positioner.classList.contains('is-artifact-lifted')).toBe(true)
    expect(positioner.style.getPropertyValue('--folio-drag-x')).toBe('44px')
    expect(positioner.style.getPropertyValue('--folio-drag-y')).toBe('55px')
    completed.dispatchEvent(eventWith('pointerup', { pointerId: 7, clientX: 50, clientY: 60 }))
    expect(positioner.classList.contains('is-artifact-lifted')).toBe(false)
    expect(positioner.classList.contains('is-returning')).toBe(true)
    expect(root.dataset.motionRecordTarget).toBe(COMPLETED)
    expect(root.dataset.motionRecordKind).toBe('return')
    expect(clock.waits.map(({ milliseconds }) => milliseconds)).toEqual([340])
    expect(calls).toEqual([
      `start:${COMPLETED}`,
      `move:${COMPLETED}`,
      `end:${COMPLETED}`,
    ])
    view.dispose()
  })

  it('drives full and reduced dossier and refusal motion through the complete authority', () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const clock = new PendingMotionClock()
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('archive'),
      motionClock: clock,
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
    const root = view.element as unknown as FakeElement

    view.update({ ...projection('archive'), selectedCulture: SECOND_CULTURE })
    expect(clock.waits.map(({ milliseconds }) => milliseconds)).toEqual([380, 260])
    expect(root.dataset.motionDossierTarget).toBe(SECOND_CULTURE)
    expect(root.dataset.motionDossierKind).toBe('replace')
    expect(root.style.getPropertyValue('--motion-dossier-duration')).toBe('260ms')

    view.resistCulture(SECOND_CULTURE)
    expect(clock.waits.map(({ milliseconds }) => milliseconds)).toEqual([380, 260, 320])
    expect(clock.waits[0]!.signal.aborted).toBe(false)
    expect(root.dataset.motionDossierTarget).toBe(SECOND_CULTURE)
    expect(root.dataset.motionDossierKind).toBe('replace')
    expect(root.dataset.motionRestrictionTarget).toBe(SECOND_CULTURE)
    expect(root.dataset.motionRestrictionKind).toBe('refuse')

    view.update({ ...projection('archive'), reducedMotion: true })
    expect(clock.waits.map(({ milliseconds }) => milliseconds)).toEqual([380, 90])
    expect(root.dataset.motionDossierTarget).toBe(FIRST_CULTURE)
    expect(root.dataset.motionDossierKind).toBe('reduced')
    expect(root.style.getPropertyValue('--motion-dossier-duration')).toBe('90ms')

    view.resistPuzzle(LOCKED)
    expect(clock.waits.map(({ milliseconds }) => milliseconds)).toEqual([380, 90, 90])
    expect(clock.waits[0]!.signal.aborted).toBe(false)
    expect(root.dataset.motionDossierTarget).toBe(FIRST_CULTURE)
    expect(root.dataset.motionDossierKind).toBe('reduced')
    expect(root.dataset.motionRestrictionTarget).toBe(LOCKED)
    expect(root.dataset.motionRestrictionKind).toBe('reduced')

    view.dispose()
    expect(clock.waits).toEqual([])
    expect(Object.keys(root.dataset).filter(
      (name) => name !== 'motion' && name.startsWith('motion'),
    )).toEqual([])
    for (const channel of ['dossier', 'restriction']) {
      expect(root.classList.contains(`is-motion-${channel}`)).toBe(false)
      expect(root.style.getPropertyValue(`--motion-${channel}-duration`)).toBe('')
    }
  })

  it('cancels an active drag exactly once before update or disposal removes its record', async () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const calls: string[] = []
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('puzzle'),
      motionClock: { wait: async () => {} },
      onSelectPuzzle: () => {},
      onRefusePuzzle: () => {},
      onSelectCulture: () => {},
      onRefuseCulture: () => {},
      onScroll: () => {},
      onArtifactDragStart: () => {},
      onArtifactDragMove: () => {},
      onArtifactDragEnd: () => calls.push('end'),
      onArtifactDragCancel: () => calls.push('cancel'),
    })
    const root = view.element as unknown as FakeElement
    const first = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    first.dispatchEvent(eventWith('pointerdown', {
      button: 0, pointerId: 11, clientX: 30, clientY: 40,
    }))
    view.update(projection('puzzle'))
    expect(calls).toEqual(['cancel'])
    expect(first.hasPointerCapture(11)).toBe(false)
    expect(first.classList.contains('is-inspection-source')).toBe(true)
    first.dispatchEvent(eventWith('pointercancel', { pointerId: 11, clientX: 30, clientY: 40 }))
    expect(calls).toEqual(['cancel'])

    await Promise.resolve()
    await Promise.resolve()
    expect(first.classList.contains('is-inspection-source')).toBe(false)

    const second = root.querySelector(`[data-puzzle="${COMPLETED}"]`)!
    second.dispatchEvent(eventWith('pointerdown', {
      button: 0, pointerId: 12, clientX: 50, clientY: 60,
    }))
    view.dispose()
    expect(calls).toEqual(['cancel', 'cancel'])
    expect(second.hasPointerCapture(12)).toBe(false)
    expect(root.querySelector('.inspection-positioner')!.classList.contains('is-artifact-lifted'))
      .toBe(false)
  })

  it('owns local cover state and detects a real restricted packet release', async () => {
    const document = new FakeDocument()
    const host = new FakeElement(document)
    const view = mountFolioView({
      host: host as unknown as HTMLElement,
      projection: projection('archive'),
      motionClock: { wait: async () => {} },
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
    const root = view.element as unknown as FakeElement
    const cover = root.querySelector('.folio-cover')!
    expect(root.dataset.cover).toBe('open')
    expect(root.dataset.motionCoverKind).toBe('open')
    await Promise.resolve()
    await Promise.resolve()
    cover.dispatchEvent(new Event('click'))
    expect(root.dataset.cover).toBe('closed')
    expect(root.dataset.motionCoverKind).toBe('close')

    const released = projection('archive')
    const firstCulture = released.cultures[0]!
    const releasedRecords = firstCulture.records.map((record) => record.id === LOCKED
      ? { ...record, status: 'unlocked' as const, affordance: 'select' as const }
      : record)
    view.update({
      ...released,
      cultures: [{ ...firstCulture, records: releasedRecords }, ...released.cultures.slice(1)],
    })
    expect(root.dataset.restriction).toBe('released')
    expect(root.dataset.motionPacketKind).toBe('release')
    expect(root.querySelector(`[data-puzzle="${LOCKED}"]`)!.dataset.packetState)
      .toBe('released')
    view.dispose()
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
    const aperture = root.querySelector('.curse-production-aperture')!
    expect(stage.children.map(({ className }) => className)).toEqual([
      'curse-production-aperture',
      'curse-production-gasket curse-decoration',
      'curse-production-timeline',
    ])
    expect(aperture.children.map(({ className }) => className)).toEqual([
      'curse-production-substrate curse-decoration',
      'curse-production-proof-slot',
    ])
    expect(root.children.map(({ className }) => className)).toEqual([
      'curse-production-desk',
      'curse-production-lens',
      'curse-production-folio-host',
      'curse-production-folio-drawer-toggle',
      'curse-production-presentation-host',
    ])
    expect(lens.proofCanvasSlot).toBe(aperture.children[1])
    expect(lens.folioHost).toBe(root.children[2])
    expect(root.querySelector('.curse-production-timeline-handle-slot')).not.toBeNull()
    expect(stage.style.getPropertyValue('--curse-lens-left')).toBe('600px')
    expect(stage.style.getPropertyValue('--curse-lens-top')).toBe('0px')
    expect(stage.style.getPropertyValue('--curse-lens-size')).toBe('1000px')
    expect(lens.folioHost.style.getPropertyValue('--curse-folio-width')).toBe('628.8px')

    lens.setLayout(1920, 1080)
    expect(stage.style.getPropertyValue('--curse-lens-left')).toBe('840px')
    expect(stage.style.getPropertyValue('--curse-lens-top')).toBe('0px')
    expect(stage.style.getPropertyValue('--curse-lens-size')).toBe('1080px')
  })

  it('references only the approved lens assets and imports production CSS from runtime modules', () => {
    const folioSource = readFileSync('src/game/interface/folio-view.ts', 'utf8')
    const lensSource = readFileSync('src/game/interface/lens-environment.ts', 'utf8')
    const folioCss = readFileSync('src/game/interface/folio.css', 'utf8')
    const motionCss = readFileSync('src/game/interface/folio-motion.css', 'utf8')
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
    expect(folioSource).toContain("import './folio-motion.css'")
    expect([...folioCss.matchAll(/@keyframes\s+([\w-]+)/g)]).toEqual([])
    expect([...motionCss.matchAll(/@keyframes\s+reduced-depth\b/g)]).toHaveLength(1)
    expect([...`${folioCss}\n${motionCss}`.matchAll(/brightness\(1\.04\)/g)]).toHaveLength(1)
    expect(folioCss).toContain('scrollbar-width: none')
    for (const asset of [
      'guard-leaf.png',
      'priority-band.png',
    ]) expect(folioCss).toContain(asset)
    expect(folioCss).not.toMatch(/mount-(?:photo|rubbing|tracing)\.png/)
    expect(folioCss).toContain('.curse-folio-puzzle-preview-frame')
    expect(folioCss).not.toContain('.curse-folio-puzzle-preview-inspection')
    expect(folioCss).toContain('clearance-slip.png')
    expect(folioCss).toContain('restricted-sleeve.png')
    expect(lensCss).toContain('background: #07090c')
    expect(lensCss).toMatch(/\.curse-production-aperture\s*{[^}]*inset: 7\.57% 13\.62% 19\.65%;/s)
    expect(lensCss).toMatch(/\.curse-production-proof-slot\s*{[^}]*inset: 0;/s)
    expect(lensCss).toMatch(/\.curse-production-substrate\s*{[^}]*top: -8%;[^}]*left: -8%;[^}]*width: 116%;[^}]*height: 116%;/s)
    expect(lensCss).toMatch(/\.curse-production-gasket\s*{[^}]*inset: 0;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline\s*{[^}]*inset: 0;[^}]*width: 100%;[^}]*height: 100%;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline\s*{[^}]*pointer-events: none;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline-housing\s*{[^}]*inset: 0;[^}]*width: 100%;[^}]*height: 100%;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline-handle-slot\s*{[^}]*inset: 0;[^}]*width: 100%;[^}]*height: 100%;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline-handle\s*{[^}]*inset: 0;[^}]*width: 100%;[^}]*height: 100%;/s)
    expect(lensCss).toMatch(/\.curse-production-timeline-control\s*{[^}]*pointer-events: auto;/s)
  })
})
