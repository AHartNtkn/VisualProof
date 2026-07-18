import type { CultureId, PuzzleId } from '../types'
import { clampSheetScroll } from './folio-layout'
import type {
  FolioProjection,
  FolioRecordProjection,
} from './folio-projection'
import { FolioMotion, type FolioMotionClock } from './folio-motion'
import './folio.css'
import './folio-motion.css'

export type FolioDragSample = {
  readonly pointerId: number
  readonly clientX: number
  readonly clientY: number
}

export type FolioViewOptions = {
  readonly host: HTMLElement
  readonly projection: FolioProjection
  readonly inputAllowed?: () => boolean
  readonly motionClock?: FolioMotionClock
  readonly onSelectPuzzle: (puzzle: PuzzleId) => void
  readonly onRefusePuzzle: (puzzle: PuzzleId) => void
  readonly onSelectCulture: (culture: CultureId) => void
  readonly onRefuseCulture: (culture: CultureId) => void
  readonly onScroll: (culture: CultureId, scroll: number) => void
  readonly onTheoremDragStart: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onTheoremDragMove: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onTheoremDragEnd: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onTheoremDragCancel: (puzzle: PuzzleId, sample: FolioDragSample) => void
}

export type MountedFolioView = {
  readonly element: HTMLElement
  update(projection: FolioProjection): void
  resistPuzzle(puzzle: PuzzleId): void
  resistCulture(culture: CultureId): void
  dispose(): void
}

const specimenByPuzzle: Readonly<Record<string, URL>> = {
  'two-veils': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyr-ossuary-seal.png', import.meta.url),
  'four-veils': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyr-cairn-seal-iv.png', import.meta.url),
  'forked-veil': new URL('../../../assets/interface/generated/excavation-folio/specimens/orra-gate-fragment.png', import.meta.url),
  'echoed-veil': new URL('../../../assets/interface/generated/excavation-folio/specimens/tel-vey-chamber-seal-viii.png', import.meta.url),
  'single-mark-return': new URL('../../../assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png', import.meta.url),
  'two-mark-projection': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png', import.meta.url),
  'blank-witness': new URL('../../../assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png', import.meta.url),
}

const element = <K extends keyof HTMLElementTagNameMap>(
  document: Document,
  tag: K,
  className: string,
): HTMLElementTagNameMap[K] => {
  const created = document.createElement(tag)
  created.className = className
  return created
}

const dragSample = (event: PointerEvent): FolioDragSample => ({
  pointerId: event.pointerId,
  clientX: event.clientX,
  clientY: event.clientY,
})

export function mountFolioView(options: FolioViewOptions): MountedFolioView {
  const document = options.host.ownerDocument
  const root = element(document, 'section', 'curse-folio')
  root.setAttribute('aria-label', 'Excavation folio')
  const cultures = element(document, 'nav', 'curse-folio-cultures')
  cultures.setAttribute('aria-label', 'Cultural dossiers')
  const dossier = element(document, 'section', 'curse-folio-dossier')
  root.append(cultures, dossier)
  options.host.append(root)

  const motion = new FolioMotion(root, options.motionClock)
  let current = options.projection
  let renderListeners = new AbortController()
  let activeDrag: {
    puzzle: PuzzleId
    pointerId: number
    record: HTMLElement
    lastSample: FolioDragSample
  } | null = null
  let restrictionTarget: HTMLElement | null = null
  let restrictionGeneration = 0
  const inputAllowed = (): boolean => options.inputAllowed?.() ?? true

  const clearRestriction = (): void => {
    restrictionGeneration += 1
    restrictionTarget?.classList.remove('is-restriction-target')
    restrictionTarget = null
    motion.settleAll()
  }

  const resist = (
    target: HTMLElement | null,
    identity: PuzzleId | CultureId,
  ): void => {
    if (target === null) return
    clearRestriction()
    const generation = restrictionGeneration
    restrictionTarget = target
    target.classList.add('is-restriction-target')
    void motion.restrictedRefusal(identity, current.reducedMotion).finally(() => {
      if (generation !== restrictionGeneration) return
      target.classList.remove('is-restriction-target')
      if (restrictionTarget === target) restrictionTarget = null
    })
  }

  const listen = (
    target: EventTarget,
    type: string,
    listener: EventListener,
  ): void => target.addEventListener(type, listener, { signal: renderListeners.signal })

  const clearDragPresentation = (
    drag: NonNullable<typeof activeDrag>,
  ): void => {
    const { pointerId, record } = drag
    if (record.hasPointerCapture(pointerId)) record.releasePointerCapture(pointerId)
    record.classList.remove('is-theorem-lifted')
    record.style.removeProperty('--folio-drag-x')
    record.style.removeProperty('--folio-drag-y')
  }

  const cancelActiveDrag = (): void => {
    if (activeDrag === null) return
    const drag = activeDrag
    activeDrag = null
    clearDragPresentation(drag)
    options.onTheoremDragCancel(drag.puzzle, drag.lastSample)
  }

  const releaseDrag = (event: PointerEvent, cancelled: boolean): void => {
    if (activeDrag === null || activeDrag.pointerId !== event.pointerId) return
    const drag = activeDrag
    activeDrag = null
    clearDragPresentation(drag)
    const sample = dragSample(event)
    if (cancelled || !inputAllowed()) options.onTheoremDragCancel(drag.puzzle, sample)
    else options.onTheoremDragEnd(drag.puzzle, sample)
  }

  const recordElement = (record: FolioRecordProjection): HTMLElement => {
    const interactive = current.mode === 'archive'
    const node = interactive
      ? element(document, 'button', 'curse-folio-record')
      : element(document, 'article', 'curse-folio-record')
    if (interactive) (node as HTMLButtonElement).type = 'button'
    node.dataset.puzzle = record.id
    node.dataset.status = record.status
    node.dataset.affordance = record.affordance
    node.setAttribute('role', 'listitem')
    if (record.status === 'locked') node.setAttribute('aria-disabled', 'true')

    const mount = element(document, 'span', 'curse-folio-record-mount')
    const specimen = specimenByPuzzle[record.id]
    if (specimen !== undefined) {
      const image = element(document, 'img', 'curse-folio-specimen')
      image.src = specimen.href
      image.alt = ''
      image.setAttribute('aria-hidden', 'true')
      mount.append(image)
    }
    const identity = element(document, 'span', 'curse-folio-record-identity')
    const name = element(document, 'strong', 'curse-folio-record-name')
    name.textContent = record.name
    const accession = element(document, 'small', 'curse-folio-record-accession')
    accession.textContent = record.accession ?? 'Catalog entry pending accession'
    const summary = element(document, 'span', 'curse-folio-record-summary')
    summary.textContent = record.summary
    identity.append(name, accession, summary)
    node.append(mount, identity)

    if (record.affordance === 'select') {
      listen(node, 'click', () => { if (inputAllowed()) options.onSelectPuzzle(record.id) })
    } else if (record.affordance === 'resist') {
      listen(node, 'click', () => { if (inputAllowed()) options.onRefusePuzzle(record.id) })
    } else if (record.affordance === 'drag-theorem') {
      listen(node, 'pointerdown', ((rawEvent: PointerEvent) => {
        if (rawEvent.button !== 0 || activeDrag !== null || !inputAllowed()) return
        rawEvent.preventDefault()
        const sample = dragSample(rawEvent)
        activeDrag = {
          puzzle: record.id,
          pointerId: rawEvent.pointerId,
          record: node,
          lastSample: sample,
        }
        node.setPointerCapture(rawEvent.pointerId)
        node.classList.add('is-theorem-lifted')
        node.style.setProperty('--folio-drag-x', `${rawEvent.clientX}px`)
        node.style.setProperty('--folio-drag-y', `${rawEvent.clientY}px`)
        options.onTheoremDragStart(record.id, sample)
      }) as EventListener)
      listen(node, 'pointermove', ((rawEvent: PointerEvent) => {
        if (activeDrag?.pointerId !== rawEvent.pointerId) return
        const sample = dragSample(rawEvent)
        activeDrag.lastSample = sample
        node.style.setProperty('--folio-drag-x', `${rawEvent.clientX}px`)
        node.style.setProperty('--folio-drag-y', `${rawEvent.clientY}px`)
        options.onTheoremDragMove(record.id, sample)
      }) as EventListener)
      listen(node, 'pointerup', ((event: PointerEvent) => releaseDrag(event, false)) as EventListener)
      listen(node, 'pointercancel', ((event: PointerEvent) => releaseDrag(event, true)) as EventListener)
    }
    return node
  }

  const render = (previousCulture: CultureId | null): void => {
    cancelActiveDrag()
    clearRestriction()
    renderListeners.abort()
    renderListeners = new AbortController()
    root.dataset.mode = current.mode
    root.dataset.activeDossier = current.selectedCulture
    root.dataset.motion = current.reducedMotion ? 'reduced' : 'full'

    const cultureControls = current.cultures.map((culture) => {
      const control = element(document, 'button', 'curse-folio-culture-tab')
      control.type = 'button'
      control.dataset.culture = culture.id
      control.textContent = culture.name
      control.setAttribute('aria-pressed', String(culture.id === current.selectedCulture))
      if (!culture.unlocked) control.setAttribute('aria-disabled', 'true')
      listen(control, 'click', () => {
        if (!inputAllowed()) return
        if (culture.unlocked) options.onSelectCulture(culture.id)
        else options.onRefuseCulture(culture.id)
      })
      return control
    })
    cultures.replaceChildren(...cultureControls)

    const selected = current.cultures.find(({ id }) => id === current.selectedCulture)
      ?? current.cultures[0]
    if (selected === undefined) {
      dossier.replaceChildren()
      return
    }
    const header = element(document, 'header', 'curse-folio-dossier-header')
    const title = element(document, 'h2', 'curse-folio-dossier-title')
    title.textContent = selected.name
    const note = element(document, 'p', 'curse-folio-dossier-note')
    note.textContent = selected.historicalSummary
    header.append(title, note)
    const sheet = element(document, 'div', 'curse-folio-sheet')
    sheet.tabIndex = 0
    sheet.setAttribute('tabindex', '0')
    sheet.setAttribute('role', 'list')
    sheet.setAttribute('aria-label', `${selected.name} artifact records`)
    sheet.append(...selected.records.map(recordElement))
    listen(sheet, 'scroll', () => {
      if (!inputAllowed()) return
      options.onScroll(
        selected.id,
        clampSheetScroll(sheet.scrollTop, sheet.scrollHeight, sheet.clientHeight),
      )
    })
    dossier.replaceChildren(header, sheet)
    sheet.scrollTop = current.selectedScroll
    if (previousCulture !== null && previousCulture !== selected.id) {
      void motion.dossier(selected.id, current.reducedMotion)
    }
  }

  render(null)
  let disposed = false
  return {
    element: root,
    update(next) {
      if (disposed) return
      const previousCulture = current.selectedCulture
      current = next
      render(previousCulture)
    },
    resistPuzzle(puzzle) {
      if (disposed) return
      resist(root.querySelector<HTMLElement>(`[data-puzzle="${puzzle}"]`), puzzle)
    },
    resistCulture(culture) {
      if (disposed) return
      resist(root.querySelector<HTMLElement>(`[data-culture="${culture}"]`), culture)
    },
    dispose() {
      if (disposed) return
      disposed = true
      cancelActiveDrag()
      clearRestriction()
      renderListeners.abort()
      root.remove()
    },
  }
}
