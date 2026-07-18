import type { CultureId, PuzzleId } from '../types'
import { clampSheetScroll } from './folio-layout'
import type {
  FolioProjection,
  FolioRecordProjection,
} from './folio-projection'
import { FolioDossierMotion, type FolioMotionClock } from './folio-motion'
import './folio.css'

export type FolioDragSample = {
  readonly pointerId: number
  readonly clientX: number
  readonly clientY: number
}

export type FolioViewOptions = {
  readonly host: HTMLElement
  readonly projection: FolioProjection
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

  const motion = new FolioDossierMotion(root, options.motionClock)
  let current = options.projection
  let renderListeners = new AbortController()
  let activeDrag: { puzzle: PuzzleId; pointerId: number; record: HTMLElement } | null = null

  const listen = (
    target: EventTarget,
    type: string,
    listener: EventListener,
  ): void => target.addEventListener(type, listener, { signal: renderListeners.signal })

  const releaseDrag = (event: PointerEvent, cancelled: boolean): void => {
    if (activeDrag === null || activeDrag.pointerId !== event.pointerId) return
    const { puzzle, pointerId, record } = activeDrag
    activeDrag = null
    record.classList.remove('is-theorem-lifted')
    record.style.removeProperty('--folio-drag-x')
    record.style.removeProperty('--folio-drag-y')
    if (record.hasPointerCapture(pointerId)) record.releasePointerCapture(pointerId)
    const sample = dragSample(event)
    if (cancelled) options.onTheoremDragCancel(puzzle, sample)
    else options.onTheoremDragEnd(puzzle, sample)
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
      listen(node, 'click', () => options.onSelectPuzzle(record.id))
    } else if (record.affordance === 'resist') {
      listen(node, 'click', () => options.onRefusePuzzle(record.id))
    } else if (record.affordance === 'drag-theorem') {
      listen(node, 'pointerdown', ((rawEvent: PointerEvent) => {
        if (rawEvent.button !== 0 || activeDrag !== null) return
        rawEvent.preventDefault()
        activeDrag = { puzzle: record.id, pointerId: rawEvent.pointerId, record: node }
        node.setPointerCapture(rawEvent.pointerId)
        node.classList.add('is-theorem-lifted')
        node.style.setProperty('--folio-drag-x', `${rawEvent.clientX}px`)
        node.style.setProperty('--folio-drag-y', `${rawEvent.clientY}px`)
        options.onTheoremDragStart(record.id, dragSample(rawEvent))
      }) as EventListener)
      listen(node, 'pointermove', ((rawEvent: PointerEvent) => {
        if (activeDrag?.pointerId !== rawEvent.pointerId) return
        node.style.setProperty('--folio-drag-x', `${rawEvent.clientX}px`)
        node.style.setProperty('--folio-drag-y', `${rawEvent.clientY}px`)
        options.onTheoremDragMove(record.id, dragSample(rawEvent))
      }) as EventListener)
      listen(node, 'pointerup', ((event: PointerEvent) => releaseDrag(event, false)) as EventListener)
      listen(node, 'pointercancel', ((event: PointerEvent) => releaseDrag(event, true)) as EventListener)
    }
    return node
  }

  const render = (previousCulture: CultureId | null): void => {
    renderListeners.abort()
    renderListeners = new AbortController()
    activeDrag = null
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
    sheet.scrollTop = current.selectedScroll
    listen(sheet, 'scroll', () => {
      options.onScroll(
        selected.id,
        clampSheetScroll(sheet.scrollTop, sheet.scrollHeight, sheet.clientHeight),
      )
    })
    dossier.replaceChildren(header, sheet)
    if (previousCulture !== null && previousCulture !== selected.id) {
      void motion.replace(selected.id, current.reducedMotion)
    } else if (current.reducedMotion) {
      motion.settle()
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
    dispose() {
      if (disposed) return
      disposed = true
      renderListeners.abort()
      motion.settle()
      root.remove()
    },
  }
}
