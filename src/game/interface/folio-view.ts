import type { CultureId, PuzzleId } from '../types'
import { clampSheetScroll } from './folio-layout'
import type { FolioProjection, FolioRecordProjection } from './folio-projection'
import { FolioMotion, type FolioMotionClock } from './folio-motion'
import type {
  PuzzlePreviewService,
  PuzzlePreviewState,
} from './puzzle-preview-service'
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
  readonly previewService?: PuzzlePreviewService
  readonly inputAllowed?: () => boolean
  readonly motionClock?: FolioMotionClock
  readonly onSelectPuzzle: (puzzle: PuzzleId) => void
  readonly onRefusePuzzle: (puzzle: PuzzleId) => void
  readonly onSelectCulture: (culture: CultureId) => void
  readonly onRefuseCulture: (culture: CultureId) => void
  readonly onScroll: (culture: CultureId, scroll: number) => void
  readonly onArtifactDragStart: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onArtifactDragMove: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onArtifactDragEnd: (puzzle: PuzzleId, sample: FolioDragSample) => void
  readonly onArtifactDragCancel: (puzzle: PuzzleId, sample: FolioDragSample) => void
}

export type MountedFolioView = {
  readonly element: HTMLElement
  update(projection: FolioProjection): void
  resistPuzzle(puzzle: PuzzleId): void
  resistCulture(culture: CultureId): void
  dispose(): void
}

type ActiveDrag = {
  readonly puzzle: PuzzleId
  readonly pointerId: number
  readonly source: HTMLElement
  readonly sourceRect: RectSnapshot | null
  lastSample: FolioDragSample
}

type RectSnapshot = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
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

const snapshotRect = (node: HTMLElement): RectSnapshot | null => {
  if (typeof node.getBoundingClientRect !== 'function') return null
  const { left, top, width, height } = node.getBoundingClientRect()
  return { left, top, width, height }
}

export function mountFolioView(options: FolioViewOptions): MountedFolioView {
  const document = options.host.ownerDocument
  const root = element(document, 'section', 'curse-folio folio-foundation')
  root.setAttribute('aria-label', 'Excavation conservation folio')

  const lowerBoard = element(document, 'span', 'folio-board folio-board-lower')
  lowerBoard.setAttribute('aria-hidden', 'true')
  const underlays = options.projection.cultures.slice(0, 2).map((culture, index) => {
    const underlay = element(
      document,
      'span',
      `dossier-underlay dossier-underlay-${index + 1}`,
    )
    underlay.dataset.dossierUnderlay = culture.id
    underlay.setAttribute('aria-hidden', 'true')
    return underlay
  })
  const guardLeaf = element(document, 'span', 'guard-leaf-layer')
  guardLeaf.setAttribute('aria-hidden', 'true')

  const dossier = element(document, 'section', 'active-dossier')
  const cultures = element(document, 'nav', 'culture-tabs curse-folio-cultures')
  cultures.setAttribute('aria-label', 'Cultural dossiers')
  const dossierHeader = element(document, 'header', 'dossier-header')
  const dossierTitle = element(document, 'h2', 'dossier-title')
  const dossierNote = element(document, 'p', 'dossier-note')
  dossierHeader.append(dossierTitle, dossierNote)
  const sheet = element(document, 'ul', 'record-grid')
  sheet.tabIndex = 0
  sheet.setAttribute('tabindex', '0')
  sheet.setAttribute('role', 'list')
  dossier.append(cultures, dossierHeader, sheet)

  const cover = element(document, 'button', 'folio-cover')
  cover.type = 'button'
  cover.dataset.coverControl = ''
  const coverSurface = element(document, 'span', 'cover-surface')
  coverSurface.setAttribute('aria-hidden', 'true')
  const coverCloth = element(document, 'span', 'cover-cloth')
  const coverLabel = element(document, 'span', 'cover-label')
  coverLabel.textContent = 'Excavation register · conservation folio'
  const coverEdge = element(document, 'span', 'cover-edge')
  coverSurface.append(coverCloth, coverLabel, coverEdge)
  const coverSpine = element(document, 'span', 'cover-spine-hit')
  coverSpine.dataset.coverSpine = ''
  coverSpine.setAttribute('aria-hidden', 'true')
  cover.append(coverSurface, coverSpine)

  const inspectionStage = element(document, 'section', 'inspection-stage')
  inspectionStage.setAttribute('aria-hidden', 'true')
  const inspectionPositioner = element(document, 'div', 'inspection-positioner')
  const inspectionRecord = element(document, 'div', 'inspection-record')
  inspectionPositioner.append(inspectionRecord)
  inspectionStage.append(inspectionPositioner)

  root.append(
    lowerBoard,
    ...underlays,
    guardLeaf,
    dossier,
    cover,
    inspectionStage,
  )
  options.host.append(root)

  const motion = new FolioMotion(root, options.motionClock)
  const listeners = new AbortController()
  const recordElements = new Map<PuzzleId, HTMLElement>()
  const recordItems = new Map<PuzzleId, HTMLLIElement>()
  const cultureElements = new Map<CultureId, HTMLButtonElement>()
  const previewStates = new Map<string, PuzzlePreviewState>()
  const previewElements = new Map<string, Set<{
    readonly frame: HTMLElement
    readonly image: HTMLImageElement
    readonly status: HTMLElement
  }>>()
  const previewSubscriptions = new Map<Element, () => void>()
  const pendingPreviews = new Map<Element, FolioRecordProjection>()
  const failedPreviews = new Map<Element, {
    readonly record: FolioRecordProjection
    exited: boolean
  }>()
  let current = options.projection
  let coverState: 'open' | 'closed' = current.mode === 'archive' ? 'closed' : 'open'
  let activeDrag: ActiveDrag | null = null
  let returningSource: HTMLElement | null = null
  let recordGeneration = 0
  let restrictionTarget: HTMLElement | null = null
  let restrictionGeneration = 0
  let previewObserver: IntersectionObserver | null = null
  let disposed = false
  const inputAllowed = (): boolean => options.inputAllowed?.() ?? true

  const listen = (
    target: EventTarget,
    type: string,
    listener: EventListener,
  ): void => target.addEventListener(type, listener, { signal: listeners.signal })

  const selectedCulture = () => current.cultures
    .find(({ id }) => id === current.selectedCulture) ?? current.cultures[0]

  const projectedRecord = (puzzle: PuzzleId): FolioRecordProjection | null => {
    for (const culture of current.cultures) {
      const record = culture.records.find(({ id }) => id === puzzle)
      if (record !== undefined) return record
    }
    return null
  }

  const applyPreviewState = (
    target: { readonly frame: HTMLElement; readonly image: HTMLImageElement; readonly status: HTMLElement },
    state: PuzzlePreviewState,
  ): void => {
    target.frame.dataset.previewState = state.kind
    if (state.kind === 'ready') {
      target.image.src = state.url
      target.status.textContent = ''
      return
    }
    target.image.src = ''
    target.status.textContent = state.kind === 'preparing'
      ? 'Preparing preview…'
      : 'Preview unavailable'
  }

  const publishPreview = (record: FolioRecordProjection, state: PuzzlePreviewState): void => {
    previewStates.set(record.preview.key, state)
    for (const target of previewElements.get(record.preview.key) ?? []) {
      applyPreviewState(target, state)
    }
  }

  const requestPreview = (target: Element, record: FolioRecordProjection): void => {
    if (previewSubscriptions.has(target) || options.previewService === undefined) return
    const remembered = previewStates.get(record.preview.key)
    if (remembered?.kind === 'ready'
      && options.previewService.currentUrl(record.preview.key) === remembered.url) return
    if (remembered?.kind === 'ready') publishPreview(record, { kind: 'preparing' })
    let terminal = false
    const cancel = options.previewService.subscribe(
      record.preview,
      (state) => {
        publishPreview(record, state)
        if (state.kind === 'preparing') return
        terminal = true
        previewSubscriptions.get(target)?.()
        previewSubscriptions.delete(target)
        if (state.kind !== 'error' || previewObserver === null) return
        previewObserver.unobserve(target)
        failedPreviews.set(target, { record, exited: false })
        previewObserver.observe(target)
      },
    )
    if (terminal) cancel()
    else previewSubscriptions.set(target, cancel)
  }

  const failPreviewImage = (record: FolioRecordProjection): void => {
    options.previewService?.invalidate(record.preview.key)
    publishPreview(record, { kind: 'error', message: 'preview image could not be decoded' })
    for (const target of previewElements.get(record.preview.key) ?? []) {
      previewSubscriptions.get(target.frame)?.()
      previewSubscriptions.delete(target.frame)
      if (previewObserver === null) continue
      previewObserver.unobserve(target.frame)
      failedPreviews.set(target.frame, { record, exited: false })
      previewObserver.observe(target.frame)
    }
  }

  const clearPreviewBindings = (): void => {
    previewObserver?.disconnect()
    for (const cancel of previewSubscriptions.values()) cancel()
    previewSubscriptions.clear()
    pendingPreviews.clear()
    failedPreviews.clear()
    previewElements.clear()
    previewStates.clear()
  }

  const PreviewObserver = document.defaultView?.IntersectionObserver
  if (PreviewObserver !== undefined) {
    previewObserver = new PreviewObserver((entries) => {
      for (const entry of entries) {
        const failed = failedPreviews.get(entry.target)
        if (failed !== undefined) {
          if (!entry.isIntersecting) {
            failed.exited = true
          } else if (failed.exited) {
            failedPreviews.delete(entry.target)
            requestPreview(entry.target, failed.record)
          }
          continue
        }
        if (!entry.isIntersecting) continue
        const record = pendingPreviews.get(entry.target)
        if (record !== undefined) requestPreview(entry.target, record)
      }
    }, { root: sheet, rootMargin: '240px 0px' })
  }

  const clearRestriction = (): void => {
    restrictionGeneration += 1
    restrictionTarget?.classList.remove('is-restriction-target')
    restrictionTarget = null
    motion.settleRestriction()
  }

  const resist = (target: HTMLElement | null, identity: PuzzleId | CultureId): void => {
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

  const appendRecordFace = (
    target: HTMLElement,
    record: FolioRecordProjection,
    schedulePreview = true,
  ): void => {
    const face = element(document, 'span', 'record-face')
    const frame = element(document, 'span', 'curse-folio-puzzle-preview-frame')
    frame.setAttribute('aria-hidden', 'true')
    const image = element(document, 'img', 'curse-folio-puzzle-preview')
    image.alt = ''
    image.setAttribute('aria-hidden', 'true')
    image.addEventListener('error', () => {
      if (frame.dataset.previewState === 'ready') failPreviewImage(record)
    })
    const status = element(document, 'span', 'curse-folio-puzzle-preview-status')
    frame.append(image, status)
    const previewTarget = { frame, image, status }
    const state = previewStates.get(record.preview.key) ?? { kind: 'preparing' as const }
    applyPreviewState(previewTarget, state)
    if (schedulePreview) {
      let elements = previewElements.get(record.preview.key)
      if (elements === undefined) {
        elements = new Set()
        previewElements.set(record.preview.key, elements)
      }
      elements.add(previewTarget)
      if (previewObserver === null) requestPreview(frame, record)
      else {
        pendingPreviews.set(frame, record)
        previewObserver.observe(frame)
      }
    }
    const name = element(document, 'strong', 'curse-folio-record-name')
    name.textContent = `${record.levelNumber}. ${record.name}`
    const accession = element(document, 'small', 'curse-folio-record-accession')
    accession.textContent = record.accession ?? 'Catalog entry pending accession'
    const summary = element(document, 'span', 'curse-folio-record-summary')
    summary.textContent = record.summary
    face.append(frame, name, accession, summary)
    target.append(face)
  }

  const syncRecord = (
    node: HTMLElement,
    record: FolioRecordProjection,
  ): void => {
    node.dataset.puzzle = record.id
    node.dataset.status = record.status
    node.dataset.affordance = record.affordance
    node.dataset.priority = String(record.priority && record.status !== 'completed')
    delete node.dataset.mount
    node.classList.toggle('restricted-packet', record.restrictedPacket)
    if (record.restrictedPacket) {
      node.dataset.packetState = record.status === 'locked' ? 'sealed' : 'released'
    } else {
      delete node.dataset.packetState
    }
    const numberedName = `${record.levelNumber}. ${record.name}`
    node.setAttribute('aria-label', record.status === 'locked'
      ? `${numberedName}. Restricted sleeve closed.`
      : numberedName)
    node.replaceChildren()
    appendRecordFace(node, record)
    if (record.status === 'locked' || record.restrictedPacket) {
      const guard = element(document, 'span', 'curse-folio-record-guard record-guard')
      guard.dataset.obstruction = 'restricted-sleeve'
      guard.setAttribute('aria-hidden', 'true')
      const fold = element(document, 'span', 'guard-fold')
      guard.append(fold)
      if (record.restrictedPacket) {
        guard.append(
          element(document, 'span', 'packet-tie'),
          element(document, 'span', 'packet-fastener'),
        )
      }
      const band = element(document, 'span', 'guard-band')
      band.textContent = 'Restricted accession · guard remains sealed'
      guard.append(band)
      node.append(guard)
    }
  }

  const stageReturnGeometry = (drag: ActiveDrag): void => {
    if (drag.sourceRect === null) return
    const destination = snapshotRect(inspectionRecord)
    if (destination === null || destination.width === 0 || destination.height === 0) return
    inspectionRecord.style.setProperty(
      '--record-source-x',
      `${drag.sourceRect.left - destination.left}px`,
    )
    inspectionRecord.style.setProperty(
      '--record-source-y',
      `${drag.sourceRect.top - destination.top}px`,
    )
    inspectionRecord.style.setProperty(
      '--record-source-scale-x',
      String(drag.sourceRect.width / destination.width),
    )
    inspectionRecord.style.setProperty(
      '--record-source-scale-y',
      String(drag.sourceRect.height / destination.height),
    )
  }

  const positionInspection = (sample: FolioDragSample): void => {
    const containingBlock = snapshotRect(inspectionStage)
    const left = containingBlock?.left ?? 0
    const top = containingBlock?.top ?? 0
    inspectionPositioner.style.setProperty('--folio-drag-x', `${sample.clientX - left}px`)
    inspectionPositioner.style.setProperty('--folio-drag-y', `${sample.clientY - top}px`)
  }

  const clearInspection = (generation: number): void => {
    if (recordGeneration !== generation) return
    returningSource?.classList.remove('is-inspection-source')
    returningSource = null
    inspectionStage.setAttribute('aria-hidden', 'true')
    inspectionPositioner.classList.remove('is-artifact-lifted', 'is-returning')
    inspectionPositioner.style.removeProperty('--folio-drag-x')
    inspectionPositioner.style.removeProperty('--folio-drag-y')
    inspectionRecord.replaceChildren()
    delete inspectionRecord.dataset.liftedPuzzle
    delete inspectionRecord.dataset.status
    options.host.classList.remove('is-folio-drag-owner')
  }

  const returnRecord = (drag: ActiveDrag): void => {
    const generation = ++recordGeneration
    if (drag.source.hasPointerCapture(drag.pointerId)) {
      drag.source.releasePointerCapture(drag.pointerId)
    }
    returningSource = drag.source
    inspectionPositioner.classList.remove('is-artifact-lifted')
    inspectionPositioner.classList.add('is-returning')
    stageReturnGeometry(drag)
    void motion.recordInspection(drag.puzzle, false, current.reducedMotion)
      .finally(() => clearInspection(generation))
  }

  const finishDrag = (event: PointerEvent, cancelled: boolean): void => {
    if (activeDrag === null || activeDrag.pointerId !== event.pointerId) return
    const drag = activeDrag
    activeDrag = null
    drag.lastSample = dragSample(event)
    positionInspection(drag.lastSample)
    stageReturnGeometry(drag)
    if (cancelled || !inputAllowed()) {
      options.onArtifactDragCancel(drag.puzzle, drag.lastSample)
    } else {
      options.onArtifactDragEnd(drag.puzzle, drag.lastSample)
    }
    returnRecord(drag)
  }

  const cancelActiveDrag = (): void => {
    if (activeDrag === null) return
    const drag = activeDrag
    activeDrag = null
    options.onArtifactDragCancel(drag.puzzle, drag.lastSample)
    returnRecord(drag)
  }

  const beginDrag = (node: HTMLElement, record: FolioRecordProjection, event: PointerEvent): void => {
    if (
      event.button !== 0
      || activeDrag !== null
      || returningSource !== null
      || !inputAllowed()
    ) return
    event.preventDefault()
    options.host.classList.add('is-folio-drag-owner')
    const sample = dragSample(event)
    const drag: ActiveDrag = {
      puzzle: record.id,
      pointerId: event.pointerId,
      source: node,
      sourceRect: snapshotRect(node),
      lastSample: sample,
    }
    activeDrag = drag
    node.setPointerCapture(event.pointerId)
    node.classList.add('is-inspection-source')
    inspectionRecord.replaceChildren()
    appendRecordFace(inspectionRecord, record, false)
    inspectionRecord.dataset.liftedPuzzle = record.id
    inspectionRecord.dataset.status = record.status
    inspectionStage.setAttribute('aria-hidden', 'false')
    inspectionPositioner.classList.add('is-artifact-lifted')
    positionInspection(sample)
    stageReturnGeometry(drag)
    options.onArtifactDragStart(record.id, sample)
  }

  const createRecord = (record: FolioRecordProjection): HTMLElement => {
    const node = element(document, 'button', 'artifact-record curse-folio-record')
    node.type = 'button'
    listen(node, 'click', () => {
      if (!inputAllowed()) return
      const projection = projectedRecord(record.id)
      if (projection?.affordance === 'select') options.onSelectPuzzle(record.id)
      else if (projection?.affordance === 'resist') options.onRefusePuzzle(record.id)
    })
    listen(node, 'pointerdown', ((event: PointerEvent) => {
      const projection = projectedRecord(record.id)
      if (projection?.affordance === 'drag-artifact') beginDrag(node, projection, event)
    }) as EventListener)
    listen(node, 'pointermove', ((event: PointerEvent) => {
      if (activeDrag?.pointerId !== event.pointerId || activeDrag.source !== node) return
      const sample = dragSample(event)
      activeDrag.lastSample = sample
      positionInspection(sample)
      stageReturnGeometry(activeDrag)
      options.onArtifactDragMove(record.id, sample)
    }) as EventListener)
    listen(node, 'pointerup', ((event: PointerEvent) => finishDrag(event, false)) as EventListener)
    listen(node, 'pointercancel', ((event: PointerEvent) => finishDrag(event, true)) as EventListener)
    const item = element(document, 'li', 'folio-record-item')
    item.append(node)
    recordItems.set(record.id, item)
    return node
  }

  const syncCultures = (): void => {
    const controls = current.cultures.map((culture) => {
      let control = cultureElements.get(culture.id)
      if (control === undefined) {
        control = element(document, 'button', 'curse-folio-culture-tab')
        control.type = 'button'
        control.dataset.culture = culture.id
        const label = element(document, 'span', 'curse-folio-culture-label record-guard')
        control.append(label)
        listen(control, 'click', () => {
          if (!inputAllowed()) return
          const projection = current.cultures.find(({ id }) => id === culture.id)
          if (projection?.unlocked === true) options.onSelectCulture(culture.id)
          else if (projection !== undefined) options.onRefuseCulture(culture.id)
        })
        cultureElements.set(culture.id, control)
      }
      const label = control.querySelector<HTMLElement>('.curse-folio-culture-label')
      if (label !== null) label.textContent = culture.shortName
      control.setAttribute('aria-pressed', String(culture.id === current.selectedCulture))
      if (culture.unlocked) control.removeAttribute('aria-disabled')
      else control.setAttribute('aria-disabled', 'true')
      return control
    })
    cultures.replaceChildren(...controls)
  }

  const packetRecord = (projection: FolioProjection): FolioRecordProjection | null => {
    for (const culture of projection.cultures) {
      const packet = culture.records.find(({ restrictedPacket }) => restrictedPacket)
      if (packet !== undefined) return packet
    }
    return null
  }

  const syncCover = (): void => {
    root.dataset.cover = coverState
    cover.setAttribute(
      'aria-label',
      coverState === 'closed' ? 'Open folio cover' : 'Close folio cover',
    )
  }

  const render = (previous: FolioProjection | null): void => {
    clearPreviewBindings()
    cancelActiveDrag()
    clearRestriction()
    root.dataset.mode = current.mode
    root.dataset.activeDossier = current.selectedCulture
    root.dataset.motion = current.reducedMotion ? 'reduced' : 'full'
    const packet = packetRecord(current)
    root.dataset.restriction = packet?.status === 'locked' ? 'sealed' : 'released'
    syncCover()
    syncCultures()

    const selected = selectedCulture()
    if (selected === undefined) {
      dossierTitle.textContent = ''
      dossierNote.textContent = ''
      sheet.replaceChildren()
      return
    }
    dossierTitle.textContent = `Excavation archive · ${selected.shortName} dossier`
    dossierNote.textContent = selected.historicalSummary
    sheet.setAttribute('aria-label', `${selected.name} artifact records`)
    const records = selected.records.map((record) => {
      let node = recordElements.get(record.id)
      if (node === undefined) {
        node = createRecord(record)
        recordElements.set(record.id, node)
      }
      syncRecord(node, record)
      return recordItems.get(record.id)!
    })
    sheet.replaceChildren(...records)
    sheet.scrollTop = current.selectedScroll

    if (previous?.selectedCulture !== undefined
      && previous.selectedCulture !== current.selectedCulture) {
      void motion.dossier(current.selectedCulture, current.reducedMotion)
    }
    const previousPacket = previous === null ? null : packetRecord(previous)
    if (
      previousPacket?.restrictedPacket === true
      && previousPacket.status === 'locked'
      && packet?.status !== 'locked'
    ) void motion.packetRelease(current.reducedMotion)
  }

  listen(sheet, 'scroll', () => {
    if (!inputAllowed()) return
    const selected = selectedCulture()
    if (selected === undefined) return
    options.onScroll(
      selected.id,
      clampSheetScroll(sheet.scrollTop, sheet.scrollHeight, sheet.clientHeight),
    )
  })
  listen(cover, 'click', () => {
    if (!inputAllowed()) return
    coverState = coverState === 'closed' ? 'open' : 'closed'
    syncCover()
    void motion.cover(coverState, current.reducedMotion)
  })

  render(null)
  if (current.mode === 'archive') {
    coverState = 'open'
    syncCover()
    void motion.cover('open', current.reducedMotion)
  }

  return {
    element: root,
    update(next) {
      if (disposed) return
      const previous = current
      current = next
      render(previous)
    },
    resistPuzzle(puzzle) {
      if (disposed) return
      resist(recordElements.get(puzzle) ?? null, puzzle)
    },
    resistCulture(culture) {
      if (disposed) return
      resist(cultureElements.get(culture) ?? null, culture)
    },
    dispose() {
      if (disposed) return
      disposed = true
      if (activeDrag !== null) {
        const drag = activeDrag
        activeDrag = null
        if (drag.source.hasPointerCapture(drag.pointerId)) {
          drag.source.releasePointerCapture(drag.pointerId)
        }
        drag.source.classList.remove('is-inspection-source')
        options.onArtifactDragCancel(drag.puzzle, drag.lastSample)
      }
      recordGeneration += 1
      returningSource?.classList.remove('is-inspection-source')
      returningSource = null
      inspectionPositioner.classList.remove('is-artifact-lifted', 'is-returning')
      inspectionPositioner.style.removeProperty('--folio-drag-x')
      inspectionPositioner.style.removeProperty('--folio-drag-y')
      inspectionStage.setAttribute('aria-hidden', 'true')
      options.host.classList.remove('is-folio-drag-owner')
      clearPreviewBindings()
      clearRestriction()
      listeners.abort()
      motion.settleAll()
      root.remove()
    },
  }
}
