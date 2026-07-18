import type { CultureId, PuzzleId } from '../types'
import { clampSheetScroll } from './folio-layout'
import type { FolioProjection, FolioRecordProjection } from './folio-projection'
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

type RecordMount = 'photograph' | 'rubbing' | 'tracing'

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

const specimenByPuzzle: Readonly<Record<string, URL>> = {
  'two-veils': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyr-ossuary-seal.png', import.meta.url),
  'four-veils': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyr-cairn-seal-iv.png', import.meta.url),
  'forked-veil': new URL('../../../assets/interface/generated/excavation-folio/specimens/orra-gate-fragment.png', import.meta.url),
  'echoed-veil': new URL('../../../assets/interface/generated/excavation-folio/specimens/tel-vey-chamber-seal-viii.png', import.meta.url),
  'single-mark-return': new URL('../../../assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png', import.meta.url),
  'two-mark-projection': new URL('../../../assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png', import.meta.url),
  'blank-witness': new URL('../../../assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png', import.meta.url),
}

const mountSequence: readonly RecordMount[] = [
  'rubbing',
  'tracing',
  'photograph',
  'photograph',
  'photograph',
  'rubbing',
]

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

const culturePresentationName = (culture: CultureId): string => {
  const name = culture.split('-').find((part) => part.length > 0) ?? culture
  return `${name[0]!.toUpperCase()}${name.slice(1)}`
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
  const dossierTitle = element(document, 'p', 'dossier-title')
  const dossierNote = element(document, 'p', 'dossier-note')
  dossierHeader.append(dossierTitle, dossierNote)
  const sheet = element(document, 'div', 'record-grid')
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
  const cultureElements = new Map<CultureId, HTMLButtonElement>()
  let current = options.projection
  let coverState: 'open' | 'closed' = current.mode === 'puzzle' ? 'open' : 'closed'
  let activeDrag: ActiveDrag | null = null
  let returningSource: HTMLElement | null = null
  let recordGeneration = 0
  let restrictionTarget: HTMLElement | null = null
  let restrictionGeneration = 0
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

  const mountFor = (record: FolioRecordProjection, index: number): RecordMount =>
    record.restrictedPacket ? 'photograph' : mountSequence[index % mountSequence.length]!

  const appendRecordFace = (
    target: HTMLElement,
    record: FolioRecordProjection,
    mount: RecordMount,
  ): void => {
    const face = element(document, 'span', 'record-face')
    const evidence = element(document, 'span', 'evidence-mount curse-folio-record-mount')
    evidence.dataset.mount = mount
    evidence.setAttribute('aria-hidden', 'true')
    const specimen = specimenByPuzzle[record.id]
    if (specimen !== undefined) {
      const image = element(document, 'img', 'specimen-image curse-folio-specimen')
      image.src = specimen.href
      image.alt = ''
      image.setAttribute('aria-hidden', 'true')
      evidence.append(image)
    }
    const name = element(document, 'strong', 'curse-folio-record-name')
    name.textContent = record.name
    const accession = element(document, 'small', 'curse-folio-record-accession')
    accession.textContent = record.accession ?? 'Catalog entry pending accession'
    const summary = element(document, 'span', 'curse-folio-record-summary')
    summary.textContent = record.summary
    face.append(evidence, name, accession, summary)
    target.append(face)
  }

  const syncRecord = (
    node: HTMLElement,
    record: FolioRecordProjection,
    index: number,
  ): void => {
    const mount = mountFor(record, index)
    node.dataset.puzzle = record.id
    node.dataset.status = record.status
    node.dataset.affordance = record.affordance
    node.dataset.priority = String(record.priority && record.status !== 'completed')
    node.dataset.mount = mount
    node.classList.toggle('restricted-packet', record.restrictedPacket)
    if (record.restrictedPacket) {
      node.dataset.packetState = record.status === 'locked' ? 'sealed' : 'released'
    } else {
      delete node.dataset.packetState
    }
    node.setAttribute('role', 'listitem')
    if (record.status === 'locked') {
      node.setAttribute('aria-disabled', 'true')
      node.setAttribute('aria-label', `${record.name}. Restricted sleeve closed.`)
    } else {
      node.removeAttribute('aria-disabled')
      node.removeAttribute('aria-label')
    }
    node.replaceChildren()
    appendRecordFace(node, record, mount)
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
    inspectionPositioner.classList.remove('is-theorem-lifted', 'is-returning')
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
    inspectionPositioner.classList.remove('is-theorem-lifted')
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
      options.onTheoremDragCancel(drag.puzzle, drag.lastSample)
    } else {
      options.onTheoremDragEnd(drag.puzzle, drag.lastSample)
    }
    returnRecord(drag)
  }

  const cancelActiveDrag = (): void => {
    if (activeDrag === null) return
    const drag = activeDrag
    activeDrag = null
    options.onTheoremDragCancel(drag.puzzle, drag.lastSample)
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
    appendRecordFace(inspectionRecord, record, node.dataset.mount as RecordMount)
    inspectionRecord.dataset.liftedPuzzle = record.id
    inspectionRecord.dataset.status = record.status
    inspectionStage.setAttribute('aria-hidden', 'false')
    inspectionPositioner.classList.add('is-theorem-lifted')
    positionInspection(sample)
    stageReturnGeometry(drag)
    options.onTheoremDragStart(record.id, sample)
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
      if (projection?.affordance === 'drag-theorem') beginDrag(node, projection, event)
    }) as EventListener)
    listen(node, 'pointermove', ((event: PointerEvent) => {
      if (activeDrag?.pointerId !== event.pointerId || activeDrag.source !== node) return
      const sample = dragSample(event)
      activeDrag.lastSample = sample
      positionInspection(sample)
      stageReturnGeometry(activeDrag)
      options.onTheoremDragMove(record.id, sample)
    }) as EventListener)
    listen(node, 'pointerup', ((event: PointerEvent) => finishDrag(event, false)) as EventListener)
    listen(node, 'pointercancel', ((event: PointerEvent) => finishDrag(event, true)) as EventListener)
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
      if (label !== null) label.textContent = culturePresentationName(culture.id)
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
    dossierTitle.textContent = `Excavation archive · ${culturePresentationName(selected.id)} dossier`
    dossierNote.textContent = selected.historicalSummary
    sheet.setAttribute('aria-label', `${selected.name} artifact records`)
    const records = selected.records.map((record, index) => {
      let node = recordElements.get(record.id)
      if (node === undefined) {
        node = createRecord(record)
        recordElements.set(record.id, node)
      }
      syncRecord(node, record, index)
      return node
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
        options.onTheoremDragCancel(drag.puzzle, drag.lastSample)
      }
      recordGeneration += 1
      returningSource?.classList.remove('is-inspection-source')
      returningSource = null
      inspectionPositioner.classList.remove('is-theorem-lifted', 'is-returning')
      inspectionPositioner.style.removeProperty('--folio-drag-x')
      inspectionPositioner.style.removeProperty('--folio-drag-y')
      inspectionStage.setAttribute('aria-hidden', 'true')
      options.host.classList.remove('is-folio-drag-owner')
      clearRestriction()
      listeners.abort()
      motion.settleAll()
      root.remove()
    },
  }
}
