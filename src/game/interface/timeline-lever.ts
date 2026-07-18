import type { GameTimeline } from '../session'

export const TIMELINE_TRACK_START = 0.085
export const TIMELINE_TRACK_SPAN = 0.83

export const leverHandleFraction = (cursor: number, stateCount: number): number =>
  stateCount <= 1 ? 0 : Math.max(0, Math.min(stateCount - 1, cursor)) / (stateCount - 1)

export const leverCursorAt = (
  clientX: number,
  left: number,
  width: number,
  stateCount: number,
): number => {
  if (stateCount <= 1 || !Number.isFinite(width) || width <= 0) return 0
  const fraction = Math.max(0, Math.min(1, (clientX - left) / width))
  return Math.max(0, Math.min(stateCount - 1, Math.round(fraction * (stateCount - 1))))
}

export type MountedTimelineLever = {
  readonly element: HTMLElement
  update(projection: TimelineLeverProjection): void
  dispose(): void
}

export type TimelineLeverProjection =
  | { readonly kind: 'active'; readonly timeline: GameTimeline }
  | {
      readonly kind: 'inactive'
      readonly position: 'home' | 'complete'
      readonly moves: number
    }

/** Mount interaction only; the lens environment owns both approved PNG layers. */
export function mountTimelineLever(
  handleSlot: HTMLElement,
  initialProjection: TimelineLeverProjection,
  onMove: (cursor: number) => void,
  inputAllowed: () => boolean = () => true,
): MountedTimelineLever {
  const document = handleSlot.ownerDocument
  const rail = document.createElement('div')
  rail.className = 'curse-production-timeline-control'
  rail.setAttribute('role', 'slider')
  rail.setAttribute('aria-label', 'Recorded seal states')
  rail.tabIndex = 0
  handleSlot.append(rail)

  let projection = initialProjection
  let draggingPointer: number | null = null
  let lastRequestedCursor: number | null = null
  const inputTimeline = (): GameTimeline | null =>
    projection.kind === 'active' && inputAllowed() ? projection.timeline : null
  const cancelDrag = (pointerId: number): void => {
    if (draggingPointer !== pointerId) return
    draggingPointer = null
    lastRequestedCursor = null
    if (rail.hasPointerCapture(pointerId)) rail.releasePointerCapture(pointerId)
  }
  const requestAt = (event: PointerEvent): void => {
    const timeline = inputTimeline()
    if (timeline === null) {
      cancelDrag(event.pointerId)
      return
    }
    const rect = rail.getBoundingClientRect()
    const cursor = leverCursorAt(
      event.clientX,
      rect.left + rect.width * TIMELINE_TRACK_START,
      rect.width * TIMELINE_TRACK_SPAN,
      timeline.states.length,
    )
    if (cursor === lastRequestedCursor) return
    lastRequestedCursor = cursor
    onMove(cursor)
  }
  const down = (event: PointerEvent): void => {
    if (event.button !== 0 || draggingPointer !== null || inputTimeline() === null) return
    draggingPointer = event.pointerId
    lastRequestedCursor = null
    rail.setPointerCapture(event.pointerId)
    requestAt(event)
  }
  const moving = (event: PointerEvent): void => {
    if (draggingPointer === event.pointerId) requestAt(event)
  }
  const up = (event: PointerEvent): void => {
    if (draggingPointer !== event.pointerId) return
    requestAt(event)
    cancelDrag(event.pointerId)
  }
  const cancelled = (event: PointerEvent): void => cancelDrag(event.pointerId)
  const lost = (event: PointerEvent): void => {
    if (draggingPointer === event.pointerId) {
      draggingPointer = null
      lastRequestedCursor = null
    }
  }
  const keydown = (event: KeyboardEvent): void => {
    const timeline = inputTimeline()
    if (timeline === null) return
    const last = Math.max(0, timeline.states.length - 1)
    let cursor: number
    switch (event.key) {
      case 'ArrowLeft':
      case 'ArrowDown': cursor = Math.max(0, timeline.cursor - 1); break
      case 'ArrowRight':
      case 'ArrowUp': cursor = Math.min(last, timeline.cursor + 1); break
      case 'Home': cursor = 0; break
      case 'End': cursor = last; break
      default: return
    }
    event.preventDefault()
    onMove(cursor)
  }

  rail.addEventListener('pointerdown', down)
  rail.addEventListener('pointermove', moving)
  rail.addEventListener('pointerup', up)
  rail.addEventListener('pointercancel', cancelled)
  rail.addEventListener('lostpointercapture', lost)
  rail.addEventListener('keydown', keydown)

  const setPosition = (position: number): void => {
    handleSlot.style.setProperty('--curse-timeline-position', String(position))
    handleSlot.style.setProperty(
      '--curse-timeline-handle-shift',
      `${(TIMELINE_TRACK_START + position * TIMELINE_TRACK_SPAN - 0.5) * 100}%`,
    )
  }
  const update = (next: TimelineLeverProjection): void => {
    projection = next
    if (projection.kind === 'inactive') {
      if (draggingPointer !== null) cancelDrag(draggingPointer)
      const complete = projection.position === 'complete'
      const cursor = complete ? projection.moves : 0
      setPosition(complete ? 1 : 0)
      rail.setAttribute('aria-disabled', 'true')
      rail.tabIndex = -1
      rail.setAttribute('aria-valuemin', '0')
      rail.setAttribute('aria-valuemax', String(cursor))
      rail.setAttribute('aria-valuenow', String(cursor))
      rail.setAttribute(
        'aria-valuetext',
        complete ? `Completed state ${cursor}` : 'Timeline inactive',
      )
      return
    }
    const timeline = projection.timeline
    const last = Math.max(0, timeline.states.length - 1)
    const cursor = Math.max(0, Math.min(last, timeline.cursor))
    setPosition(leverHandleFraction(cursor, timeline.states.length))
    rail.setAttribute('aria-disabled', 'false')
    rail.tabIndex = 0
    rail.setAttribute('aria-valuemin', '0')
    rail.setAttribute('aria-valuemax', String(last))
    rail.setAttribute('aria-valuenow', String(cursor))
    rail.setAttribute('aria-valuetext', cursor === 0 ? 'Original seal' : `Recorded state ${cursor}`)
  }

  update(initialProjection)
  let disposed = false
  return {
    element: rail,
    update,
    dispose: () => {
      if (disposed) return
      disposed = true
      if (draggingPointer !== null) cancelDrag(draggingPointer)
      rail.removeEventListener('pointerdown', down)
      rail.removeEventListener('pointermove', moving)
      rail.removeEventListener('pointerup', up)
      rail.removeEventListener('pointercancel', cancelled)
      rail.removeEventListener('lostpointercapture', lost)
      rail.removeEventListener('keydown', keydown)
      rail.remove()
    },
  }
}
