import type { GameTimeline } from '../session'

export const leverHandleFraction = (cursor: number, stateCount: number): number =>
  stateCount <= 1 ? 0.5 : Math.max(0, Math.min(stateCount - 1, cursor)) / (stateCount - 1)

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
  refresh(): void
  dispose(): void
}

/** Mount interaction only; the lens environment owns both approved PNG layers. */
export function mountTimelineLever(
  handleSlot: HTMLElement,
  getTimeline: () => GameTimeline,
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

  let draggingPointer: number | null = null
  const cancelDrag = (pointerId: number): void => {
    if (draggingPointer !== pointerId) return
    draggingPointer = null
    if (rail.hasPointerCapture(pointerId)) rail.releasePointerCapture(pointerId)
  }
  const requestAt = (event: PointerEvent): void => {
    if (!inputAllowed()) {
      cancelDrag(event.pointerId)
      return
    }
    const timeline = getTimeline()
    const rect = rail.getBoundingClientRect()
    onMove(leverCursorAt(event.clientX, rect.left, rect.width, timeline.states.length))
  }
  const down = (event: PointerEvent): void => {
    if (event.button !== 0 || !inputAllowed()) return
    draggingPointer = event.pointerId
    rail.setPointerCapture(event.pointerId)
    requestAt(event)
  }
  const moving = (event: PointerEvent): void => {
    if (draggingPointer === event.pointerId) requestAt(event)
  }
  const up = (event: PointerEvent): void => cancelDrag(event.pointerId)
  const lost = (event: PointerEvent): void => {
    if (draggingPointer === event.pointerId) draggingPointer = null
  }
  const keydown = (event: KeyboardEvent): void => {
    if (!inputAllowed()) return
    const timeline = getTimeline()
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
  rail.addEventListener('pointercancel', up)
  rail.addEventListener('lostpointercapture', lost)
  rail.addEventListener('keydown', keydown)

  const refresh = (): void => {
    const timeline = getTimeline()
    const last = Math.max(0, timeline.states.length - 1)
    const cursor = Math.max(0, Math.min(last, timeline.cursor))
    handleSlot.style.setProperty('--curse-timeline-position', String(leverHandleFraction(cursor, timeline.states.length)))
    rail.setAttribute('aria-valuemin', '0')
    rail.setAttribute('aria-valuemax', String(last))
    rail.setAttribute('aria-valuenow', String(cursor))
    rail.setAttribute('aria-valuetext', cursor === 0 ? 'Original seal' : `Recorded state ${cursor}`)
  }

  refresh()
  let disposed = false
  return {
    element: rail,
    refresh,
    dispose: () => {
      if (disposed) return
      disposed = true
      if (draggingPointer !== null) cancelDrag(draggingPointer)
      rail.removeEventListener('pointerdown', down)
      rail.removeEventListener('pointermove', moving)
      rail.removeEventListener('pointerup', up)
      rail.removeEventListener('pointercancel', up)
      rail.removeEventListener('lostpointercapture', lost)
      rail.removeEventListener('keydown', keydown)
      rail.remove()
    },
  }
}
