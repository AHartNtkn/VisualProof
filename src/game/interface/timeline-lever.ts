import { nearestTimelineCursor } from '../../app/interact/scrubber'
import type { GameTimeline } from '../session'

export const leverHandleFraction = (cursor: number, stateCount: number): number =>
  stateCount <= 1 ? 0.5 : cursor / (stateCount - 1)

export const leverCursorAt = (
  clientX: number,
  left: number,
  width: number,
  stateCount: number,
): number => nearestTimelineCursor(clientX, left, width, stateCount)

export type MountedTimelineLever = {
  readonly element: HTMLElement
  refresh(): void
  dispose(): void
}

export function mountTimelineLever(
  host: HTMLElement,
  getTimeline: () => GameTimeline,
  onMove: (cursor: number) => void,
  inputAllowed: () => boolean = () => true,
): MountedTimelineLever {
  const element = document.createElement('div')
  element.className = 'curse-timeline'

  const housing = document.createElement('img')
  housing.className = 'curse-timeline-housing curse-decoration'
  housing.src = new URL('../../../assets/interface/generated/central-lens/lever-housing.png', import.meta.url).href
  housing.alt = ''
  housing.setAttribute('aria-hidden', 'true')

  const rail = document.createElement('div')
  rail.className = 'curse-timeline-rail'
  rail.setAttribute('role', 'slider')
  rail.setAttribute('aria-label', 'Recorded seal states')
  rail.tabIndex = 0

  const handle = document.createElement('img')
  handle.className = 'curse-timeline-handle curse-decoration'
  handle.src = new URL('../../../assets/interface/generated/central-lens/lever-handle.png', import.meta.url).href
  handle.alt = ''
  handle.setAttribute('aria-hidden', 'true')

  rail.append(handle)
  element.append(housing, rail)
  host.append(element)

  let dragging = false
  const move = (event: PointerEvent): void => {
    if (!inputAllowed()) return
    const timeline = getTimeline()
    const rect = rail.getBoundingClientRect()
    onMove(leverCursorAt(event.clientX, rect.left, rect.width, timeline.states.length))
  }
  const down = (event: PointerEvent): void => {
    if (event.button !== 0 || !inputAllowed()) return
    dragging = true
    rail.setPointerCapture(event.pointerId)
    move(event)
  }
  const moving = (event: PointerEvent): void => {
    if (dragging) move(event)
  }
  const up = (event: PointerEvent): void => {
    if (!dragging) return
    dragging = false
    if (rail.hasPointerCapture(event.pointerId)) rail.releasePointerCapture(event.pointerId)
  }
  const keydown = (event: KeyboardEvent): void => {
    if (!inputAllowed()) return
    const timeline = getTimeline()
    const last = Math.max(0, timeline.states.length - 1)
    let cursor: number
    switch (event.key) {
      case 'ArrowLeft':
      case 'ArrowDown':
        cursor = Math.max(0, timeline.cursor - 1)
        break
      case 'ArrowRight':
      case 'ArrowUp':
        cursor = Math.min(last, timeline.cursor + 1)
        break
      case 'Home':
        cursor = 0
        break
      case 'End':
        cursor = last
        break
      default:
        return
    }
    event.preventDefault()
    onMove(cursor)
  }

  rail.addEventListener('pointerdown', down)
  rail.addEventListener('pointermove', moving)
  rail.addEventListener('pointerup', up)
  rail.addEventListener('pointercancel', up)
  rail.addEventListener('keydown', keydown)

  const refresh = (): void => {
    const timeline = getTimeline()
    const fraction = leverHandleFraction(timeline.cursor, timeline.states.length)
    handle.style.setProperty('--curse-lever-position', String(fraction))
    rail.setAttribute('aria-valuemin', '0')
    rail.setAttribute('aria-valuemax', String(timeline.states.length - 1))
    rail.setAttribute('aria-valuenow', String(timeline.cursor))
  }

  refresh()
  return {
    element,
    refresh,
    dispose: () => {
      rail.removeEventListener('pointerdown', down)
      rail.removeEventListener('pointermove', moving)
      rail.removeEventListener('pointerup', up)
      rail.removeEventListener('pointercancel', up)
      rail.removeEventListener('keydown', keydown)
      element.remove()
    },
  }
}
