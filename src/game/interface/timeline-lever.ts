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
): MountedTimelineLever {
  const element = document.createElement('div')
  element.className = 'curse-timeline'
  element.setAttribute('aria-label', 'Recorded seal states')

  const housing = document.createElement('img')
  housing.className = 'curse-timeline-housing curse-decoration'
  housing.src = new URL('../../../assets/interface/generated/central-lens/lever-housing.png', import.meta.url).href
  housing.alt = ''

  const rail = document.createElement('div')
  rail.className = 'curse-timeline-rail'
  rail.setAttribute('role', 'slider')
  rail.tabIndex = 0

  const handle = document.createElement('img')
  handle.className = 'curse-timeline-handle curse-decoration'
  handle.src = new URL('../../../assets/interface/generated/central-lens/lever-handle.png', import.meta.url).href
  handle.alt = ''

  rail.append(handle)
  element.append(housing, rail)
  host.append(element)

  let dragging = false
  const move = (event: PointerEvent): void => {
    const timeline = getTimeline()
    const rect = rail.getBoundingClientRect()
    onMove(leverCursorAt(event.clientX, rect.left, rect.width, timeline.states.length))
  }
  const down = (event: PointerEvent): void => {
    if (event.button !== 0) return
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

  rail.addEventListener('pointerdown', down)
  rail.addEventListener('pointermove', moving)
  rail.addEventListener('pointerup', up)
  rail.addEventListener('pointercancel', up)

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
      element.remove()
    },
  }
}
