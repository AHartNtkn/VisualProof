import type { Diagram, WireId } from '../../kernel/diagram/diagram'
import type { ProofStep } from '../../kernel/proof/step'

export type TimelineView = {
  readonly states: readonly Diagram[]
  readonly steps: readonly ProofStep[]
  readonly cursor: number
  readonly boundary: readonly WireId[]
  moveTo(cursor: number): void
}

export type TickStatus = 'past' | 'current' | 'future'
export type CursorCommand = 'undo' | 'redo'

export function nearestTimelineCursor(clientX: number, left: number, width: number, stateCount: number): number {
  if (stateCount <= 1 || width <= 0) return 0
  const unit = Math.max(0, Math.min(1, (clientX - left) / width))
  return Math.round(unit * (stateCount - 1))
}

export function tickStatus(index: number, cursor: number): TickStatus {
  return index < cursor ? 'past' : index > cursor ? 'future' : 'current'
}

export function cursorCommand(cursor: number, stateCount: number, command: CursorCommand): number | null {
  const next = cursor + (command === 'undo' ? -1 : 1)
  return next < 0 || next >= stateCount ? null : next
}

export function proofStepLabel(step: ProofStep): string {
  return step.rule === 'theorem' ? `cite ${step.name}` : step.rule
}

export function timelineCopy(cursor: number, stateCount: number, labels: readonly string[]): string {
  const label = cursor === 0 ? 'start' : labels[cursor - 1] ?? 'step'
  return `${cursor} / ${Math.max(0, stateCount - 1)} · ${label}`
}

export type ScrubberActions = {
  readonly preview?: (cursor: number, anchor: { readonly x: number; readonly y: number }) => void
  readonly closePreview?: () => void
  readonly unavailable?: (command: CursorCommand) => void
}

export type MountedScrubber = {
  readonly element: HTMLElement
  refresh(): void
  dispose(): void
}

export function mountScrubber(
  host: HTMLElement,
  getView: () => TimelineView | null,
  actions: ScrubberActions = {},
): MountedScrubber {
  const element = document.createElement('section')
  element.className = 'vpa-temporal'
  element.setAttribute('aria-label', 'Proof history')
  const undo = document.createElement('button')
  undo.type = 'button'
  undo.className = 'vpa-temporal-undo'
  undo.title = 'Undo (Ctrl+Z)'
  undo.textContent = '↶'
  const rail = document.createElement('div')
  rail.className = 'vpa-temporal-rail'
  rail.setAttribute('role', 'slider')
  rail.tabIndex = 0
  const ticks = document.createElement('div')
  ticks.className = 'vpa-temporal-ticks'
  rail.append(ticks)
  const copy = document.createElement('output')
  copy.className = 'vpa-temporal-copy'
  const redo = document.createElement('button')
  redo.type = 'button'
  redo.className = 'vpa-temporal-redo'
  redo.title = 'Redo (Ctrl+Shift+Z)'
  redo.textContent = '↷'
  element.append(undo, rail, copy, redo)
  host.replaceChildren(element)

  let dragging = false
  let disposed = false
  const disposers: Array<() => void> = []
  const listen = (target: EventTarget, type: string, listener: EventListener): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const moveFromPointer = (event: PointerEvent): void => {
    const view = getView()
    if (view === null) return
    const rect = rail.getBoundingClientRect()
    view.moveTo(nearestTimelineCursor(event.clientX, rect.left, rect.width, view.states.length))
  }
  const command = (kind: CursorCommand): void => {
    const view = getView()
    if (view === null) return
    const next = cursorCommand(view.cursor, view.states.length, kind)
    if (next === null) actions.unavailable?.(kind)
    else view.moveTo(next)
  }

  listen(undo, 'click', () => command('undo'))
  listen(redo, 'click', () => command('redo'))
  listen(rail, 'pointerdown', ((event: PointerEvent) => {
    dragging = true
    actions.closePreview?.()
    rail.setPointerCapture?.(event.pointerId)
    moveFromPointer(event)
  }) as EventListener)
  listen(rail, 'pointermove', ((event: PointerEvent) => {
    if (dragging) {
      moveFromPointer(event)
      return
    }
    const view = getView()
    if (view === null) return
    const rect = rail.getBoundingClientRect()
    actions.preview?.(
      nearestTimelineCursor(event.clientX, rect.left, rect.width, view.states.length),
      { x: event.clientX, y: rect.top },
    )
  }) as EventListener)
  const endDrag = ((event: PointerEvent) => {
    if (!dragging) return
    dragging = false
    rail.releasePointerCapture?.(event.pointerId)
    actions.closePreview?.()
  }) as EventListener
  listen(rail, 'pointerup', endDrag)
  listen(rail, 'pointercancel', endDrag)
  listen(rail, 'pointerleave', () => { if (!dragging) actions.closePreview?.() })

  const refresh = (): void => {
    if (disposed) return
    const view = getView()
    element.hidden = view === null
    if (view === null) return
    const labels = view.steps.map(proofStepLabel)
    copy.value = timelineCopy(view.cursor, view.states.length, labels)
    undo.disabled = view.cursor === 0
    redo.disabled = view.cursor === view.states.length - 1
    rail.setAttribute('aria-valuemin', '0')
    rail.setAttribute('aria-valuemax', String(view.states.length - 1))
    rail.setAttribute('aria-valuenow', String(view.cursor))
    ticks.replaceChildren(...view.states.map((_, index) => {
      const tick = document.createElement('i')
      tick.className = `vpa-temporal-tick is-${tickStatus(index, view.cursor)}`
      tick.style.left = view.states.length === 1 ? '50%' : `${index / (view.states.length - 1) * 100}%`
      tick.dataset.cursor = String(index)
      return tick
    }))
  }

  refresh()
  return {
    element,
    refresh,
    dispose: () => {
      if (disposed) return
      disposed = true
      actions.closePreview?.()
      for (const dispose of disposers.splice(0)) dispose()
      element.remove()
    },
  }
}
