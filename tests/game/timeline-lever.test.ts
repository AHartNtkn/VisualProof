import { afterEach, beforeEach, describe, expect, it } from 'vitest'
import type { GameTimeline } from '../../src/game/session'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { leverCursorAt, leverHandleFraction, mountTimelineLever } from '../../src/game/interface/timeline-lever'

class FakeStyle {
  private readonly properties = new Map<string, string>()
  setProperty(name: string, value: string): void { this.properties.set(name, value) }
  getPropertyValue(name: string): string { return this.properties.get(name) ?? '' }
}

class FakeElement extends EventTarget {
  readonly children: FakeElement[] = []
  readonly style = new FakeStyle()
  readonly ownerDocument: FakeDocument
  className = ''
  tabIndex = -1
  parent: FakeElement | null = null
  rect = { left: 0, width: 0 }
  released: number[] = []
  private readonly attributes = new Map<string, string>()
  private readonly capturedPointers = new Set<number>()

  constructor(ownerDocument: FakeDocument) { super(); this.ownerDocument = ownerDocument }
  append(...children: FakeElement[]): void { for (const child of children) { child.parent = this; this.children.push(child) } }
  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
  getAttribute(name: string): string | null { return this.attributes.get(name) ?? null }
  getBoundingClientRect(): DOMRect { return { left: this.rect.left, width: this.rect.width } as DOMRect }
  setPointerCapture(pointerId: number): void { this.capturedPointers.add(pointerId) }
  hasPointerCapture(pointerId: number): boolean { return this.capturedPointers.has(pointerId) }
  releasePointerCapture(pointerId: number): void { this.capturedPointers.delete(pointerId); this.released.push(pointerId) }
  remove(): void {
    if (this.parent === null) return
    const index = this.parent.children.indexOf(this)
    if (index >= 0) this.parent.children.splice(index, 1)
    this.parent = null
  }
}

class FakeDocument { createElement(): FakeElement { return new FakeElement(this) } }

const diagram: Diagram = { root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes: {}, wires: {} }
const timeline = (cursor: number, stateCount = 5): GameTimeline => ({
  states: Array.from({ length: stateCount }, () => diagram), steps: [], cursor,
})
const eventWith = <T extends Record<string, unknown>>(type: string, values: T): Event & T => {
  const event = new Event(type, { cancelable: true })
  for (const [name, value] of Object.entries(values)) Object.defineProperty(event, name, { value })
  return event as Event & T
}

let document: FakeDocument
beforeEach(() => { document = new FakeDocument() })
afterEach(() => {})

describe('production timeline control', () => {
  it('rounds and clamps exact cursor positions over the retained track', () => {
    expect(leverHandleFraction(0, 5)).toBe(0)
    expect(leverHandleFraction(2, 5)).toBe(0.5)
    expect(leverHandleFraction(4, 5)).toBe(1)
    expect(leverHandleFraction(0, 1)).toBe(0.5)
    expect(leverCursorAt(99, 100, 300, 4)).toBe(0)
    expect(leverCursorAt(250, 100, 300, 4)).toBe(2)
    expect(leverCursorAt(999, 100, 300, 4)).toBe(3)
    expect(leverCursorAt(100, 100, 0, 4)).toBe(0)
  })

  it('mounts only a focusable slider interaction into the existing handle slot', () => {
    const slot = new FakeElement(document)
    const approvedHandle = new FakeElement(document)
    approvedHandle.className = 'curse-production-timeline-handle curse-decoration'
    slot.append(approvedHandle)
    const mounted = mountTimelineLever(slot as unknown as HTMLElement, () => timeline(2), () => {})
    const control = mounted.element as unknown as FakeElement

    expect(slot.children).toEqual([approvedHandle, control])
    expect(control.className).toBe('curse-production-timeline-control')
    expect(control.getAttribute('role')).toBe('slider')
    expect(control.getAttribute('aria-label')).toBe('Recorded seal states')
    expect(control.tabIndex).toBe(0)
    expect(control.children).toEqual([])
  })

  it('refreshes ARIA and the environment-owned handle position, including cursor-zero restart', () => {
    const slot = new FakeElement(document)
    let current = timeline(0)
    const mounted = mountTimelineLever(slot as unknown as HTMLElement, () => current, () => {})
    const control = mounted.element as unknown as FakeElement
    expect(control.getAttribute('aria-valuenow')).toBe('0')
    expect(control.getAttribute('aria-valuetext')).toBe('Original seal')
    expect(slot.style.getPropertyValue('--curse-timeline-position')).toBe('0')
    expect(slot.style.getPropertyValue('--curse-timeline-handle-shift')).toBe('-41.5%')

    current = timeline(3)
    mounted.refresh()
    expect(control.getAttribute('aria-valuemax')).toBe('4')
    expect(control.getAttribute('aria-valuenow')).toBe('3')
    expect(control.getAttribute('aria-valuetext')).toBe('Recorded state 3')
    expect(slot.style.getPropertyValue('--curse-timeline-position')).toBe('0.75')
    expect(Number.parseFloat(slot.style.getPropertyValue('--curse-timeline-handle-shift')))
      .toBeCloseTo(20.75)
  })

  it('routes standard slider keys as clamped cursor requests', () => {
    const slot = new FakeElement(document)
    let current = timeline(2)
    const moves: number[] = []
    const control = mountTimelineLever(slot as unknown as HTMLElement, () => current, (cursor) => moves.push(cursor)).element as unknown as FakeElement
    for (const [key, expected] of [
      ['ArrowLeft', 1], ['ArrowDown', 1], ['ArrowRight', 3], ['ArrowUp', 3], ['Home', 0], ['End', 4],
    ] as const) {
      const event = eventWith('keydown', { key })
      control.dispatchEvent(event)
      expect(moves.at(-1)).toBe(expected)
      expect(event.defaultPrevented).toBe(true)
    }
    current = timeline(0)
    control.dispatchEvent(eventWith('keydown', { key: 'ArrowLeft' }))
    current = timeline(4)
    control.dispatchEvent(eventWith('keydown', { key: 'ArrowRight' }))
    expect(moves.slice(-2)).toEqual([0, 4])
  })

  it('gates keyboard and pointer input while another transient or motion owns input', () => {
    const slot = new FakeElement(document)
    let allowed = false
    const moves: number[] = []
    const control = mountTimelineLever(
      slot as unknown as HTMLElement, () => timeline(1, 4), (cursor) => moves.push(cursor), () => allowed,
    ).element as unknown as FakeElement
    control.rect = { left: 100, width: 300 }
    const blockedKey = eventWith('keydown', { key: 'ArrowRight' })
    control.dispatchEvent(blockedKey)
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 7 }))
    expect(moves).toEqual([])
    expect(blockedKey.defaultPrevented).toBe(false)
    allowed = true
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 8 }))
    expect(moves).toEqual([2])
  })

  it('cancels pointer capture if input becomes unavailable during a drag', () => {
    const slot = new FakeElement(document)
    let allowed = true
    const moves: number[] = []
    const control = mountTimelineLever(
      slot as unknown as HTMLElement, () => timeline(1, 4), (cursor) => moves.push(cursor), () => allowed,
    ).element as unknown as FakeElement
    control.rect = { left: 100, width: 300 }
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 8 }))
    allowed = false
    control.dispatchEvent(eventWith('pointermove', { clientX: 400, pointerId: 8 }))
    expect(moves).toEqual([2])
    expect(control.released).toEqual([8])
    allowed = true
    control.dispatchEvent(eventWith('pointermove', { clientX: 100, pointerId: 8 }))
    expect(moves).toEqual([2])
  })

  it('rejects a second concurrent pointer and samples the final allowed pointerup coordinate', () => {
    const slot = new FakeElement(document)
    const moves: number[] = []
    const control = mountTimelineLever(
      slot as unknown as HTMLElement, () => timeline(1, 8), (cursor) => moves.push(cursor),
    ).element as unknown as FakeElement
    control.rect = { left: 100, width: 700 }
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 243, pointerId: 1 }))
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 800, pointerId: 2 }))
    control.dispatchEvent(eventWith('pointerup', { clientX: 657.5, pointerId: 1 }))
    expect(moves).toEqual([1, 6])
    expect(control.released).toEqual([1])
  })

  it('emits a stationary pointer gesture exactly once', () => {
    const slot = new FakeElement(document)
    const moves: number[] = []
    const control = mountTimelineLever(
      slot as unknown as HTMLElement, () => timeline(1, 8), (cursor) => moves.push(cursor),
    ).element as unknown as FakeElement
    control.rect = { left: 100, width: 700 }
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 326.5, pointerId: 11 }))
    control.dispatchEvent(eventWith('pointerup', { clientX: 326.5, pointerId: 11 }))
    expect(moves).toEqual([2])
    expect(control.released).toEqual([11])
  })

  it('handles pointer cancellation/lost capture and removes all ownership on disposal', () => {
    const slot = new FakeElement(document)
    const moves: number[] = []
    const mounted = mountTimelineLever(slot as unknown as HTMLElement, () => timeline(1, 4), (cursor) => moves.push(cursor))
    const control = mounted.element as unknown as FakeElement
    control.rect = { left: 100, width: 300 }
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 9 }))
    control.dispatchEvent(eventWith('lostpointercapture', { pointerId: 9 }))
    control.dispatchEvent(eventWith('pointermove', { clientX: 400, pointerId: 9 }))
    expect(moves).toEqual([2])
    control.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 10 }))
    control.dispatchEvent(eventWith('pointercancel', { pointerId: 10 }))
    expect(control.released).toContain(10)
    mounted.dispose()
    expect(slot.children).toEqual([])
    control.dispatchEvent(eventWith('keydown', { key: 'End' }))
    expect(moves).toEqual([2, 2])
  })
})
