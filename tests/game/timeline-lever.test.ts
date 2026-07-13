import { afterEach, beforeEach, describe, expect, it } from 'vitest'
import type { GameTimeline } from '../../src/game/session'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { leverCursorAt, leverHandleFraction, mountTimelineLever } from '../../src/game/interface/timeline-lever'

class FakeStyle {
  private readonly properties = new Map<string, string>()

  setProperty(name: string, value: string): void {
    this.properties.set(name, value)
  }

  getPropertyValue(name: string): string {
    return this.properties.get(name) ?? ''
  }
}

class FakeElement extends EventTarget {
  readonly children: FakeElement[] = []
  readonly style = new FakeStyle()
  className = ''
  src = ''
  alt = ''
  tabIndex = -1
  parent: FakeElement | null = null
  rect = { left: 0, width: 0 }
  private readonly attributes = new Map<string, string>()
  private readonly capturedPointers = new Set<number>()

  append(...children: FakeElement[]): void {
    for (const child of children) {
      child.parent = this
      this.children.push(child)
    }
  }

  setAttribute(name: string, value: string): void {
    this.attributes.set(name, value)
  }

  getAttribute(name: string): string | null {
    return this.attributes.get(name) ?? null
  }

  getBoundingClientRect(): DOMRect {
    return { left: this.rect.left, width: this.rect.width } as DOMRect
  }

  setPointerCapture(pointerId: number): void {
    this.capturedPointers.add(pointerId)
  }

  hasPointerCapture(pointerId: number): boolean {
    return this.capturedPointers.has(pointerId)
  }

  releasePointerCapture(pointerId: number): void {
    this.capturedPointers.delete(pointerId)
  }

  remove(): void {
    if (this.parent === null) return
    const index = this.parent.children.indexOf(this)
    if (index >= 0) this.parent.children.splice(index, 1)
    this.parent = null
  }
}

class FakeDocument {
  createElement(): FakeElement {
    return new FakeElement()
  }
}

const diagram: Diagram = { root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes: {}, wires: {} }

const timeline = (cursor: number, stateCount = 5): GameTimeline => ({
  states: Array.from({ length: stateCount }, () => diagram),
  steps: [],
  cursor,
})

const eventWith = <T extends Record<string, unknown>>(type: string, values: T): Event & T => {
  const event = new Event(type, { cancelable: true })
  for (const [name, value] of Object.entries(values)) Object.defineProperty(event, name, { value })
  return event as Event & T
}

let previousDocument: typeof globalThis.document | undefined

beforeEach(() => {
  previousDocument = globalThis.document
  Object.defineProperty(globalThis, 'document', { configurable: true, value: new FakeDocument() })
})

afterEach(() => {
  Object.defineProperty(globalThis, 'document', { configurable: true, value: previousDocument })
})

describe('timeline lever presentation', () => {
  it('maps retained states to the full physical track', () => {
    expect(leverHandleFraction(0, 5)).toBe(0)
    expect(leverHandleFraction(2, 5)).toBe(0.5)
    expect(leverHandleFraction(4, 5)).toBe(1)
    expect(leverHandleFraction(0, 1)).toBe(0.5)
  })

  it('delegates pointer mapping to the established temporal rail rule', () => {
    expect(leverCursorAt(250, 100, 300, 4)).toBe(2)
  })

  it('names the actual focusable slider rail', () => {
    const host = new FakeElement()
    const mounted = mountTimelineLever(host as unknown as HTMLElement, () => timeline(2), () => {})
    const root = mounted.element as unknown as FakeElement
    const housing = root.children[0]
    const rail = root.children[1]
    const handle = rail?.children[0]

    expect(rail?.getAttribute('role')).toBe('slider')
    expect(rail?.getAttribute('aria-label')).toBe('Recorded seal states')
    expect(rail?.tabIndex).toBe(0)
    expect(root.getAttribute('aria-label')).toBeNull()
    expect(housing?.className).toBe('curse-timeline-housing curse-decoration')
    expect(housing?.src).toMatch(/assets\/interface\/generated\/central-lens\/lever-housing\.png$/)
    expect(housing?.alt).toBe('')
    expect(housing?.getAttribute('aria-hidden')).toBe('true')
    expect(handle?.className).toBe('curse-timeline-handle curse-decoration')
    expect(handle?.src).toMatch(/assets\/interface\/generated\/central-lens\/lever-handle\.png$/)
    expect(handle?.alt).toBe('')
    expect(handle?.getAttribute('aria-hidden')).toBe('true')
  })

  it('delegates standard slider keys as clamped cursor requests', () => {
    const host = new FakeElement()
    let current = timeline(2)
    const moves: number[] = []
    const mounted = mountTimelineLever(
      host as unknown as HTMLElement,
      () => current,
      (cursor) => moves.push(cursor),
    )
    const rail = (mounted.element as unknown as FakeElement).children[1]
    if (rail === undefined) throw new Error('timeline rail missing')

    for (const [key, expected] of [
      ['ArrowLeft', 1], ['ArrowDown', 1], ['ArrowRight', 3], ['ArrowUp', 3], ['Home', 0], ['End', 4],
    ] as const) {
      const event = eventWith('keydown', { key })
      rail.dispatchEvent(event)
      expect(moves.at(-1)).toBe(expected)
      expect(event.defaultPrevented).toBe(true)
    }

    current = timeline(0)
    rail.dispatchEvent(eventWith('keydown', { key: 'ArrowLeft' }))
    rail.dispatchEvent(eventWith('keydown', { key: 'ArrowDown' }))
    current = timeline(4)
    rail.dispatchEvent(eventWith('keydown', { key: 'ArrowRight' }))
    rail.dispatchEvent(eventWith('keydown', { key: 'ArrowUp' }))
    expect(moves.slice(-4)).toEqual([0, 0, 4, 4])

    const unrelated = eventWith('keydown', { key: 'Enter' })
    rail.dispatchEvent(unrelated)
    expect(unrelated.defaultPrevented).toBe(false)
    expect(moves).toHaveLength(10)
  })

  it('refreshes slider state and handle position from the supplied timeline', () => {
    const host = new FakeElement()
    let current = timeline(0)
    const mounted = mountTimelineLever(host as unknown as HTMLElement, () => current, () => {})
    const rail = (mounted.element as unknown as FakeElement).children[1]
    const handle = rail?.children[0]
    if (rail === undefined || handle === undefined) throw new Error('timeline lever structure missing')

    expect(rail.getAttribute('aria-valuemin')).toBe('0')
    expect(rail.getAttribute('aria-valuemax')).toBe('4')
    expect(rail.getAttribute('aria-valuenow')).toBe('0')
    expect(handle.style.getPropertyValue('--curse-lever-position')).toBe('0')

    current = timeline(3)
    mounted.refresh()
    expect(rail.getAttribute('aria-valuemax')).toBe('4')
    expect(rail.getAttribute('aria-valuenow')).toBe('3')
    expect(handle.style.getPropertyValue('--curse-lever-position')).toBe('0.75')
  })

  it('routes pointer dragging and removes all owned behavior on disposal', () => {
    const host = new FakeElement()
    const moves: number[] = []
    const mounted = mountTimelineLever(
      host as unknown as HTMLElement,
      () => timeline(1, 4),
      (cursor) => moves.push(cursor),
    )
    const rail = (mounted.element as unknown as FakeElement).children[1]
    if (rail === undefined) throw new Error('timeline rail missing')
    rail.rect = { left: 100, width: 300 }

    rail.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 7 }))
    rail.dispatchEvent(eventWith('pointermove', { clientX: 400, pointerId: 7 }))
    rail.dispatchEvent(eventWith('pointerup', { clientX: 400, pointerId: 7 }))
    expect(moves).toEqual([2, 3])

    mounted.dispose()
    expect(host.children).toHaveLength(0)
    rail.dispatchEvent(eventWith('keydown', { key: 'End' }))
    rail.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 100, pointerId: 8 }))
    expect(moves).toEqual([2, 3])
  })

  it('does not begin or continue pointer cursor requests while input is disallowed', () => {
    const host = new FakeElement()
    let allowed = false
    const moves: number[] = []
    const mounted = mountTimelineLever(
      host as unknown as HTMLElement,
      () => timeline(1, 4),
      (cursor) => moves.push(cursor),
      () => allowed,
    )
    const rail = (mounted.element as unknown as FakeElement).children[1]
    if (rail === undefined) throw new Error('timeline rail missing')
    rail.rect = { left: 100, width: 300 }

    rail.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 7 }))
    rail.dispatchEvent(eventWith('pointermove', { clientX: 400, pointerId: 7 }))
    expect(moves).toEqual([])

    allowed = true
    rail.dispatchEvent(eventWith('pointerdown', { button: 0, clientX: 250, pointerId: 8 }))
    expect(moves).toEqual([2])
    allowed = false
    rail.dispatchEvent(eventWith('pointermove', { clientX: 400, pointerId: 8 }))
    expect(moves).toEqual([2])
  })

  it('does not request keyboard cursor movement while input is disallowed and resumes when allowed', () => {
    const host = new FakeElement()
    let allowed = false
    const moves: number[] = []
    const mounted = mountTimelineLever(
      host as unknown as HTMLElement,
      () => timeline(1, 4),
      (cursor) => moves.push(cursor),
      () => allowed,
    )
    const rail = (mounted.element as unknown as FakeElement).children[1]
    if (rail === undefined) throw new Error('timeline rail missing')

    const blocked = eventWith('keydown', { key: 'ArrowRight' })
    rail.dispatchEvent(blocked)
    expect(moves).toEqual([])
    expect(blocked.defaultPrevented).toBe(false)

    allowed = true
    const resumed = eventWith('keydown', { key: 'ArrowRight' })
    rail.dispatchEvent(resumed)
    expect(moves).toEqual([2])
    expect(resumed.defaultPrevented).toBe(true)
  })
})
