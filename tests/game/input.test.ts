import { describe, expect, it } from 'vitest'
import { attachWorldInput } from '../../game/input'

class TestWorldTarget extends EventTarget {
  requestPointerLockCalls = 0

  requestPointerLock(): Promise<void> {
    this.requestPointerLockCalls += 1
    return Promise.resolve()
  }
}

class TestDocumentTarget extends EventTarget {
  pointerLockElement: Element | null = null
  visibilityState: DocumentVisibilityState = 'visible'
  exitPointerLockCalls = 0

  exitPointerLock(): void {
    this.exitPointerLockCalls += 1
  }
}

function event(type: string, properties: Record<string, number | string> = {}): Event {
  return Object.defineProperties(new Event(type), Object.fromEntries(
    Object.entries(properties).map(([name, value]) => [name, { value }]),
  ))
}

function createHarness(): {
  readonly target: TestWorldTarget
  readonly windowTarget: EventTarget
  readonly documentTarget: TestDocumentTarget
  readonly primary: Array<readonly [number, number]>
  readonly escapes: { count: number }
  readonly input: ReturnType<typeof attachWorldInput>
} {
  const target = new TestWorldTarget()
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocumentTarget()
  const primary: Array<readonly [number, number]> = []
  const escapes = { count: 0 }
  const input = attachWorldInput(target as unknown as HTMLElement, {
    primary: (clientX, clientY) => primary.push([clientX, clientY]),
    escape: () => { escapes.count += 1 },
  }, {
    window: windowTarget as Window,
    document: documentTarget as unknown as Document,
  })

  return { target, windowTarget, documentTarget, primary, escapes, input }
}

describe('world input sampling', () => {
  it('samples held movement keys and releases only the lifted key', () => {
    const { windowTarget, input } = createHarness()

    for (const code of ['KeyW', 'KeyD', 'Space', 'ShiftLeft']) {
      windowTarget.dispatchEvent(event('keydown', { code }))
    }
    expect(input.sample()).toEqual({
      forward: 1, strafe: 1, vertical: 1, sprint: true, lookX: 0, lookY: 0,
    })

    for (const code of ['KeyS', 'KeyA', 'ControlLeft']) {
      windowTarget.dispatchEvent(event('keydown', { code }))
    }
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: true, lookX: 0, lookY: 0,
    })

    windowTarget.dispatchEvent(event('keyup', { code: 'KeyA' }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 1, vertical: 0, sprint: true, lookX: 0, lookY: 0,
    })
  })

  it('consumes accumulated pointer motion only while the world is engaged', () => {
    const { target, documentTarget, input } = createHarness()

    target.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })

    documentTarget.pointerLockElement = target as unknown as Element
    target.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    target.dispatchEvent(event('mousemove', { movementX: -1, movementY: 7 }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 2, lookY: 3,
    })
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
  })

  it('reports primary coordinates and escape synchronously without retaining escape', () => {
    const { target, windowTarget, primary, escapes, input } = createHarness()

    target.dispatchEvent(event('mousedown', { button: 0, clientX: 123, clientY: 456 }))
    windowTarget.dispatchEvent(event('keydown', { code: 'Escape' }))

    expect(primary).toEqual([[123, 456]])
    expect(escapes.count).toBe(1)
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
  })

  it('maps the right Control and Shift keys', () => {
    const { windowTarget, input } = createHarness()

    for (const code of ['Space', 'ControlRight', 'ShiftRight']) {
      windowTarget.dispatchEvent(event('keydown', { code }))
    }
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: true, lookX: 0, lookY: 0,
    })

    windowTarget.dispatchEvent(event('keyup', { code: 'ControlRight' }))
    windowTarget.dispatchEvent(event('keyup', { code: 'ShiftRight' }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 1, sprint: false, lookX: 0, lookY: 0,
    })
  })

  it('prevents the world context menu without a semantic action', () => {
    const { target, primary, escapes } = createHarness()
    const contextMenu = new Event('contextmenu', { cancelable: true })

    expect(target.dispatchEvent(contextMenu)).toBe(false)
    expect(contextMenu.defaultPrevented).toBe(true)
    expect(primary).toEqual([])
    expect(escapes.count).toBe(0)
  })
})

describe('world input interruption and lifecycle', () => {
  it.each([
    ['pointer-lock loss', (harness: ReturnType<typeof createHarness>) => {
      harness.documentTarget.pointerLockElement = null
      harness.documentTarget.dispatchEvent(event('pointerlockchange'))
    }],
    ['window blur', (harness: ReturnType<typeof createHarness>) => {
      harness.windowTarget.dispatchEvent(event('blur'))
    }],
    ['hidden visibility', (harness: ReturnType<typeof createHarness>) => {
      harness.documentTarget.visibilityState = 'hidden'
      harness.documentTarget.dispatchEvent(event('visibilitychange'))
    }],
  ] as const)('clears held input on %s without semantic actions', (_name, interrupt) => {
    const harness = createHarness()
    harness.documentTarget.pointerLockElement = harness.target as unknown as Element
    harness.windowTarget.dispatchEvent(event('keydown', { code: 'KeyW' }))
    harness.target.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))

    interrupt(harness)

    expect(harness.input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
    expect(harness.primary).toEqual([])
    expect(harness.escapes.count).toBe(0)
  })

  it('detaches every input effect when disposed', () => {
    const harness = createHarness()
    harness.documentTarget.pointerLockElement = harness.target as unknown as Element
    harness.input.dispose()
    harness.input.dispose()

    harness.windowTarget.dispatchEvent(event('keydown', { code: 'KeyW' }))
    harness.target.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    harness.target.dispatchEvent(event('mousedown', { button: 0, clientX: 123, clientY: 456 }))
    harness.windowTarget.dispatchEvent(event('keydown', { code: 'Escape' }))
    harness.documentTarget.pointerLockElement = null
    harness.documentTarget.dispatchEvent(event('pointerlockchange'))
    harness.windowTarget.dispatchEvent(event('blur'))
    harness.documentTarget.visibilityState = 'hidden'
    harness.documentTarget.dispatchEvent(event('visibilitychange'))

    expect(harness.input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
    expect(harness.primary).toEqual([])
    expect(harness.escapes.count).toBe(0)
  })

  it('engages and releases only the target world', async () => {
    const { target, documentTarget, input } = createHarness()

    await input.engage()
    expect(target.requestPointerLockCalls).toBe(1)
    expect(input.engaged()).toBe(false)

    documentTarget.pointerLockElement = new EventTarget() as unknown as Element
    input.release()
    expect(documentTarget.exitPointerLockCalls).toBe(0)

    documentTarget.pointerLockElement = target as unknown as Element
    expect(input.engaged()).toBe(true)
    input.release()
    expect(documentTarget.exitPointerLockCalls).toBe(1)
  })
})
