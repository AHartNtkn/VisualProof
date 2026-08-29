import { describe, expect, it } from 'vitest'
import {
  applyStationaryPointerRelease,
  attachWorldInput,
  type WorldInputActions,
} from '../../game/input'

class TestWorldTarget extends EventTarget {
  requestPointerLockCalls = 0
  rejectEngagement = false
  throwEngagement = false

  requestPointerLock(): Promise<void> {
    this.requestPointerLockCalls += 1
    if (this.throwEngagement) throw new Error('synchronous denial')
    return this.rejectEngagement ? Promise.reject(new Error('denied')) : Promise.resolve()
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

function event(type: string, properties: Record<string, number | string | boolean> = {}, cancelable = false): Event {
  return Object.defineProperties(new Event(type, { cancelable }), Object.fromEntries(
    Object.entries(properties).map(([name, value]) => [name, { value }]),
  ))
}

function createHarness(): {
  readonly target: TestWorldTarget
  readonly windowTarget: EventTarget
  readonly documentTarget: TestDocumentTarget
  readonly pointers: string[]
  readonly releases: Array<{
    readonly button: number
    readonly clientX: number
    readonly clientY: number
    readonly relativeDistance: number
  }>
  readonly engagements: boolean[]
  readonly escapes: { count: number }
  readonly swaps: { count: number }
  readonly catalogToggles: { count: number }
  readonly escapeHandled: { value: boolean }
  readonly input: ReturnType<typeof attachWorldInput>
} {
  const target = new TestWorldTarget()
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocumentTarget()
  const pointers: string[] = []
  const releases: Array<{
    readonly button: number
    readonly clientX: number
    readonly clientY: number
    readonly relativeDistance: number
  }> = []
  const engagements: boolean[] = []
  const escapes = { count: 0 }
  const swaps = { count: 0 }
  const catalogToggles = { count: 0 }
  const escapeHandled = { value: false }
  const actions: WorldInputActions = {
    pointerDown: (button, clientX, clientY) => pointers.push(`down:${button}:${clientX}:${clientY}`),
    pointerUp: (button, clientX, clientY, relativeDistance) => {
      pointers.push(`up:${button}:${clientX}:${clientY}`)
      releases.push({ button, clientX, clientY, relativeDistance })
    },
    pointerCancel: () => pointers.push('cancel'),
    engagementChanged: (active) => engagements.push(active),
    escape: () => { escapes.count += 1; return escapeHandled.value },
    swapTool: () => { swaps.count += 1 },
    toggleCatalog: () => { catalogToggles.count += 1 },
  }
  const input = attachWorldInput(target as unknown as HTMLElement, actions, {
    window: windowTarget as Window,
    document: documentTarget as unknown as Document,
  })

  return {
    target, windowTarget, documentTarget, pointers, releases, engagements, escapes, swaps, catalogToggles,
    escapeHandled, input,
  }
}

describe('world input sampling', () => {
  it('does not apply a secondary action after relative drag at fixed client coordinates', () => {
    // Catches composition deciding stationarity from client displacement alone.
    let secondaryActions = 0

    const applied = applyStationaryPointerRelease(
      { x: 70, y: 80 },
      { x: 70, y: 80, relativeDistance: 15 },
      () => { secondaryActions += 1 },
    )

    expect(applied).toBe(false)
    expect(secondaryActions).toBe(0)
  })

  it('transports single Digit1 and Tab presses without holding either key', () => {
    const { windowTarget, input, swaps, catalogToggles } = createHarness()
    const digit = event('keydown', { code: 'Digit1' }, true)
    const tab = event('keydown', { code: 'Tab' }, true)

    windowTarget.dispatchEvent(digit)
    windowTarget.dispatchEvent(tab)
    windowTarget.dispatchEvent(event('keydown', { code: 'Digit1', repeat: true }, true))
    windowTarget.dispatchEvent(event('keydown', { code: 'Tab', repeat: true }, true))

    expect(swaps.count).toBe(1)
    expect(catalogToggles.count).toBe(1)
    expect(digit.defaultPrevented).toBe(true)
    expect(tab.defaultPrevented).toBe(true)
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
  })

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
    const { target, windowTarget, documentTarget, input } = createHarness()

    windowTarget.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })

    documentTarget.pointerLockElement = target as unknown as Element
    windowTarget.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    windowTarget.dispatchEvent(event('mousemove', { movementX: -1, movementY: 7 }))
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 2, lookY: 3,
    })
    expect(input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
  })

  it('reports pointer coordinates and leaves an unhandled Escape browser-owned', () => {
    const { target, windowTarget, pointers, escapes, input } = createHarness()

    target.dispatchEvent(event('mousedown', { button: 0, clientX: 123, clientY: 456 }))
    const escape = event('keydown', { code: 'Escape' }, true)
    windowTarget.dispatchEvent(escape)

    expect(pointers).toEqual(['down:0:123:456'])
    expect(escapes.count).toBe(1)
    expect(escape.defaultPrevented).toBe(false)
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

  it('delivers raw pointer and wheel lifecycle while preventing native scrolling and menus', () => {
    const { target, windowTarget, pointers, escapes } = createHarness()
    target.dispatchEvent(event('mousedown', { button: 2, clientX: 70, clientY: 80 }))
    windowTarget.dispatchEvent(event('mousemove', { clientX: 74, clientY: 83 }))
    windowTarget.dispatchEvent(event('mouseup', { button: 2, clientX: 74, clientY: 83 }))
    const wheel = event('wheel', { deltaY: -120 }, true)
    target.dispatchEvent(wheel)
    const contextMenu = new Event('contextmenu', { cancelable: true })

    expect(target.dispatchEvent(contextMenu)).toBe(false)
    expect(contextMenu.defaultPrevented).toBe(true)
    expect(wheel.defaultPrevented).toBe(true)
    expect(pointers).toEqual([
      'down:2:70:80', 'up:2:74:83',
    ])
    expect(escapes.count).toBe(0)
  })

  it('reports cumulative pointer-locked relative distance when client coordinates stay fixed', () => {
    // Catches the gesture boundary losing relative drag motion before stationarity is decided.
    const harness = createHarness()
    harness.documentTarget.pointerLockElement = harness.target as unknown as Element
    harness.target.dispatchEvent(event('mousedown', { button: 2, clientX: 70, clientY: 80 }))
    harness.windowTarget.dispatchEvent(event('mousemove', {
      clientX: 70, clientY: 80, movementX: 3, movementY: 4,
    }))
    harness.windowTarget.dispatchEvent(event('mousemove', {
      clientX: 70, clientY: 80, movementX: -6, movementY: -8,
    }))

    harness.windowTarget.dispatchEvent(event('mouseup', {
      button: 2, clientX: 70, clientY: 80,
    }))

    expect(harness.releases).toEqual([{
      button: 2,
      clientX: 70,
      clientY: 80,
      relativeDistance: 15,
    }])
  })

  it('delivers one complete mouse gesture when compatibility pointer events surround it', () => {
    const { target, windowTarget, pointers } = createHarness()

    target.dispatchEvent(event('pointerdown', {
      button: 0, clientX: 70, clientY: 80, pointerId: 4,
    }))
    target.dispatchEvent(event('mousedown', { button: 0, clientX: 70, clientY: 80 }))
    windowTarget.dispatchEvent(event('mousemove', { clientX: 74, clientY: 83 }))
    target.dispatchEvent(event('pointerup', {
      button: 0, clientX: 74, clientY: 83, pointerId: 4,
    }))
    target.dispatchEvent(event('lostpointercapture', { pointerId: 4 }))
    windowTarget.dispatchEvent(event('mouseup', { button: 0, clientX: 74, clientY: 83 }))

    expect(pointers).toEqual([
      'down:0:70:80', 'up:0:74:83',
    ])
  })

  it('handles orbit Escape by requesting engagement synchronously in the key event', () => {
    const harness = createHarness()
    harness.escapeHandled.value = true
    const escape = event('keydown', { code: 'Escape' }, true)

    harness.windowTarget.dispatchEvent(escape)

    expect(escape.defaultPrevented).toBe(true)
    expect(harness.target.requestPointerLockCalls).toBe(1)
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
    harness.windowTarget.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
    harness.target.dispatchEvent(event('mousedown', { button: 0, clientX: 10, clientY: 20 }))

    interrupt(harness)
    harness.windowTarget.dispatchEvent(event('mousemove', {
      clientX: 30, clientY: 40, movementX: 0, movementY: 0,
    }))
    harness.windowTarget.dispatchEvent(event('mouseup', { button: 0, clientX: 30, clientY: 40 }))

    expect(harness.input.sample()).toEqual({
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    })
    expect(harness.pointers).toEqual(['down:0:10:20', 'cancel'])
    expect(harness.escapes.count).toBe(0)
    expect(harness.engagements.at(-1)).toBe(false)
  })

  it('completes a gesture when mouseup occurs outside the world element', () => {
    const harness = createHarness()
    harness.target.dispatchEvent(event('mousedown', { button: 0, clientX: 10, clientY: 20 }))

    harness.windowTarget.dispatchEvent(event('mouseup', { button: 0, clientX: 12, clientY: 24 }))

    expect(harness.pointers).toEqual(['down:0:10:20', 'up:0:12:24'])
  })

  it('detaches every input effect when disposed', () => {
    const harness = createHarness()
    harness.documentTarget.pointerLockElement = harness.target as unknown as Element
    harness.target.dispatchEvent(event('mousedown', { button: 0, clientX: 10, clientY: 20 }))
    harness.input.dispose()
    harness.input.dispose()

    harness.windowTarget.dispatchEvent(event('keydown', { code: 'KeyW' }))
    harness.windowTarget.dispatchEvent(event('mousemove', { movementX: 3, movementY: -4 }))
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
    expect(harness.pointers).toEqual(['down:0:10:20', 'cancel'])
    expect(harness.escapes.count).toBe(0)
  })

  it('engages and releases only the target world', async () => {
    const { target, documentTarget, input } = createHarness()

    await input.engage()
    expect(target.requestPointerLockCalls).toBe(1)
    documentTarget.pointerLockElement = new EventTarget() as unknown as Element
    input.release()
    expect(documentTarget.exitPointerLockCalls).toBe(0)

    documentTarget.pointerLockElement = target as unknown as Element
    input.release()
    expect(documentTarget.exitPointerLockCalls).toBe(1)
  })

  it('reports engagement changes and reports a rejected handled-Escape request inactive', async () => {
    const harness = createHarness()
    harness.documentTarget.pointerLockElement = harness.target as unknown as Element
    harness.documentTarget.dispatchEvent(event('pointerlockchange'))
    harness.escapeHandled.value = true
    harness.target.rejectEngagement = true

    harness.windowTarget.dispatchEvent(event('keydown', { code: 'Escape' }, true))
    await Promise.resolve()

    expect(harness.engagements).toEqual([false, true, false])
  })

  it('reports a synchronous handled-Escape engagement failure inactive', async () => {
    const harness = createHarness()
    harness.escapeHandled.value = true
    harness.target.throwEngagement = true

    expect(() => harness.windowTarget.dispatchEvent(
      event('keydown', { code: 'Escape' }, true),
    )).not.toThrow()
    await Promise.resolve()

    expect(harness.engagements).toEqual([false, false])
  })

  it('normalizes a synchronous ordinary engagement failure to a rejected promise', async () => {
    const harness = createHarness()
    harness.target.throwEngagement = true

    await expect(harness.input.engage()).rejects.toThrow('synchronous denial')
  })
})
