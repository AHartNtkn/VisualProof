import { describe, expect, it } from 'vitest'
import { attachWorldInput, type WorldInputActions } from '../../game/input'
import { WorldStateController } from '../../game/world-state'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import {
  enterOrbit,
  initialCameraState,
  type CameraState,
} from '../../src/game/camera'
import type { GameTree } from '../../src/game/model'
import { completeBranchCutting, ToolInventory } from '../../src/game/tools'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'

class TestWorldTarget extends EventTarget {
  requestPointerLock(): Promise<void> {
    return Promise.resolve()
  }
}

class TestDocumentTarget extends EventTarget {
  pointerLockElement: Element | null = null
  visibilityState: DocumentVisibilityState = 'visible'
  exitCalls = 0

  exitPointerLock(): void { this.exitCalls += 1 }
}

function key(code: string): Event {
  return Object.defineProperty(new Event('keydown', { cancelable: true }), 'code', { value: code })
}

function keyUp(code: string): Event {
  return Object.defineProperty(new Event('keyup'), 'code', { value: code })
}

function mouse(type: 'mousedown' | 'mouseup', button: number): Event {
  return Object.defineProperties(new Event(type), {
    button: { value: button },
    clientX: { value: 120 },
    clientY: { value: 80 },
  })
}

function sourceTree(): GameTree {
  const diagram = new DiagramBuilder().build()
  return {
    id: 'source',
    snapshot: snapshotFromDiagram(diagram),
    placement: { x: 0, z: 0, yaw: 0 },
  }
}

function composeWorld(options: {
  readonly camera: 'free' | 'orbit'
  readonly cutting: boolean
  readonly ledgerOpen: boolean
  readonly foregroundOpen?: boolean
}) {
  const free = initialCameraState({
    position: { x: 0, y: 1.7, z: 8 },
    yaw: 0,
    pitch: -0.18,
  })
  let camera: CameraState = options.camera === 'orbit'
    ? enterOrbit(free, {
        treeId: 'source',
        center: { x: 0, y: 1.7, z: 0 },
        radius: 2,
      })
    : free
  const tools = new ToolInventory(new Set(['sprout-spawner', 'iteration']))
  if (options.cutting) {
    tools.cycle('1', 0)
    const tree = sourceTree()
    tools.hold(completeBranchCutting(tree, tree.snapshot.diagram.root))
  }
  let ledgerOpen = options.ledgerOpen
  const orchardState = {
    revision: 11,
    treeIds: new Set(['source', 'neighbor']),
  }
  let pauseVisible = false
  let freeActive = true
  const pointerEvents: string[] = []
  const target = new TestWorldTarget()
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocumentTarget()
  let controller!: WorldStateController
  const actions: WorldInputActions = {
    pointerDown: () => { pointerEvents.push('down') },
    pointerUp: () => { pointerEvents.push('up') },
    pointerCancel: () => { pointerEvents.push('cancel') },
    category() {},
    toggleLedger() {},
    stepBack: () => { controller.stepBack() },
    toggleDeveloperMode() {},
    pause: () => { controller.pause() },
    engagementChanged: (active) => { freeActive = active },
  }
  const input = attachWorldInput(target as unknown as HTMLElement, actions, {
    window: windowTarget as Window,
    document: documentTarget as unknown as Document,
  })
  if (ledgerOpen) input.suspend()
  controller = new WorldStateController({
    getCamera: () => camera,
    setCamera: (next) => { camera = next },
    tools,
    ledger: { get isOpen() { return ledgerOpen } },
    foreground: { get isOpen() { return options.foregroundOpen ?? false } },
    input,
    pauseMenu: {
      show: () => { pauseVisible = true },
      hide: () => { pauseVisible = false },
    },
    worldName: () => 'My Orchard',
    setFreeActive: (active) => { freeActive = active },
    cuttingCleared() {},
    stateChanged() {},
  })
  return {
    controller,
    input,
    tools,
    windowTarget,
    target,
    documentTarget,
    pointerEvents,
    camera: () => camera,
    ledgerOpen: () => ledgerOpen,
    closeLedger: () => {
      ledgerOpen = false
      input.resume()
    },
    pauseVisible: () => pauseVisible,
    freeActive: () => freeActive,
    orchardState,
  }
}

describe('world state controls', () => {
  it.each([
    ['free flight', { camera: 'free', cutting: false, ledgerOpen: false }],
    ['orbit', { camera: 'orbit', cutting: false, ledgerOpen: false }],
    ['held cutting', { camera: 'free', cutting: true, ledgerOpen: false }],
    ['open ledger', { camera: 'free', cutting: false, ledgerOpen: true }],
  ] as const)('preserves exact %s state across Escape and Resume', (_name, options) => {
    // Catches Pause or Resume clearing a cutting, exiting orbit, or closing/unsuspending the ledger.
    const world = composeWorld(options)
    const cameraBefore = world.camera()
    const cuttingBefore = world.tools.cutting
    const escape = key('Escape')

    world.windowTarget.dispatchEvent(escape)

    expect(escape.defaultPrevented).toBe(true)
    expect(world.controller.isPaused).toBe(true)
    expect(world.pauseVisible()).toBe(true)
    expect(world.camera()).toBe(cameraBefore)
    expect(world.tools.cutting).toBe(cuttingBefore)
    expect(world.ledgerOpen()).toBe(options.ledgerOpen)

    world.controller.resume()

    expect(world.controller.isPaused).toBe(false)
    expect(world.pauseVisible()).toBe(false)
    expect(world.camera()).toBe(cameraBefore)
    expect(world.tools.cutting).toBe(cuttingBefore)
    expect(world.ledgerOpen()).toBe(options.ledgerOpen)
    world.windowTarget.dispatchEvent(key('KeyW'))
    expect(world.input.sample().forward).toBe(options.ledgerOpen ? 0 : 1)
  })

  it('clears a held cutting before exiting orbit on the next Backspace', () => {
    // Catches step-back applying two world mutations in one press or reversing their priority.
    const world = composeWorld({ camera: 'orbit', cutting: true, ledgerOpen: false })
    const orbit = world.camera()
    expect(world.tools.selected('1')).toBe('iteration')

    world.windowTarget.dispatchEvent(key('Backspace'))

    expect(world.tools.cutting).toBeNull()
    expect(world.camera()).toBe(orbit)

    world.windowTarget.dispatchEvent(keyUp('Backspace'))
    world.windowTarget.dispatchEvent(key('Backspace'))

    expect(world.camera().mode).toBe('free')
    expect(world.tools.cutting).toBeNull()
  })

  it('preserves one maximal reachable world state across Pause and Resume', () => {
    // Catches state-conditional Pause/Resume logic that clears the held cutting, exits orbit,
    // changes the selected tool, closes or unsuspends the ledger, or mutates orchard state.
    const world = composeWorld({ camera: 'orbit', cutting: true, ledgerOpen: true })
    const cameraBefore = world.camera()
    const cuttingBefore = world.tools.cutting
    const orchardBefore = world.orchardState

    expect(cameraBefore.mode).toBe('orbit')
    expect(cuttingBefore).not.toBeNull()
    expect(world.tools.selected('1')).toBe('iteration')
    expect(world.ledgerOpen()).toBe(true)
    world.windowTarget.dispatchEvent(key('Escape'))
    world.controller.resume()

    expect(world.camera()).toBe(cameraBefore)
    expect(world.tools.cutting).toBe(cuttingBefore)
    expect(world.tools.selected('1')).toBe('iteration')
    expect(world.ledgerOpen()).toBe(true)
    expect(world.orchardState).toBe(orchardBefore)
    expect(world.orchardState).toEqual({
      revision: 11,
      treeIds: new Set(['source', 'neighbor']),
    })

    world.windowTarget.dispatchEvent(key('KeyW'))
    expect(world.input.sample().forward).toBe(0)
    world.closeLedger()
    world.windowTarget.dispatchEvent(keyUp('KeyW'))
    world.windowTarget.dispatchEvent(key('KeyW'))
    expect(world.input.sample().forward).toBe(1)
  })

  it('releases active world capture for developer interaction without mutating world state', () => {
    // Catches developer reachability exiting orbit, clearing tools, or changing progression/world data.
    const world = composeWorld({ camera: 'orbit', cutting: true, ledgerOpen: false })
    const cameraBefore = world.camera()
    const cuttingBefore = world.tools.cutting
    const orchardBefore = world.orchardState
    world.documentTarget.pointerLockElement = world.target as unknown as Element
    world.documentTarget.dispatchEvent(new Event('pointerlockchange'))

    world.controller.releasePointerForDeveloperMode()

    expect(world.documentTarget.exitCalls).toBe(1)
    expect(world.freeActive()).toBe(false)
    expect(world.camera()).toBe(cameraBefore)
    expect(world.tools.cutting).toBe(cuttingBefore)
    expect(world.orchardState).toBe(orchardBefore)
    expect(world.controller.isPaused).toBe(false)
    expect(world.ledgerOpen()).toBe(false)
  })

  it('synchronously cancels an active gesture before developer-mode pointer release', () => {
    // Catches a mouseup racing pointerlockchange and committing a world action after mode activation.
    const world = composeWorld({ camera: 'orbit', cutting: true, ledgerOpen: false })
    const cameraBefore = world.camera()
    const cuttingBefore = world.tools.cutting
    world.documentTarget.pointerLockElement = world.target as unknown as Element
    world.documentTarget.dispatchEvent(new Event('pointerlockchange'))
    world.target.dispatchEvent(mouse('mousedown', 2))

    world.controller.releasePointerForDeveloperMode()
    world.windowTarget.dispatchEvent(mouse('mouseup', 2))

    expect(world.pointerEvents).toEqual(['down', 'cancel'])
    expect(world.camera()).toBe(cameraBefore)
    expect(world.tools.cutting).toBe(cuttingBefore)
  })

  it('restores unlocked world input after developer mode turns off', () => {
    // Catches synchronous gesture cancellation leaving ordinary click-to-engage controls suspended.
    const world = composeWorld({ camera: 'free', cutting: false, ledgerOpen: false })
    world.controller.releasePointerForDeveloperMode()
    world.windowTarget.dispatchEvent(key('KeyW'))
    expect(world.input.sample().forward).toBe(0)

    world.controller.resumeAfterDeveloperMode()
    world.windowTarget.dispatchEvent(keyUp('KeyW'))
    world.windowTarget.dispatchEvent(key('KeyW'))

    expect(world.input.sample().forward).toBe(1)
    expect(world.freeActive()).toBe(false)
  })

  it('keeps world input suspended when Resume restores a foreground editor', () => {
    // Catches Resume stealing capture and keyboard ownership from preserved editor state.
    const world = composeWorld({
      camera: 'free', cutting: false, ledgerOpen: false, foregroundOpen: true,
    })

    world.controller.pause()
    world.controller.resume()
    world.windowTarget.dispatchEvent(key('KeyW'))

    expect(world.controller.isPaused).toBe(false)
    expect(world.pauseVisible()).toBe(false)
    expect(world.freeActive()).toBe(false)
    expect(world.input.sample().forward).toBe(0)
  })
})
