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

  exitPointerLock(): void {}
}

function key(code: string): Event {
  return Object.defineProperty(new Event('keydown', { cancelable: true }), 'code', { value: code })
}

function keyUp(code: string): Event {
  return Object.defineProperty(new Event('keyup'), 'code', { value: code })
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
    const tree = sourceTree()
    tools.hold(completeBranchCutting(tree, tree.snapshot.diagram.root))
  }
  let ledgerOpen = options.ledgerOpen
  let pauseVisible = false
  let freeActive = true
  const target = new TestWorldTarget()
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocumentTarget()
  let controller!: WorldStateController
  const actions: WorldInputActions = {
    pointerDown() {},
    pointerUp() {},
    pointerCancel() {},
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
    camera: () => camera,
    ledgerOpen: () => ledgerOpen,
    pauseVisible: () => pauseVisible,
    freeActive: () => freeActive,
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

    world.windowTarget.dispatchEvent(key('Backspace'))

    expect(world.tools.cutting).toBeNull()
    expect(world.camera()).toBe(orbit)

    world.windowTarget.dispatchEvent(keyUp('Backspace'))
    world.windowTarget.dispatchEvent(key('Backspace'))

    expect(world.camera().mode).toBe('free')
    expect(world.tools.cutting).toBeNull()
  })
})
