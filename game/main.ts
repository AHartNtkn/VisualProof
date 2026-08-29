import './style.css'
if (import.meta.env.VITE_WDIO === 'true') void import('@wdio/tauri-plugin')

import { DiagramBuilder, diagramToJson } from '../src/kernel/diagram'
import {
  advanceCamera,
  cameraPoseForSave,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  initialCameraState,
  type CameraMotion,
  type CameraState,
} from '../src/game/camera'
import type { GameWorld } from '../src/game/model'
import { SettledFrameTelemetry, frameTiming, percentile } from '../src/game/render/frame'
import { mountGameWorld, type GameWorldRenderer } from '../src/game/render/world'
import { saveClient, treeUpdateFromGameTree, type CameraRecord, type SlotListEntry, type TreeUpdate } from '../src/game/save-client'
import { SaveWriter } from '../src/game/save-writer'
import { gameSession, publishTreeMutation, type GameSession } from '../src/game/session'
import { StartLifecycle, type StartFailure } from '../src/game/start-lifecycle'
import { attachWorldInput, type WorldInput } from './input'

const root = document.querySelector<HTMLElement>('[data-game]')!
const worldHost = document.querySelector<HTMLElement>('[data-world]')!
const start = document.querySelector<HTMLElement>('[data-start]')!
const createForm = document.querySelector<HTMLFormElement>('[data-create-form]')!
const nameInput = document.querySelector<HTMLInputElement>('#orchard-name')!
const slotLoading = document.querySelector<HTMLElement>('[data-slot-loading]')!
const slotList = document.querySelector<HTMLUListElement>('[data-slot-list]')!
const menuError = document.querySelector<HTMLElement>('[data-menu-error]')!
const hud = document.querySelector<HTMLElement>('[data-hud]')!
const worldName = document.querySelector<HTMLElement>('[data-world-name]')!
const saveStatus = document.querySelector<HTMLElement>('[data-save-status]')!
const saveRetry = document.querySelector<HTMLButtonElement>('[data-save-retry]')!
const feedback = document.querySelector<HTMLElement>('[data-feedback]')!
const reticle = document.querySelector<HTMLElement>('[data-reticle]')!
const engage = document.querySelector<HTMLElement>('[data-engage]')!

const blankDiagram = new DiagramBuilder().build()
const blankDiagramJson = JSON.stringify(diagramToJson(blankDiagram))
const initialCameraRecord: CameraRecord = { x: 0, y: 1.7, z: 8, yaw: 0, pitch: -0.18 }
const initialTree: TreeUpdate = { treeId: 'tree-0000', diagramJson: blankDiagramJson, x: 0, z: 0, yaw: 0 }
const NEUTRAL_MOTION: CameraMotion = {
  forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
}
const slotControlReleases: Array<() => void> = []
const telemetry = new SettledFrameTelemetry(60)
let maxRepresentationOperations = 0
let camera: CameraState | null = null
let input: WorldInput | null = null
let session: GameSession | null = null
let writer: SaveWriter | null = null
let renderer: GameWorldRenderer | null = null
let animationFrame = 0
let previousFrame = performance.now()
let disposed = false

if (import.meta.env.VITE_WDIO === 'true') {
  Object.defineProperty(window, '__ORCHARD_WDIO__', {
    configurable: false,
    value: Object.freeze({
      setRenderMode(mode: 'game' | 'raw'): void {
        if (mode !== 'game' && mode !== 'raw') throw new Error(`invalid render mode '${String(mode)}'`)
        if (renderer === null) throw new Error('world is not loaded')
        renderer.setRenderMode(mode)
        maxRepresentationOperations = 0
        root.dataset['renderMode'] = mode
        telemetry.beginTransition()
      },
    }),
    writable: false,
  })
}

function message(error: unknown): string {
  return error instanceof Error ? error.message : String(error)
}

function setError(value: string): void {
  root.dataset['errors'] = value
  feedback.textContent = value
  feedback.classList.toggle('error', value.length > 0)
}

function clearError(): void {
  setError('')
  menuError.textContent = ''
}

function renderSlots(slots: readonly SlotListEntry[]): void {
  for (const release of slotControlReleases.splice(0)) release()
  slotList.replaceChildren()
  if (slots.length === 0) {
    const empty = document.createElement('li')
    empty.className = 'slot-empty'
    empty.textContent = 'No saved orchards yet.'
    slotList.appendChild(empty)
    return
  }
  for (const slot of slots) {
    const item = document.createElement('li')
    item.className = `slot${slot.error === null ? '' : ' invalid'}`
    const copy = document.createElement('div')
    const title = document.createElement('strong')
    title.textContent = slot.displayName
    const detail = document.createElement('small')
    detail.textContent = slot.error ?? `Updated ${new Date(slot.updatedAtMs).toLocaleString()}`
    copy.append(title, detail)
    item.appendChild(copy)
    if (slot.error === null) {
      const load = document.createElement('button')
      load.type = 'button'
      load.textContent = 'Load'
      load.dataset['loadSlot'] = slot.slotId
      load.addEventListener('click', () => {
        clearError()
        startOpening(() => saveClient.load(slot.slotId))
      })
      slotControlReleases.push(startLifecycle.registerControl(load))
      item.appendChild(load)
    }
    slotList.appendChild(item)
  }
}

function pointerNdc(clientX: number, clientY: number, canvas: HTMLCanvasElement): readonly [number, number] {
  const bounds = canvas.getBoundingClientRect()
  return [
    ((clientX - bounds.left) / Math.max(1, bounds.width)) * 2 - 1,
    1 - ((clientY - bounds.top) / Math.max(1, bounds.height)) * 2,
  ]
}

function mirrorControls(): void {
  if (camera === null) return
  const display = displayCameraPose(camera)
  const inputEngaged = input?.engaged() ?? false
  root.dataset['cameraMode'] = camera.mode
  root.dataset['inputEngaged'] = String(inputEngaged)
  root.dataset['orbitTarget'] = camera.mode === 'orbit' ? camera.target.treeId : ''
  root.dataset['displayedEye'] = JSON.stringify(display.eye)
  root.dataset['displayedDirection'] = JSON.stringify(display.forward)
  reticle.hidden = camera.mode !== 'free' || !inputEngaged
  engage.hidden = camera.mode !== 'free' || inputEngaged
}

function resize(): void {
  renderer?.resize(worldHost.clientWidth, worldHost.clientHeight)
}

function animate(now: number): void {
  const activeRenderer = renderer
  const activeInput = input
  const activeWriter = writer
  const currentCamera = camera
  if (
    disposed
    || currentCamera === null
    || activeInput === null
    || activeWriter === null
    || activeRenderer === null
  ) return
  const timing = frameTiming(now, previousFrame)
  previousFrame = now
  const sampledMotion = activeInput.sample()
  const motion = currentCamera.mode === 'free' && !activeInput.engaged()
    ? NEUTRAL_MOTION
    : sampledMotion
  const nextCamera = advanceCamera(currentCamera, motion, timing.movementSeconds)
  camera = nextCamera
  activeRenderer.setCamera(displayCameraPose(nextCamera))
  const rendered = activeRenderer.render(now)
  maxRepresentationOperations = Math.max(maxRepresentationOperations, rendered.representationOperations)
  activeWriter.camera(cameraPoseForSave(nextCamera))
  const settled = telemetry.record({ frameMs: timing.sampleMs, pending: rendered.pending, buildMs: rendered.buildMs, operations: rendered.representationOperations })
  root.dataset['representedCount'] = String(rendered.representedEntities)
  root.dataset['logicalCount'] = String(rendered.logical)
  root.dataset['visibleCount'] = String(rendered.visible)
  root.dataset['residentCount'] = String(rendered.resident)
  root.dataset['fullCount'] = String(rendered.full)
  root.dataset['reducedCount'] = String(rendered.reduced)
  root.dataset['markerCount'] = String(rendered.marker)
  root.dataset['culledCount'] = String(rendered.culled)
  root.dataset['pendingRepresentationCount'] = String(rendered.pending)
  root.dataset['representationErrorCount'] = String(rendered.representationErrors)
  root.dataset['representationError'] = rendered.error ?? ''
  root.dataset['pointLightCount'] = String(rendered.pointLights)
  root.dataset['instancedCount'] = String(rendered.instanced)
  root.dataset['drawCalls'] = String(rendered.drawCalls)
  root.dataset['geometries'] = String(rendered.geometries)
  root.dataset['representationOperations'] = String(rendered.representationOperations)
  root.dataset['maxRepresentationOperations'] = String(maxRepresentationOperations)
  root.dataset['settledFrameSamples'] = String(settled.sampleCount)
  root.dataset['p95FrameMs'] = String(percentile(settled.samples, 0.95))
  root.dataset['transitionBuildMs'] = String(settled.transitionBuildMs)
  root.dataset['transitionGeneration'] = String(settled.transitionGeneration)
  root.dataset['settledGeneration'] = String(settled.settledGeneration)
  if (rendered.error !== null) setError(`Renderer: ${rendered.error}`)
  mirrorControls()
  animationFrame = requestAnimationFrame(animate)
}

function applyDoubleCut(clientX: number, clientY: number): void {
  const activeCamera = camera
  const activeInput = input
  const activeSession = session
  const activeWriter = writer
  const activeRenderer = renderer
  if (
    activeCamera === null
    || activeInput === null
    || activeSession === null
    || activeWriter === null
    || activeRenderer === null
  ) return
  if (activeCamera.mode === 'free' && !activeInput.engaged()) return
  const [ndcX, ndcY] = activeCamera.mode === 'free'
    ? [0, 0]
    : pointerNdc(clientX, clientY, activeRenderer.canvas)
  const pointed = activeRenderer.pointAtBranch(
    ndcX,
    ndcY,
    activeCamera.mode === 'orbit' ? activeCamera.target.treeId : null,
  )
  if (pointed === null) {
    setError('Double cut requires an ordinary branch within reach.')
    return
  }
  try {
    const mutation = activeSession.planDoubleCut(pointed)
    publishTreeMutation(
      activeSession,
      mutation,
      activeRenderer,
      (tree) => activeWriter.tree(treeUpdateFromGameTree(tree)),
    )
    setError('')
    feedback.textContent = `Double cut applied to ${mutation.treeId}.`
  } catch (error) {
    setError(`Double cut failed: ${message(error)}`)
  }
}

async function startWorld(world: GameWorld): Promise<void> {
  const nextRenderer = mountGameWorld(worldHost, [...world.trees.values()])
  const nextCamera = initialCameraState(world.camera)
  const nextSession = gameSession(world.trees)
  const nextWriter = new SaveWriter(world.slot.id, saveClient)
  let nextInput: WorldInput | null = null
  let releaseWriterStatus = (): void => {}
  try {
    nextRenderer.resize(worldHost.clientWidth, worldHost.clientHeight)
    nextRenderer.setCamera(displayCameraPose(nextCamera))
    releaseWriterStatus = nextWriter.subscribe((status) => {
      saveStatus.textContent = status.state === 'idle'
        ? 'Saved'
        : status.state === 'saving' ? 'Saving…' : `Save error: ${status.message ?? 'unknown error'}`
      saveStatus.classList.toggle('error', status.state === 'error')
      saveRetry.hidden = status.state !== 'error'
      root.dataset['saveState'] = status.state
      if (status.state === 'error') setError(saveStatus.textContent)
    })
    nextInput = attachWorldInput(worldHost, {
      primary() {
        const activeCamera = camera
        const activeInput = input
        const activeRenderer = renderer
        if (activeCamera === null || activeInput === null || activeRenderer === null) return
        if (activeCamera.mode === 'orbit') return
        if (!activeInput.engaged()) {
          void activeInput.engage().then(mirrorControls, mirrorControls)
          return
        }
        const target = activeRenderer.pickTree(0, 0)
        if (target === null) return
        camera = enterOrbit(activeCamera, target)
        activeInput.release()
        mirrorControls()
      },
      secondary(clientX, clientY) {
        applyDoubleCut(clientX, clientY)
      },
      escape() {
        if (camera?.mode !== 'orbit') return
        camera = exitOrbit(camera)
        mirrorControls()
      },
    })
    renderer = nextRenderer
    camera = nextCamera
    input = nextInput
    session = nextSession
    writer = nextWriter
    start.hidden = true
    hud.hidden = false
    worldName.textContent = world.slot.name
    root.dataset['ready'] = 'true'
    root.dataset['loadedSlot'] = world.slot.id
    maxRepresentationOperations = 0
    root.dataset['renderMode'] = 'game'
    telemetry.beginTransition()
    mirrorControls()
    previousFrame = performance.now()
    animationFrame = requestAnimationFrame(animate)
  } catch (error) {
    nextInput?.dispose()
    releaseWriterStatus()
    await nextWriter.dispose().catch(() => {})
    nextRenderer.dispose()
    start.hidden = false
    hud.hidden = true
    root.dataset['ready'] = 'false'
    root.dataset['loadedSlot'] = ''
    throw error
  }
}

function showStartFailure(failure: StartFailure): void {
  const concrete = `Could not open orchard: ${failure.message}`
  menuError.textContent = concrete
  root.dataset['errors'] = concrete
}

const startLifecycle = new StartLifecycle({ open: startWorld, fail: showStartFailure })
startLifecycle.registerControl(nameInput)
for (const button of createForm.querySelectorAll<HTMLButtonElement>('button')) startLifecycle.registerControl(button)

function startOpening(operation: () => Promise<GameWorld>): void {
  void startLifecycle.start(operation)
}

createForm.addEventListener('submit', (event) => {
  event.preventDefault()
  if (startLifecycle.busy || camera !== null) return
  const displayName = nameInput.value.trim()
  if (displayName.length === 0) {
    menuError.textContent = 'Enter a name for the new orchard.'
    return
  }
  clearError()
  startOpening(() => saveClient.create(displayName, initialCameraRecord, [initialTree]).then((created) => saveClient.load(created.slotId)))
})
saveRetry.addEventListener('click', () => writer?.retry())

const resizeObserver = new ResizeObserver(resize)
resizeObserver.observe(worldHost)

window.addEventListener('pagehide', () => {
  if (disposed) return
  disposed = true
  startLifecycle.dispose()
  cancelAnimationFrame(animationFrame)
  resizeObserver.disconnect()
  input?.dispose()
  input = null
  session = null
  void writer?.dispose().catch((error: unknown) => setError(`Save shutdown failed: ${message(error)}`))
  renderer?.dispose()
  renderer = null
})

void saveClient.list().then((slots) => {
  if (disposed) return
  slotLoading.hidden = true
  renderSlots(slots)
}).catch((error: unknown) => {
  if (disposed) return
  slotLoading.textContent = `Could not list saves: ${message(error)}`
  menuError.textContent = slotLoading.textContent
  root.dataset['errors'] = slotLoading.textContent
})
