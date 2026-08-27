import './style.css'
import { DiagramBuilder, diagramToJson } from '../src/kernel/diagram'
import {
  INTERACTION_REACH,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  freePoseForPersistence,
  lookCamera,
  stepCamera,
  type CameraInput,
  type CameraState,
  type TreeWorldBounds,
} from '../src/game/camera'
import type { GameTree, GameWorld } from '../src/game/model'
import { SettledFrameTelemetry, frameTiming } from '../src/game/render/frame'
import { TREE_TWEEN_MS } from '../src/game/render/dynamic-tree'
import { mountGameWorld } from '../src/game/render/world'
import { saveClient, type CameraRecord, type SlotListEntry, type TreeUpdate } from '../src/game/save-client'
import { SaveWriter } from '../src/game/save-writer'
import { gameSession, useDoubleCut, type GameSession, type PointedTreePart } from '../src/game/session'
import {
  PointerLockGate,
  ResumePointerLock,
  StartLifecycle,
  type PointerLockPort,
  type StartFailure,
} from '../src/game/start-lifecycle'
import { scene3 } from '../src/view3d/scene'

const root = document.querySelector<HTMLElement>('[data-game]')!
const worldHost = document.querySelector<HTMLElement>('[data-world]')!
const start = document.querySelector<HTMLElement>('[data-start]')!
const createForm = document.querySelector<HTMLFormElement>('[data-create-form]')!
const nameInput = document.querySelector<HTMLInputElement>('#orchard-name')!
const slotLoading = document.querySelector<HTMLElement>('[data-slot-loading]')!
const slotList = document.querySelector<HTMLUListElement>('[data-slot-list]')!
const menuError = document.querySelector<HTMLElement>('[data-menu-error]')!
const reticle = document.querySelector<HTMLElement>('[data-reticle]')!
const hud = document.querySelector<HTMLElement>('[data-hud]')!
const worldName = document.querySelector<HTMLElement>('[data-world-name]')!
const saveStatus = document.querySelector<HTMLElement>('[data-save-status]')!
const saveRetry = document.querySelector<HTMLButtonElement>('[data-save-retry]')!
const freeHint = document.querySelector<HTMLElement>('[data-free-hint]')!
const orbitHint = document.querySelector<HTMLElement>('[data-orbit-hint]')!
const pointedLabel = document.querySelector<HTMLElement>('[data-pointed]')!
const feedback = document.querySelector<HTMLElement>('[data-feedback]')!
const resume = document.querySelector<HTMLButtonElement>('[data-resume]')!

const blankDiagram = new DiagramBuilder().build()
const blankDiagramJson = JSON.stringify(diagramToJson(blankDiagram))
const initialCameraRecord: CameraRecord = { x: 0, y: 1.7, z: 8, yaw: 0, pitch: -0.18 }
const initialTree: TreeUpdate = {
  treeId: 'tree-0000',
  diagramJson: blankDiagramJson,
  x: 0,
  z: 0,
  yaw: 0,
}
const renderer = mountGameWorld(worldHost, [])
const pointerLockPort: PointerLockPort = {
  request: () => renderer.canvas.requestPointerLock(),
  isLocked: () => document.pointerLockElement === renderer.canvas,
  onChange(listener) {
    document.addEventListener('pointerlockchange', listener)
    return () => document.removeEventListener('pointerlockchange', listener)
  },
  onError(listener) {
    const callback = (): void => listener()
    document.addEventListener('pointerlockerror', callback)
    return () => document.removeEventListener('pointerlockerror', callback)
  },
  release() {
    if (document.pointerLockElement !== null) document.exitPointerLock()
  },
}
const pointerLock = new PointerLockGate(pointerLockPort)
const resumePointerLock = new ResumePointerLock(pointerLock)
const keys = new Set<string>()
const activeTweens = new Map<string, number>()
const slotControlReleases: Array<() => void> = []
const telemetry = new SettledFrameTelemetry(60)
let session: GameSession | null = null
let camera: CameraState | null = null
let writer: SaveWriter | null = null
let animationFrame = 0
let previousFrame = performance.now()
let disposed = false

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

function requestPlayPointerLock(): void {
  void resumePointerLock.request().catch((error: unknown) => {
    if (disposed) return
    setError(`Pointer lock failed: ${message(error)}`)
    resume.hidden = false
  })
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
      load.addEventListener('click', () => {
        clearError()
        void startLifecycle.start(() => saveClient.load(slot.slotId))
      })
      slotControlReleases.push(startLifecycle.registerControl(load))
      item.appendChild(load)
    }
    slotList.appendChild(item)
  }
}

function pointerNdc(event: MouseEvent, canvas: HTMLCanvasElement): readonly [number, number] {
  const bounds = canvas.getBoundingClientRect()
  return [
    ((event.clientX - bounds.left) / Math.max(1, bounds.width)) * 2 - 1,
    1 - ((event.clientY - bounds.top) / Math.max(1, bounds.height)) * 2,
  ]
}

function worldBounds(tree: GameTree): TreeWorldBounds {
  const bounds = scene3(tree.diagram)
  const cosine = Math.cos(tree.placement.yaw)
  const sine = Math.sin(tree.placement.yaw)
  return {
    center: {
      x: tree.placement.x + bounds.center.x * cosine + bounds.center.z * sine,
      y: bounds.center.y,
      z: tree.placement.z - bounds.center.x * sine + bounds.center.z * cosine,
    },
    radius: bounds.radius,
  }
}

function mirrorCamera(): void {
  if (camera === null) return
  const display = displayCameraPose(camera)
  root.dataset['cameraMode'] = camera.mode
  root.dataset['displayedEye'] = JSON.stringify(display.eye)
  root.dataset['displayedDirection'] = JSON.stringify(display.forward)
  root.dataset['orbitTarget'] = camera.mode === 'orbit' ? camera.orbitTarget : ''
  freeHint.hidden = camera.mode !== 'free'
  orbitHint.hidden = camera.mode !== 'orbit'
  reticle.hidden = camera.mode !== 'free'
}

function mirrorPoint(pointed: PointedTreePart | null): void {
  root.dataset['pointedTreeId'] = pointed?.treeId ?? ''
  root.dataset['pointedEntityId'] = pointed?.entityKey ?? ''
  pointedLabel.hidden = pointed === null
  pointedLabel.textContent = pointed === null
    ? ''
    : `${pointed.treeId} · ${pointed.entityKey} · ${pointed.distance.toFixed(1)} m`
}

function resize(): void {
  renderer.resize(worldHost.clientWidth, worldHost.clientHeight)
}

function input(): CameraInput {
  return {
    w: keys.has('KeyW'),
    a: keys.has('KeyA'),
    s: keys.has('KeyS'),
    d: keys.has('KeyD'),
    space: keys.has('Space'),
    ctrl: keys.has('ControlLeft') || keys.has('ControlRight'),
    shift: keys.has('ShiftLeft') || keys.has('ShiftRight'),
  }
}

function animate(now: number): void {
  if (disposed || camera === null || writer === null) return
  const timing = frameTiming(now, previousFrame)
  previousFrame = now
  camera = stepCamera(camera, input(), timing.movementSeconds)
  const display = displayCameraPose(camera)
  renderer.setCamera(display)
  const rendered = renderer.render(now)
  writer.camera(freePoseForPersistence(camera))
  for (const [treeId, finish] of activeTweens) {
    if (finish <= now) activeTweens.delete(treeId)
  }
  if (camera.mode === 'free' && document.pointerLockElement === renderer.canvas) {
    mirrorPoint(renderer.pointAt(0, 0, INTERACTION_REACH, null))
  } else if (camera.mode === 'free') {
    mirrorPoint(null)
  }
  const settled = telemetry.record({
    frameMs: timing.sampleMs,
    pending: rendered.pending,
    buildMs: rendered.buildMs,
    operations: rendered.representationOperations,
  })
  root.dataset['activeTweenCount'] = String(activeTweens.size)
  root.dataset['representedCount'] = String(rendered.representedEntities)
  root.dataset['residentCount'] = String(rendered.resident)
  root.dataset['fullCount'] = String(rendered.full)
  root.dataset['reducedCount'] = String(rendered.reduced)
  root.dataset['markerCount'] = String(rendered.marker)
  root.dataset['culledCount'] = String(rendered.culled)
  root.dataset['pendingRepresentationCount'] = String(rendered.pending)
  root.dataset['settledFrameSamples'] = String(settled.sampleCount)
  root.dataset['settledGeneration'] = String(settled.settledGeneration)
  if (rendered.error !== null) setError(`Renderer: ${rendered.error}`)
  mirrorCamera()
  animationFrame = requestAnimationFrame(animate)
}

function startWorld(world: GameWorld): void {
  const nextSession = gameSession(world)
  const nextCamera: CameraState = { mode: 'free', pose: world.camera }
  const nextWriter = new SaveWriter(world.slot.id, saveClient)
  let releaseWriterStatus = (): void => {}
  let requestedFrame: number | null = null

  try {
    renderer.setTrees([...world.trees.values()])
    resize()
    renderer.setCamera(displayCameraPose(nextCamera))
    session = nextSession
    camera = nextCamera
    writer = nextWriter
    releaseWriterStatus = nextWriter.subscribe((status) => {
      saveStatus.textContent = status.state === 'idle'
        ? 'Saved'
        : status.state === 'saving' ? 'Saving…' : `Save error: ${status.message ?? 'unknown error'}`
      saveStatus.classList.toggle('error', status.state === 'error')
      saveRetry.hidden = status.state !== 'error'
      root.dataset['saveState'] = status.state
      if (status.state === 'error') setError(saveStatus.textContent)
    })
    start.hidden = true
    hud.hidden = false
    worldName.textContent = world.slot.name
    root.dataset['ready'] = 'true'
    root.dataset['loadedSlotId'] = world.slot.id
    root.dataset['changedTreeId'] = ''
    root.dataset['activeTweenCount'] = '0'
    mirrorCamera()
    previousFrame = performance.now()
    telemetry.beginTransition()
    requestedFrame = requestAnimationFrame(animate)
    animationFrame = requestedFrame
    resume.hidden = document.pointerLockElement === renderer.canvas
  } catch (error) {
    if (requestedFrame !== null) cancelAnimationFrame(requestedFrame)
    releaseWriterStatus()
    void nextWriter.dispose().catch(() => {})
    if (session === nextSession) session = null
    if (camera === nextCamera) camera = null
    if (writer === nextWriter) writer = null
    start.hidden = false
    hud.hidden = true
    root.dataset['ready'] = 'false'
    root.dataset['loadedSlotId'] = ''
    try {
      renderer.setTrees([])
    } catch {
      // Preserve the opening failure as the concrete menu error.
    }
    throw error
  }
}

function showStartFailure(failure: StartFailure): void {
  const concrete = failure.kind === 'pointer-lock'
    ? `Could not capture mouse: ${failure.message}`
    : `Could not open orchard: ${failure.message}`
  menuError.textContent = concrete
  root.dataset['errors'] = concrete
}

const startLifecycle = new StartLifecycle(pointerLock, {
  open: startWorld,
  fail: showStartFailure,
})
startLifecycle.registerControl(nameInput)
for (const button of createForm.querySelectorAll<HTMLButtonElement>('button')) {
  startLifecycle.registerControl(button)
}

function applyDoubleCut(pointed: PointedTreePart | null, now: number): void {
  if (session === null || writer === null || camera === null) return
  if (pointed === null) {
    setError('Double cut requires an ordinary branch within reach.')
    return
  }
  const cameraBefore = camera
  try {
    const mutation = useDoubleCut(session, pointed, now, {
      beginTreeTween: (treeId, before, after, startedAt) => {
        renderer.beginTreeTween(treeId, before, after, startedAt)
        activeTweens.set(treeId, startedAt + TREE_TWEEN_MS)
      },
      persistTree: (update) => writer!.tree(update),
    })
    if (camera !== cameraBefore) throw new Error('tool use changed camera state')
    root.dataset['changedTreeId'] = mutation.treeId
    setError('')
    feedback.textContent = `Double cut applied to ${mutation.treeId}.`
  } catch (error) {
    setError(`Double cut failed: ${message(error)}`)
  }
}

createForm.addEventListener('submit', (event) => {
  event.preventDefault()
  if (startLifecycle.busy || session !== null) return
  const displayName = nameInput.value.trim()
  if (displayName.length === 0) {
    menuError.textContent = 'Enter a name for the new orchard.'
    return
  }
  clearError()
  void startLifecycle.start(() => saveClient
    .create(displayName, initialCameraRecord, [initialTree])
    .then((created) => saveClient.load(created.slotId)))
})

renderer.canvas.addEventListener('click', () => {
  if (camera === null || camera.mode !== 'free') return
  if (document.pointerLockElement !== renderer.canvas) {
    requestPlayPointerLock()
    return
  }
  const pointedPart = renderer.pointAt(0, 0, INTERACTION_REACH, null)
  if (pointedPart === null || session === null) return
  const tree = session.world.trees.get(pointedPart.treeId)
  if (tree === undefined) return
  camera = enterOrbit(camera, tree.id, worldBounds(tree))
  pointerLock.release()
  mirrorCamera()
  mirrorPoint(pointedPart)
})

renderer.canvas.addEventListener('contextmenu', (event) => {
  event.preventDefault()
  if (camera === null) return
  if (camera.mode === 'free' && document.pointerLockElement !== renderer.canvas) {
    setError('Click to resume flight before using double cut.')
    return
  }
  const [x, y] = camera.mode === 'free' ? [0, 0] : pointerNdc(event, renderer.canvas)
  const orbitTarget = camera.mode === 'orbit' ? camera.orbitTarget : null
  applyDoubleCut(renderer.pointAt(x, y, INTERACTION_REACH, orbitTarget), performance.now())
})

renderer.canvas.addEventListener('mousemove', (event) => {
  if (camera === null) return
  if (camera.mode === 'free') {
    if (document.pointerLockElement === renderer.canvas) {
      camera = lookCamera(camera, { x: event.movementX, y: event.movementY })
    }
    return
  }
  const [x, y] = pointerNdc(event, renderer.canvas)
  mirrorPoint(renderer.pointAt(x, y, INTERACTION_REACH, camera.orbitTarget))
})

window.addEventListener('keydown', (event) => {
  if (camera === null) return
  if (event.code === 'Escape' && camera.mode === 'orbit') {
    event.preventDefault()
    camera = exitOrbit(camera)
    mirrorPoint(null)
    mirrorCamera()
    requestPlayPointerLock()
    return
  }
  if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'Space', 'ControlLeft', 'ControlRight', 'ShiftLeft', 'ShiftRight'].includes(event.code)) {
    event.preventDefault()
    keys.add(event.code)
  }
})

window.addEventListener('keyup', (event) => keys.delete(event.code))
window.addEventListener('blur', () => keys.clear())
document.addEventListener('pointerlockchange', () => {
  const locked = document.pointerLockElement === renderer.canvas
  root.dataset['pointerLock'] = locked ? 'locked' : 'free'
  resume.hidden = camera === null || camera.mode !== 'free' || locked
})
resume.addEventListener('click', requestPlayPointerLock)
saveRetry.addEventListener('click', () => writer?.retry())

const resizeObserver = new ResizeObserver(resize)
resizeObserver.observe(worldHost)
resize()

window.addEventListener('pagehide', () => {
  if (disposed) return
  disposed = true
  resumePointerLock.dispose()
  startLifecycle.dispose()
  pointerLock.dispose()
  cancelAnimationFrame(animationFrame)
  resizeObserver.disconnect()
  keys.clear()
  void writer?.dispose().catch((error: unknown) => setError(`Save shutdown failed: ${message(error)}`))
  renderer.dispose()
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
