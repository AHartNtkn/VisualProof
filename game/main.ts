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
import {
  openingOrderCatalog,
} from '../src/game/orders/catalog'
import { potPlacementAhead } from '../src/game/orders/placement'
import {
  orderSession,
  publishOrderMutation,
  type OrderMutation,
  type OrderSession,
} from '../src/game/orders/session'
import { SettledFrameTelemetry, frameTiming, percentile } from '../src/game/render/frame'
import { mountGameWorld, type GameWorldRenderer } from '../src/game/render/world'
import { initialOrderCreateState, saveClient, treeUpdateFromGameTree, type CameraRecord, type SlotListEntry, type TreeUpdate } from '../src/game/save-client'
import { SaveWriter } from '../src/game/save-writer'
import { gameSession, publishTreeChange, ToolError, type GameSession, type TreeChange } from '../src/game/session'
import { StartLifecycle, type StartFailure } from '../src/game/start-lifecycle'
import { completeBranchCutting, TOOL_CATALOG, ToolInventory } from '../src/game/tools'
import {
  mountCatalog,
  renderEquippedItem,
  type CatalogController,
  type CatalogView,
} from './catalog'
import {
  applyStationaryPointerRelease,
  attachWorldInput,
  requestWorldEngagement,
  type WorldInput,
} from './input'
import { mountPauseMenu, type PauseMenuController } from './pause'
import { quitApplication } from './quit'

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
const catalogRoot = document.querySelector<HTMLElement>('[data-catalog]')!
const pauseRoot = document.querySelector<HTMLElement>('[data-pause]')!

const blankDiagram = new DiagramBuilder().build()
const blankDiagramJson = JSON.stringify(diagramToJson(blankDiagram))
const initialCameraRecord: CameraRecord = { x: 0, y: 1.7, z: 8, yaw: 0, pitch: -0.18 }
const initialTree: TreeUpdate = { treeId: 'tree-0000', diagramJson: blankDiagramJson, x: 0, z: 0, yaw: 0 }
const POT_SPAWN_DISTANCE = 6
const NEUTRAL_MOTION: CameraMotion = {
  forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
}
const slotControlReleases: Array<() => void> = []
const telemetry = new SettledFrameTelemetry(60)
let maxRepresentationOperations = 0
let camera: CameraState | null = null
let input: WorldInput | null = null
let session: GameSession | null = null
let orders: OrderSession | null = null
let tools: ToolInventory | null = null
let writer: SaveWriter | null = null
let renderer: GameWorldRenderer | null = null
let catalog: CatalogController | null = null
let catalogView: CatalogView | null = null
let pauseMenu: PauseMenuController | null = null
let animationFrame = 0
let previousFrame = performance.now()
let disposed = false
let freeActive = false
let paused = false
let releaseWriterStatus = (): void => {}

function authoredGoalForOrder(orderId: string) {
  return openingOrderCatalog.definition(orderId)?.goal
}

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

function setFeedback(value: string): void {
  setError('')
  feedback.textContent = value
}

function mirrorToolInventory(activeTools: ToolInventory | null = tools): void {
  if (activeTools === null) return
  const cuttingHeld = activeTools.cutting !== null
  const selected = activeTools.selected('1')
  renderEquippedItem(hud, selected, cuttingHeld)
  root.dataset['equippedItem'] = selected
  root.dataset['cuttingHeld'] = String(cuttingHeld)
}

function mirrorOrderProgress(activeOrders: OrderSession | null = orders): void {
  if (activeOrders === null) return
  root.dataset['reputation'] = String(activeOrders.progress.reputation)
  const openingOrderId = openingOrderCatalog.current.definitions[0]?.id
  root.dataset['orderState'] = openingOrderId === undefined
    ? ''
    : activeOrders.progress.orders.get(openingOrderId)?.kind ?? ''
}

function mirrorCatalog(): void {
  root.dataset['catalogOpen'] = String(!catalogRoot.hidden)
}

function refreshVisibleCatalog(): void {
  const activeCatalog = catalog
  const activeOrders = orders
  const view = catalogView
  if (activeCatalog === null || activeOrders === null || view === null || catalogRoot.hidden) return
  activeCatalog.show(activeOrders.progress, view)
}

function acceptOrderWrite(activeWriter: SaveWriter, mutation: OrderMutation): void {
  switch (mutation.kind) {
    case 'accept': activeWriter.acceptOrder(mutation.orderId, mutation.pot); break
    case 'abandon': activeWriter.abandonOrder(mutation.orderId); break
    case 'complete': activeWriter.completeOrder(mutation.orderId, mutation.reward); break
  }
}

function closeCatalog(requestEngagement: boolean): void {
  catalog?.hide()
  catalogView = null
  mirrorCatalog()
  input?.resume()
  if (!requestEngagement || input === null) return
  void input.engage().catch(() => {
    freeActive = false
    mirrorControls()
  })
}

function acceptCatalogOrder(orderId: string, view: CatalogView): void {
  const activeOrders = orders
  const activeWriter = writer
  const activeRenderer = renderer
  if (activeOrders === null || activeWriter === null || activeRenderer === null) return
  try {
    const mutation = activeOrders.planAccept(orderId, potPlacementAhead(view, POT_SPAWN_DISTANCE))
    publishOrderMutation(
      activeOrders,
      mutation,
      activeRenderer,
      (accepted) => acceptOrderWrite(activeWriter, accepted),
    )
    mirrorOrderProgress(activeOrders)
    refreshVisibleCatalog()
    setFeedback(`Accepted ${orderId}.`)
    closeCatalog(true)
  } catch (error) {
    setError(`Order acceptance failed: ${message(error)}`)
  }
}

function abandonCatalogOrder(orderId: string): void {
  const activeOrders = orders
  const activeWriter = writer
  const activeRenderer = renderer
  if (activeOrders === null || activeWriter === null || activeRenderer === null) return
  try {
    const mutation = activeOrders.planAbandon(orderId)
    publishOrderMutation(
      activeOrders,
      mutation,
      activeRenderer,
      (accepted) => acceptOrderWrite(activeWriter, accepted),
    )
    mirrorOrderProgress(activeOrders)
    refreshVisibleCatalog()
    setFeedback(`Abandoned ${orderId}.`)
    closeCatalog(true)
  } catch (error) {
    setError(`Order abandonment failed: ${message(error)}`)
  }
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
  root.dataset['cameraMode'] = camera.mode
  root.dataset['inputEngaged'] = String(freeActive)
  root.dataset['orbitTarget'] = camera.mode === 'orbit' ? camera.treeId : ''
  root.dataset['displayedEye'] = JSON.stringify(display.eye)
  root.dataset['displayedDirection'] = JSON.stringify(display.forward)
  root.dataset['paused'] = String(paused)
  reticle.hidden = paused || camera.mode !== 'free' || !freeActive
  engage.hidden = paused || camera.mode !== 'free' || freeActive
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
    || paused
    || currentCamera === null
    || activeInput === null
    || activeWriter === null
    || activeRenderer === null
  ) return
  const timing = frameTiming(now, previousFrame)
  previousFrame = now
  const sampledMotion = activeInput.sample()
  const motion = currentCamera.mode === 'free' && !freeActive
    ? NEUTRAL_MOTION
    : sampledMotion
  const nextCamera = advanceCamera(currentCamera, motion, timing.movementSeconds, now)
  camera = nextCamera
  activeRenderer.setCamera(displayCameraPose(nextCamera, now))
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

function openPause(): void {
  if (paused || camera === null || input === null || pauseMenu === null) return
  paused = true
  freeActive = false
  input.suspend()
  cancelAnimationFrame(animationFrame)
  animationFrame = 0
  pauseMenu.show(worldName.textContent ?? 'Orchard')
  mirrorControls()
}

function resumePause(): void {
  const activeInput = input
  const activeCamera = camera
  if (!paused || activeInput === null || activeCamera === null) return
  pauseMenu?.hide()
  paused = false
  activeInput.resume()
  previousFrame = performance.now()
  animationFrame = requestAnimationFrame(animate)
  if (activeCamera.mode === 'free') {
    void activeInput.engage().catch(() => {
      freeActive = false
      mirrorControls()
    })
  }
  mirrorControls()
}

async function refreshSlots(): Promise<void> {
  slotLoading.textContent = 'Reading save slots…'
  slotLoading.hidden = false
  try {
    const slots = await saveClient.list()
    if (disposed) return
    slotLoading.hidden = true
    renderSlots(slots)
  } catch (error) {
    if (disposed) return
    slotLoading.textContent = `Could not list saves: ${message(error)}`
    menuError.textContent = slotLoading.textContent
    root.dataset['errors'] = slotLoading.textContent
  }
}

async function returnToMainMenu(): Promise<void> {
  const activeWriter = writer
  if (!paused || activeWriter === null) return
  await activeWriter.dispose()
  cancelAnimationFrame(animationFrame)
  animationFrame = 0
  releaseWriterStatus()
  releaseWriterStatus = (): void => {}
  input?.dispose()
  catalog?.dispose()
  renderer?.dispose()
  input = null
  catalog = null
  catalogView = null
  renderer = null
  camera = null
  session = null
  orders = null
  tools = null
  writer = null
  freeActive = false
  paused = false
  pauseMenu?.hide()
  startLifecycle.returnToMenu()
  start.hidden = false
  hud.hidden = true
  root.dataset['ready'] = 'false'
  root.dataset['loadedSlot'] = ''
  root.dataset['cameraMode'] = 'menu'
  root.dataset['inputEngaged'] = 'false'
  root.dataset['orbitTarget'] = ''
  root.dataset['paused'] = 'false'
  reticle.hidden = true
  engage.hidden = true
  clearError()
  await refreshSlots()
}

async function quitFromPause(): Promise<void> {
  const activeWriter = writer
  if (!paused || activeWriter === null) return
  await activeWriter.flushChecked()
  await quitApplication()
}

function publishPlannedTreeChange(
  activeSession: GameSession,
  activeWriter: SaveWriter,
  activeRenderer: GameWorldRenderer,
  change: TreeChange,
): void {
  publishTreeChange(
    activeSession,
    change,
    activeRenderer,
    (tree) => {
      const update = treeUpdateFromGameTree(tree)
      if (change.kind === 'insert') activeWriter.insertTree(update)
      else activeWriter.tree(update)
    },
  )
}

function applySecondaryAction(clientX: number, clientY: number): void {
  const activeCamera = camera
  const activeSession = session
  const activeOrders = orders
  const activeTools = tools
  const activeWriter = writer
  const activeRenderer = renderer
  if (
    activeCamera === null
    || activeSession === null
    || activeOrders === null
    || activeTools === null
    || activeWriter === null
    || activeRenderer === null
  ) return
  if (activeCamera.mode === 'free' && !freeActive) return
  const [ndcX, ndcY] = activeCamera.mode === 'free'
    ? [0, 0]
    : pointerNdc(clientX, clientY, activeRenderer.canvas)
  const orbitTarget = activeCamera.mode === 'orbit' ? activeCamera.treeId : null
  try {
    const selected = activeTools.selected('1')
    if (selected === 'double-cut') {
      const pointed = activeRenderer.pointAtBranch(ndcX, ndcY, orbitTarget)
      if (pointed === null) throw new ToolError('Double cut requires an ordinary branch within reach.')
      const change = activeSession.planDoubleCut(pointed)
      publishPlannedTreeChange(activeSession, activeWriter, activeRenderer, change)
      setFeedback(`Double cut applied to ${change.treeId}.`)
      return
    }

    const cutting = activeTools.cutting
    if (cutting === null) {
      const pointed = activeRenderer.pointAtBranch(ndcX, ndcY, orbitTarget)
      if (pointed === null) throw new ToolError('Iteration requires a branch cutting within reach.')
      if (pointed.entity.kind !== 'branch') throw new ToolError('Iteration requires a branch cutting within reach.')
      const source = activeSession.trees.get(pointed.treeId)
      if (source === undefined) throw new ToolError(`unknown tree '${pointed.treeId}'`)
      activeTools.hold(completeBranchCutting(source, pointed.entity.region))
      mirrorToolInventory(activeTools)
      setFeedback(pointed.entity.region === source.snapshot.diagram.root
        ? `Whole-tree cutting held from ${source.id}.`
        : `Subtree cutting held from ${source.id}.`)
      return
    }

    const target = activeRenderer.pointAtToolTarget(ndcX, ndcY, orbitTarget)
    if (target === null) throw new ToolError('Iteration requires a branch, ground, or pot within reach.')
    if (target.kind === 'pot') {
      if (cutting.kind !== 'whole') throw new ToolError('delivery requires a whole tree cutting')
      const mutation = activeOrders.planDelivery(target.orderId, activeSession.propositionForDelivery(cutting))
      publishOrderMutation(
        activeOrders,
        mutation,
        activeRenderer,
        (accepted) => acceptOrderWrite(activeWriter, accepted),
      )
      activeTools.cancel()
      mirrorToolInventory(activeTools)
      mirrorOrderProgress(activeOrders)
      refreshVisibleCatalog()
      setFeedback(`Completed ${target.orderId}. Reputation ${activeOrders.progress.reputation}.`)
      return
    }

    const change = target.kind === 'branch'
      ? activeSession.planIteration(cutting, target.pointed)
      : activeSession.planDuplicate(cutting, {
          ...target.point,
          yaw: potPlacementAhead(displayCameraPose(activeCamera), 1).yaw,
        })
    publishPlannedTreeChange(activeSession, activeWriter, activeRenderer, change)
    activeTools.cancel()
    mirrorToolInventory(activeTools)
    setFeedback(target.kind === 'branch'
      ? `Iteration applied to ${change.treeId}.`
      : `Duplicated tree as ${change.treeId}.`)
  } catch (error) {
    setError(message(error))
  }
}

async function startWorld(world: GameWorld): Promise<void> {
  const nextRenderer = mountGameWorld(worldHost, [...world.trees.values()], {
    goalForOrder: authoredGoalForOrder,
  })
  const nextCamera = initialCameraState(world.camera)
  const nextSession = gameSession(world.trees)
  const nextOrders = orderSession(world.progress, openingOrderCatalog)
  const nextTools = new ToolInventory(world.progress.acquiredToolIds)
  const nextWriter = new SaveWriter(world.slot.id, saveClient)
  let nextCatalog: CatalogController | null = null
  let nextInput: WorldInput | null = null
  let nextReleaseWriterStatus = (): void => {}
  let freeSecondaryPress: { readonly x: number; readonly y: number } | null = null
  try {
    nextCatalog = mountCatalog(catalogRoot, openingOrderCatalog, {
      accept: acceptCatalogOrder,
      abandon: abandonCatalogOrder,
    })
    nextRenderer.setPots([...world.progress.orders].flatMap(([orderId, state]) => {
      if (state.kind !== 'accepted') return []
      const goal = authoredGoalForOrder(orderId)
      if (goal === undefined) throw new Error(`missing authored goal for '${orderId}'`)
      return [{ orderId, placement: state.pot, goal }]
    }))
    nextRenderer.resize(worldHost.clientWidth, worldHost.clientHeight)
    nextRenderer.setCamera(displayCameraPose(nextCamera))
    nextReleaseWriterStatus = nextWriter.subscribe((status) => {
      saveStatus.textContent = status.state === 'idle'
        ? 'Saved'
        : status.state === 'saving' ? 'Saving…' : `Save error: ${status.message ?? 'unknown error'}`
      saveStatus.classList.toggle('error', status.state === 'error')
      saveRetry.hidden = status.state !== 'error'
      root.dataset['saveState'] = status.state
      if (status.state === 'error') setError(saveStatus.textContent)
    })
    nextInput = attachWorldInput(worldHost, {
      pointerDown(button, clientX, clientY) {
        const activeCamera = camera
        const activeInput = input
        const activeRenderer = renderer
        if (activeCamera === null || activeInput === null || activeRenderer === null) return
        if (activeCamera.mode === 'orbit') {
          activeCamera.interaction.pointerDown(button, clientX, clientY)
          return
        }
        if (button === 2) {
          freeSecondaryPress = { x: clientX, y: clientY }
          return
        }
        if (button !== 0) return
        if (!freeActive) {
          void activeInput.engage().catch(() => {
            freeActive = false
            mirrorControls()
          })
          return
        }
        const target = activeRenderer.pickTree(0, 0)
        if (target === null) return
        camera = enterOrbit(activeCamera, target)
        freeActive = false
        activeInput.release()
        mirrorControls()
      },
      pointerUp(button, clientX, clientY, relativeDistance) {
        const activeCamera = camera
        const activeRenderer = renderer
        if (activeCamera === null || activeRenderer === null) return
        if (activeCamera.mode === 'free') {
          const press = freeSecondaryPress
          freeSecondaryPress = null
          if (button === 2 && press !== null) {
            applyStationaryPointerRelease(
              press,
              { x: clientX, y: clientY, relativeDistance },
              applySecondaryAction,
            )
          }
          return
        }
        const release = activeCamera.interaction.pointerUp(clientX, clientY)
        if (release === null) return
        if (release.button === 2) {
          applySecondaryAction(release.clientX, release.clientY)
          return
        }
        if (release.button !== 0) return
        const [ndcX, ndcY] = pointerNdc(
          release.clientX,
          release.clientY,
          activeRenderer.canvas,
        )
        const focus = activeRenderer.pickTreeFocus(ndcX, ndcY, activeCamera.treeId)
        if (focus !== null) activeCamera.interaction.focus(focus.worldFocus, performance.now())
      },
      pointerCancel() {
        freeSecondaryPress = null
        if (camera?.mode === 'orbit') camera.interaction.cancelPointer()
      },
      escape() {
        const activeTools = tools
        let handled = false
        let resumeEngagement = false
        if (activeTools !== null && activeTools.cutting !== null) {
          activeTools.cancel()
          mirrorToolInventory(activeTools)
          setFeedback('Cutting cleared.')
          handled = true
        }
        if (!catalogRoot.hidden) {
          closeCatalog(false)
          return 'resume-engagement'
        }
        if (camera?.mode === 'orbit') {
          camera = exitOrbit(camera)
          freeActive = false
          handled = true
          resumeEngagement = true
        }
        mirrorControls()
        if (handled) return resumeEngagement ? 'resume-engagement' : 'handled'
        openPause()
        return 'handled'
      },
      swapTool() {
        const activeTools = tools
        if (paused || activeTools === null || !catalogRoot.hidden) return
        const selected = activeTools.cycle('1').selected
        mirrorToolInventory(activeTools)
        setFeedback(`Equipped ${TOOL_CATALOG.find((tool) => tool.id === selected)!.label}.`)
      },
      toggleCatalog() {
        const activeCatalog = catalog
        const activeOrders = orders
        const activeCamera = camera
        const activeInput = input
        if (
          paused
          || activeCatalog === null
          || activeOrders === null
          || activeCamera === null
          || activeInput === null
        ) return
        if (!catalogRoot.hidden) {
          closeCatalog(true)
          return
        }
        catalogView = displayCameraPose(activeCamera)
        activeInput.suspend()
        freeActive = false
        activeCatalog.show(activeOrders.progress, catalogView)
        mirrorCatalog()
        mirrorControls()
      },
      engagementChanged(active) {
        freeActive = active
        mirrorControls()
      },
    })
    renderer = nextRenderer
    camera = nextCamera
    input = nextInput
    session = nextSession
    orders = nextOrders
    tools = nextTools
    writer = nextWriter
    releaseWriterStatus = nextReleaseWriterStatus
    catalog = nextCatalog
    catalogView = null
    nextCatalog.hide()
    start.hidden = true
    hud.hidden = false
    worldName.textContent = world.slot.name
    root.dataset['ready'] = 'true'
    root.dataset['paused'] = 'false'
    root.dataset['loadedSlot'] = world.slot.id
    maxRepresentationOperations = 0
    root.dataset['renderMode'] = 'game'
    mirrorToolInventory(nextTools)
    mirrorOrderProgress(nextOrders)
    mirrorCatalog()
    telemetry.beginTransition()
    mirrorControls()
    previousFrame = performance.now()
    animationFrame = requestAnimationFrame(animate)
  } catch (error) {
    nextCatalog?.dispose()
    nextInput?.dispose()
    nextReleaseWriterStatus()
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
  if (document.pointerLockElement === worldHost) document.exitPointerLock()
  const concrete = `Could not open orchard: ${failure.message}`
  menuError.textContent = concrete
  root.dataset['errors'] = concrete
}

const startLifecycle = new StartLifecycle({ open: startWorld, fail: showStartFailure })
startLifecycle.registerControl(nameInput)
for (const button of createForm.querySelectorAll<HTMLButtonElement>('button')) startLifecycle.registerControl(button)
pauseMenu = mountPauseMenu(pauseRoot, {
  resume: resumePause,
  mainMenu: returnToMainMenu,
  quit: quitFromPause,
})

function startOpening(operation: () => Promise<GameWorld>): void {
  void requestWorldEngagement(worldHost).catch((error: unknown) => {
    setError(`Could not begin play: ${message(error)}`)
  })
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
  const revision = openingOrderCatalog.current
  const initialOrders = initialOrderCreateState(revision)
  startOpening(() => saveClient.create({
    displayName,
    camera: initialCameraRecord,
    trees: [initialTree],
    ...initialOrders,
  }, revision).then((created) => saveClient.load(created.slotId)))
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
  catalog?.dispose()
  catalog = null
  catalogView = null
  session = null
  orders = null
  tools = null
  pauseMenu?.dispose()
  pauseMenu = null
  releaseWriterStatus()
  releaseWriterStatus = (): void => {}
  void writer?.dispose().catch((error: unknown) => setError(`Save shutdown failed: ${message(error)}`))
  renderer?.dispose()
  renderer = null
})

void refreshSlots()
