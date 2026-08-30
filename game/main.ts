import './style.css'
if (import.meta.env.VITE_WDIO === 'true') void import('@wdio/tauri-plugin')

import { DiagramBuilder, diagramToJson } from '../src/kernel/diagram'
import {
  advanceCamera,
  cameraPoseForSave,
  displayCameraPose,
  enterOrbit,
  initialCameraState,
  type CameraMotion,
  type CameraState,
} from '../src/game/camera'
import type { GameProgress, GameWorld } from '../src/game/model'
import {
  decodeOrderCatalog,
  openingOrderCatalog,
} from '../src/game/orders/catalog'
import { orderContentClient, serializeOrderCatalog } from '../src/game/orders/content-client'
import { availablePotPlacementAhead, potPlacementAhead } from '../src/game/orders/placement'
import {
  initialOrderProgress,
  orderSession,
  publishOrderMutation,
  type OrderMutation,
  type OrderSession,
} from '../src/game/orders/session'
import { SettledFrameTelemetry, frameTiming, percentile } from '../src/game/render/frame'
import { mountGameWorld, type GameWorldRenderer } from '../src/game/render/world'
import { orderRecordsFromProgress, saveClient, treeUpdateFromGameTree, type CameraRecord, type SlotListEntry, type TreeUpdate } from '../src/game/save-client'
import { SaveWriter } from '../src/game/save-writer'
import { gameSession, publishTreeChange, ToolError, type GameSession, type TreeChange } from '../src/game/session'
import { StartLifecycle, type StartFailure } from '../src/game/start-lifecycle'
import { completeBranchCutting, TOOL_CATALOG, ToolInventory, type ToolId } from '../src/game/tools'
import { TutorialSession, type TutorialEvent } from '../src/game/tutorial'
import { openingTutorialContent } from '../src/game/tutorial/content'
import { authoredContentClient } from '../src/game/content-client'
import type { PlacementObstacle } from '../src/game/placement'
import {
  mountLedger,
  type LedgerController,
  type LedgerView,
} from './ledger'
import { mountToolSelector, renderHeldToolModel } from './tool-selector'
import {
  applyStationaryPointerRelease,
  attachWorldInput,
  requestWorldEngagement,
  type WorldInput,
} from './input'
import { mountPauseMenu, type PauseMenuController } from './pause'
import { mountOrderEditor, type OrderEditorController } from './order-editor'
import { DeveloperPreferences } from './preferences'
import { quitApplication } from './quit'
import { mountSettings, type SettingsController } from './settings'
import { mountTutorialCard, type TutorialCardController } from './tutorial-card'
import { mountTutorialEditor, type TutorialEditorController } from './tutorial-editor'
import { enqueueTutorialCommit } from './tutorial-progression'
import { WorldStateController } from './world-state'
import { commitWorldShutdown } from './world-lifecycle'
import {
  acceptedPotsForRevision,
  publishOrderCatalogRevision,
} from './order-catalog-publication'
import { publishTutorialContentRevision } from './content-publication'

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
const toolSelectorRoot = document.querySelector<HTMLElement>('[data-tool-selector]')!
const heldToolRoot = document.querySelector<HTMLElement>('[data-held-tool-model]')!
const ledgerRoot = document.querySelector<HTMLElement>('[data-ledger]')!
const pauseRoot = document.querySelector<HTMLElement>('[data-pause]')!
const settingsRoot = document.querySelector<HTMLElement>('[data-settings]')!
const tutorialCardRoot = document.querySelector<HTMLElement>('[data-tutorial-card]')!
const developerModeIndicator = document.querySelector<HTMLElement>('[data-developer-mode-indicator]')!
const orderEditorRoot = document.querySelector<HTMLElement>('[data-order-editor]')!
const tutorialEditorRoot = document.querySelector<HTMLElement>('[data-tutorial-editor]')!
const createTutorials = document.querySelector<HTMLInputElement>('[data-create-tutorials]')!

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
let tutorial: TutorialSession | null = null
let ledger: LedgerController | null = null
let ledgerView: LedgerView | null = null
let pauseMenu: PauseMenuController | null = null
let settings: SettingsController | null = null
let tutorialCard: TutorialCardController | null = null
let orderEditor: OrderEditorController | null = null
let tutorialEditor: TutorialEditorController | null = null
let worldState: WorldStateController | null = null
let animationFrame = 0
let previousFrame = performance.now()
let disposed = false
let freeActive = false
let developerMode = false
type ForegroundEditorState =
  | { readonly kind: 'closed' }
  | { readonly kind: 'order'; readonly mode: 'create' | 'edit' }
  | { readonly kind: 'tutorial' }
let editorState: ForegroundEditorState = { kind: 'closed' }
let worldGeneration = 0
let releaseWriterStatus = (): void => {}
const toolSelector = mountToolSelector(toolSelectorRoot)
const preferences = new DeveloperPreferences()

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

function mirrorRuntimeState(): void {
  const tutorialClosed = editorState.kind === 'tutorial' && tutorialEditor?.isOpen !== true
  if (
    (editorState.kind === 'order' && orderEditor?.isOpen !== true)
    || tutorialClosed
  ) editorState = { kind: 'closed' }
  if (tutorialClosed && worldState?.isPaused === false && ledger?.isOpen !== true) input?.resume()
  root.dataset['tutorialsEnabled'] = String(tutorial?.enabled ?? false)
  root.dataset['completedTutorialMilestones'] = JSON.stringify(
    tutorial === null ? [] : [...tutorial.completed],
  )
  root.dataset['acquiredToolIds'] = JSON.stringify(tools?.snapshotForSave() ?? [])
  root.dataset['selectedTool'] = tools?.selected('1') ?? ''
  root.dataset['selectorVisible'] = String(toolSelectorRoot.childElementCount > 0)
  root.dataset['ledgerOpen'] = String(ledger?.isOpen ?? false)
  root.dataset['ledgerTab'] = ledger?.selectedPrimaryTab ?? 'tools'
  root.dataset['developerMode'] = String(developerMode)
  root.dataset['editorState'] = editorState.kind === 'order' ? editorState.mode : editorState.kind
  developerModeIndicator.hidden = !developerMode
}

function renderTutorial(): void {
  if (tutorial === null || tutorialCard === null) return
  tutorialCard.render(tutorial.currentInstruction, tutorial.enabled, developerMode)
  mirrorRuntimeState()
}

function observeTutorial(event: TutorialEvent): void {
  const activeTutorial = tutorial
  const activeWriter = writer
  const activeCard = tutorialCard
  if (activeTutorial === null || activeWriter === null || activeCard === null) return
  const commit = activeTutorial.observe(event)
  enqueueTutorialCommit(activeWriter, commit)
  activeCard.render(commit.instruction, activeTutorial.enabled, developerMode)
  mirrorRuntimeState()
  refreshVisibleLedger()
}

function mirrorToolInventory(activeTools: ToolInventory | null = tools): void {
  if (activeTools === null) return
  const cuttingHeld = activeTools.cutting !== null
  const selected = activeTools.selected('1')
  renderHeldToolModel(heldToolRoot, selected, cuttingHeld)
  heldToolRoot.hidden = false
  toolSelector.render(activeTools, performance.now())
  root.dataset['equippedItem'] = selected
  root.dataset['cuttingHeld'] = String(cuttingHeld)
  mirrorRuntimeState()
}

function mirrorOrderProgress(activeOrders: OrderSession | null = orders): void {
  if (activeOrders === null) return
  root.dataset['reputation'] = String(activeOrders.progress.reputation)
  const openingOrderId = openingOrderCatalog.current.definitions[0]?.id
  root.dataset['orderState'] = openingOrderId === undefined
    ? ''
    : activeOrders.progress.orders.get(openingOrderId)?.kind ?? ''
}

function mirrorLedger(): void {
  mirrorRuntimeState()
}

function currentLedgerProgress(
  activeOrders: OrderSession,
  activeTools: ToolInventory,
  activeTutorial: TutorialSession,
): GameProgress {
  return {
    ...activeOrders.progress,
    tutorialsEnabled: activeTutorial.enabled,
    completedTutorialMilestones: activeTutorial.completed,
    acquiredToolIds: new Set(activeTools.snapshotForSave()),
  }
}

function deletionRevision(orderId: string) {
  return decodeOrderCatalog(
    serializeOrderCatalog(openingOrderCatalog.current).filter((definition) => definition.id !== orderId),
  )
}

function refreshVisibleLedger(): void {
  const activeLedger = ledger
  const activeOrders = orders
  const activeTools = tools
  const activeTutorial = tutorial
  const view = ledgerView
  if (
    activeLedger === null
    || activeOrders === null
    || activeTools === null
    || activeTutorial === null
    || view === null
    || !activeLedger.isOpen
  ) return
  activeLedger.show({
    catalog: openingOrderCatalog.current,
    progress: currentLedgerProgress(activeOrders, activeTools, activeTutorial),
    tools: activeTools,
    tutorialCheck: (milestone) => activeTutorial.check(milestone),
    developerMode,
    view,
  })
}

function acceptOrderWrite(activeWriter: SaveWriter, mutation: OrderMutation): void {
  switch (mutation.kind) {
    case 'accept': activeWriter.acceptOrder(mutation.orderId, mutation.pot); break
    case 'abandon': activeWriter.abandonOrder(mutation.orderId); break
    case 'complete': activeWriter.completeOrder(mutation.orderId, mutation.reward); break
  }
}

function closeLedger(requestEngagement: boolean): void {
  ledger?.hide()
  ledgerView = null
  mirrorLedger()
  input?.resume()
  if (!requestEngagement || input === null || camera?.mode !== 'free') return
  void input.engage().catch(() => {
    freeActive = false
    mirrorControls()
  })
}

function acquireLedgerTool(toolId: ToolId): void {
  const activeTools = tools
  const activeOrders = orders
  const activeWriter = writer
  if (activeTools === null || activeOrders === null || activeWriter === null) return
  try {
    activeTools.acquire(toolId, activeOrders.progress.reputation)
    activeWriter.acquireTool(toolId)
    mirrorToolInventory(activeTools)
    refreshVisibleLedger()
    observeTutorial({ kind: 'tool-acquired', toolId })
    setFeedback(`Acquired ${TOOL_CATALOG.find((tool) => tool.id === toolId)!.label}.`)
  } catch (error) {
    setError(`Tool acquisition failed: ${message(error)}`)
  }
}

function acceptLedgerOrder(orderId: string, view: LedgerView): void {
  const activeOrders = orders
  const activeWriter = writer
  const activeRenderer = renderer
  if (activeOrders === null || activeWriter === null || activeRenderer === null) return
  try {
    const occupiedPots = [...activeOrders.progress.orders.values()].flatMap((state) =>
      state.kind === 'accepted' ? [state.pot] : [])
    const mutation = activeOrders.planAccept(orderId, availablePotPlacementAhead(
      view,
      POT_SPAWN_DISTANCE,
      occupiedPots,
    ))
    publishOrderMutation(
      activeOrders,
      mutation,
      activeRenderer,
      (accepted) => acceptOrderWrite(activeWriter, accepted),
    )
    mirrorOrderProgress(activeOrders)
    refreshVisibleLedger()
    setFeedback(`Accepted ${orderId}.`)
    closeLedger(true)
  } catch (error) {
    setError(`Order acceptance failed: ${message(error)}`)
  }
}

function abandonLedgerOrder(orderId: string): void {
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
    refreshVisibleLedger()
    setFeedback(`Abandoned ${orderId}.`)
    closeLedger(true)
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
  const paused = worldState?.isPaused ?? false
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
    || worldState?.isPaused === true
    || currentCamera === null
    || activeInput === null
    || activeWriter === null
    || activeRenderer === null
  ) return
  const timing = frameTiming(now, previousFrame)
  previousFrame = now
  if (tools !== null) toolSelector.render(tools, now)
  const sampledMotion = activeInput.sample()
  const motion = currentCamera.mode === 'free' && !freeActive
    ? NEUTRAL_MOTION
    : sampledMotion
  const nextCamera = advanceCamera(currentCamera, motion, timing.movementSeconds, now)
  camera = nextCamera
  if (currentCamera.mode === 'orbit') {
    if (motion.forward !== 0 || motion.strafe !== 0 || motion.vertical !== 0) {
      observeTutorial({ kind: 'orbit-moved' })
    }
  } else {
    if (motion.forward !== 0 || motion.strafe !== 0) {
      observeTutorial({ kind: 'camera-capability', capability: 'move' })
    }
    if (motion.lookX !== 0 || motion.lookY !== 0) {
      observeTutorial({ kind: 'camera-capability', capability: 'look' })
    }
    if (motion.vertical > 0) observeTutorial({ kind: 'camera-capability', capability: 'ascend' })
    if (motion.vertical < 0) observeTutorial({ kind: 'camera-capability', capability: 'descend' })
    if (motion.sprint && (motion.forward !== 0 || motion.strafe !== 0 || motion.vertical !== 0)) {
      observeTutorial({ kind: 'camera-capability', capability: 'sprint' })
    }
  }
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
  mirrorRuntimeState()
  animationFrame = requestAnimationFrame(animate)
}

function openPause(): void {
  const activeWorldState = worldState
  if (activeWorldState === null || !activeWorldState.pause()) return
  cancelAnimationFrame(animationFrame)
  animationFrame = 0
}

function resumePause(): void {
  const activeWorldState = worldState
  if (activeWorldState === null || !activeWorldState.resume()) return
  previousFrame = performance.now()
  animationFrame = requestAnimationFrame(animate)
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
  if (worldState?.isPaused !== true || activeWriter === null) return
  await commitWorldShutdown(
    () => activeWriter.dispose(),
    () => { worldGeneration += 1 },
  )
  cancelAnimationFrame(animationFrame)
  animationFrame = 0
  releaseWriterStatus()
  releaseWriterStatus = (): void => {}
  input?.dispose()
  ledger?.dispose()
  orderEditor?.dispose()
  tutorialEditor?.dispose()
  renderer?.dispose()
  input = null
  ledger = null
  orderEditor = null
  tutorialEditor = null
  ledgerView = null
  renderer = null
  camera = null
  session = null
  orders = null
  tools = null
  tutorial = null
  writer = null
  worldState = null
  freeActive = false
  developerMode = false
  pauseMenu?.hide()
  settings?.hide()
  tutorialCard?.render(null, false, false)
  startLifecycle.returnToMenu()
  start.hidden = false
  hud.hidden = true
  heldToolRoot.hidden = true
  toolSelector.clear()
  root.dataset['ready'] = 'false'
  root.dataset['loadedSlot'] = ''
  root.dataset['cameraMode'] = 'menu'
  root.dataset['inputEngaged'] = 'false'
  root.dataset['orbitTarget'] = ''
  root.dataset['paused'] = 'false'
  reticle.hidden = true
  engage.hidden = true
  mirrorRuntimeState()
  clearError()
  await refreshSlots()
}

async function quitFromPause(): Promise<void> {
  const activeWriter = writer
  if (worldState?.isPaused !== true || activeWriter === null) return
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

function sproutPlacementObstacles(
  activeSession: GameSession,
  activeOrders: OrderSession,
): readonly PlacementObstacle[] {
  return [
    ...[...activeSession.trees.values()].map((tree) => ({
      kind: 'tree' as const,
      id: tree.id,
      x: tree.placement.x,
      z: tree.placement.z,
    })),
    ...[...activeOrders.progress.orders].flatMap(([id, state]) => state.kind === 'accepted'
      ? [{ kind: 'pot' as const, id, x: state.pot.x, z: state.pot.z }]
      : []),
  ]
}

function unreachableTool(tool: never): never {
  throw new Error(`unsupported tool '${tool}'`)
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
    switch (selected) {
      case 'sprout-spawner': {
        const target = activeRenderer.pointAtToolTarget(ndcX, ndcY, orbitTarget)
        if (target?.kind !== 'ground') {
          throw new ToolError('Sprout Spawner requires clear ground within reach.')
        }
        const change = activeSession.planSpawnSprout({
          ...target.point,
          yaw: potPlacementAhead(displayCameraPose(activeCamera), 1).yaw,
        }, sproutPlacementObstacles(activeSession, activeOrders))
        publishPlannedTreeChange(activeSession, activeWriter, activeRenderer, change)
        const blankTreeCount = [...activeSession.trees.values()]
          .filter(({ snapshot }) => snapshot.json === blankDiagramJson).length
        observeTutorial({ kind: 'sprout-spawned', blankTreeCount })
        setFeedback(`Planted sprout ${change.treeId}.`)
        return
      }
      case 'double-cut': {
        const pointed = activeRenderer.pointAtBranch(ndcX, ndcY, orbitTarget)
        if (pointed === null) throw new ToolError('Double cut requires an ordinary branch within reach.')
        const change = activeSession.planDoubleCut(pointed)
        publishPlannedTreeChange(activeSession, activeWriter, activeRenderer, change)
        observeTutorial({ kind: 'double-cut-applied' })
        setFeedback(`Double cut applied to ${change.treeId}.`)
        return
      }
      case 'iteration': {
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
          refreshVisibleLedger()
          observeTutorial({ kind: 'order-completed', orderId: target.orderId })
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
        if (target.kind === 'ground' && change.after.snapshot.json !== blankDiagramJson) {
          observeTutorial({ kind: 'nonblank-tree-duplicated' })
        }
        setFeedback(target.kind === 'branch'
          ? `Iteration applied to ${change.treeId}.`
          : `Duplicated tree as ${change.treeId}.`)
        return
      }
      default: return unreachableTool(selected)
    }
  } catch (error) {
    setError(message(error))
  }
}

async function startWorld(world: GameWorld): Promise<void> {
  const generation = ++worldGeneration
  const nextRenderer = mountGameWorld(worldHost, [...world.trees.values()], {
    goalForOrder: authoredGoalForOrder,
  })
  const nextCamera = initialCameraState(world.camera)
  const nextSession = gameSession(world.trees)
  const nextOrders = orderSession(world.progress, openingOrderCatalog)
  const nextTools = new ToolInventory(world.progress.acquiredToolIds)
  const nextTutorial = new TutorialSession(
    world.progress.tutorialsEnabled,
    world.progress.completedTutorialMilestones,
  )
  const nextWriter = new SaveWriter(world.slot.id, saveClient)
  const reconstructedTutorial = nextTutorial.reconcileDurableProgress(world.progress)
  enqueueTutorialCommit(nextWriter, reconstructedTutorial)
  let nextLedger: LedgerController | null = null
  let nextEditor: OrderEditorController | null = null
  let nextTutorialEditor: TutorialEditorController | null = null
  let nextInput: WorldInput | null = null
  let nextReleaseWriterStatus = (): void => {}
  let freeSecondaryPress: { readonly x: number; readonly y: number } | null = null
  try {
    const publishCatalog = async (
      candidate: Parameters<typeof openingOrderCatalog.publish>[0],
    ): Promise<void> => {
      await publishOrderCatalogRevision({
        slotId: world.slot.id,
        candidate,
        writer: nextWriter,
        contentClient: orderContentClient,
        catalog: openingOrderCatalog,
        orders: nextOrders,
        renderer: nextRenderer,
        isCurrent: () => generation === worldGeneration
          && orders === nextOrders
          && writer === nextWriter
          && renderer === nextRenderer,
      })
      mirrorOrderProgress(nextOrders)
      refreshVisibleLedger()
      mirrorRuntimeState()
    }
    nextLedger = mountLedger(ledgerRoot, {
      acquireTool: acquireLedgerTool,
      acceptOrder: acceptLedgerOrder,
      abandonOrder: abandonLedgerOrder,
      editOrder: (orderId) => {
        if (!developerMode || editorState.kind !== 'closed') return
        const definition = openingOrderCatalog.definition(orderId)
        if (definition === undefined) {
          setError(`Order editing failed: unknown order '${orderId}'.`)
          return
        }
        editorState = { kind: 'order', mode: 'edit' }
        orderEditor?.edit(definition)
        mirrorRuntimeState()
      },
      createOrder: () => {
        if (!developerMode || editorState.kind !== 'closed') return
        editorState = { kind: 'order', mode: 'create' }
        orderEditor?.create()
        mirrorRuntimeState()
      },
    })
    nextEditor = mountOrderEditor(orderEditorRoot, {
      currentRevision: () => openingOrderCatalog.current,
      isForeground: () => worldState?.isPaused === false,
      save: publishCatalog,
      delete: (orderId) => publishCatalog(deletionRevision(orderId)),
    })
    nextTutorialEditor = mountTutorialEditor(tutorialEditorRoot, {
      currentRevision: () => openingTutorialContent.current,
      isForeground: () => worldState?.isPaused === false && editorState.kind === 'tutorial',
      save: async (candidate) => {
        await publishTutorialContentRevision({
          candidate,
          contentClient: authoredContentClient,
          content: openingTutorialContent,
          isCurrent: () => generation === worldGeneration && tutorial === nextTutorial,
        })
        if (generation !== worldGeneration || tutorial !== nextTutorial) return
        renderTutorial()
      },
    })
    nextRenderer.setPots(acceptedPotsForRevision(
      nextOrders.progress,
      openingOrderCatalog.current,
    ))
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
        observeTutorial({ kind: 'tree-selected' })
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
      stepBack: () => {
        const result = worldState?.stepBack()
        if (result === 'orbit-exited') observeTutorial({ kind: 'orbit-exited' })
        mirrorRuntimeState()
      },
      pause: openPause,
      category(code) {
        const activeTools = tools
        if (
          code !== '1'
          || worldState?.isPaused === true
          || activeTools === null
          || ledger?.isOpen === true
          || editorState.kind !== 'closed'
        ) return
        activeTools.cycle('1', performance.now())
        mirrorToolInventory(activeTools)
      },
      toggleLedger() {
        const activeLedger = ledger
        const activeOrders = orders
        const activeTools = tools
        const activeTutorial = tutorial
        const activeCamera = camera
        const activeInput = input
        if (
          worldState?.isPaused === true
          || activeLedger === null
          || activeOrders === null
          || activeTools === null
          || activeTutorial === null
          || activeCamera === null
          || activeInput === null
          || editorState.kind !== 'closed'
        ) return
        if (activeLedger.isOpen) {
          closeLedger(true)
          return
        }
        ledgerView = displayCameraPose(activeCamera)
        activeInput.suspend()
        freeActive = false
        const explainsDoubleCut = activeTutorial.completed.has('apply-double-cut')
          && !activeTutorial.completed.has('double-cut-explained')
        activeLedger.show({
          catalog: openingOrderCatalog.current,
          progress: currentLedgerProgress(activeOrders, activeTools, activeTutorial),
          tools: activeTools,
          tutorialCheck: (milestone) => activeTutorial.check(milestone),
          developerMode,
          view: ledgerView,
        })
        mirrorLedger()
        mirrorControls()
        if (explainsDoubleCut) observeTutorial({ kind: 'ledger-opened' })
      },
      toggleDeveloperMode() {
        if (
          worldState?.isPaused === true
          || !preferences.developerToolsEnabled
          || editorState.kind !== 'closed'
        ) return
        developerMode = !developerMode
        if (developerMode) worldState?.releasePointerForDeveloperMode()
        else {
          orderEditor?.hide()
          tutorialEditor?.hide()
        }
        renderTutorial()
        refreshVisibleLedger()
        mirrorRuntimeState()
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
    tutorial = nextTutorial
    writer = nextWriter
    releaseWriterStatus = nextReleaseWriterStatus
    ledger = nextLedger
    orderEditor = nextEditor
    tutorialEditor = nextTutorialEditor
    editorState = { kind: 'closed' }
    ledgerView = null
    const activePauseMenu = pauseMenu
    if (activePauseMenu === null) throw new Error('pause menu is unavailable')
    worldState = new WorldStateController({
      getCamera: () => camera ?? nextCamera,
      setCamera: (next) => { camera = next },
      tools: nextTools,
      ledger: nextLedger,
      foreground: { get isOpen() { return editorState.kind !== 'closed' } },
      input: nextInput,
      pauseMenu: activePauseMenu,
      worldName: () => worldName.textContent ?? 'Orchard',
      setFreeActive: (active) => { freeActive = active },
      cuttingCleared: () => {
        mirrorToolInventory(nextTools)
        setFeedback('Cutting cleared.')
      },
      stateChanged: mirrorControls,
    })
    nextLedger.hide()
    nextEditor.hide()
    nextTutorialEditor.hide()
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
    mirrorLedger()
    renderTutorial()
    mirrorRuntimeState()
    telemetry.beginTransition()
    mirrorControls()
    previousFrame = performance.now()
    animationFrame = requestAnimationFrame(animate)
  } catch (error) {
    if (worldGeneration === generation) worldGeneration += 1
    worldState = null
    nextLedger?.dispose()
    nextEditor?.dispose()
    nextTutorialEditor?.dispose()
    nextInput?.dispose()
    nextReleaseWriterStatus()
    await nextWriter.dispose().catch(() => {})
    nextRenderer.dispose()
    start.hidden = false
    hud.hidden = true
    heldToolRoot.hidden = true
    toolSelector.clear()
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

function showSettings(): void {
  if (worldState?.isPaused !== true || tutorial === null || settings === null) return
  pauseMenu?.hide()
  settings.show({
    tutorialsEnabled: tutorial.enabled,
    developerToolsEnabled: preferences.developerToolsEnabled,
  })
}

function returnToPauseFromSettings(): void {
  if (worldState?.isPaused !== true) return
  pauseMenu?.show(worldName.textContent ?? 'Orchard')
}

const startLifecycle = new StartLifecycle({ open: startWorld, fail: showStartFailure })
startLifecycle.registerControl(nameInput)
startLifecycle.registerControl(createTutorials)
for (const button of createForm.querySelectorAll<HTMLButtonElement>('button')) startLifecycle.registerControl(button)
tutorialCard = mountTutorialCard(tutorialCardRoot, {
  edit(milestoneId) {
    const activeTutorial = tutorial
    const activeEditor = tutorialEditor
    if (
      !developerMode
      || worldState?.isPaused !== false
      || activeTutorial?.currentInstruction?.milestoneId !== milestoneId
      || activeEditor === null
      || editorState.kind !== 'closed'
    ) return
    input?.suspend()
    editorState = { kind: 'tutorial' }
    activeEditor.edit(openingTutorialContent.current.definition(milestoneId))
    mirrorRuntimeState()
  },
})
settings = mountSettings(settingsRoot, {
  setTutorialsEnabled(enabled) {
    const activeTutorial = tutorial
    const activeWriter = writer
    if (activeTutorial === null || activeWriter === null) return
    try {
      activeTutorial.setEnabled(enabled)
      activeWriter.setTutorialsEnabled(enabled)
      renderTutorial()
      refreshVisibleLedger()
    } catch (error) {
      setError(`Tutorial setting failed: ${message(error)}`)
    }
  },
  setDeveloperToolsEnabled(enabled) {
    preferences.setDeveloperToolsEnabled(enabled)
    if (!enabled) {
      developerMode = false
      orderEditor?.hide()
      tutorialEditor?.hide()
      editorState = { kind: 'closed' }
    }
    renderTutorial()
    refreshVisibleLedger()
    mirrorRuntimeState()
  },
  back: returnToPauseFromSettings,
})
pauseMenu = mountPauseMenu(pauseRoot, {
  resume: resumePause,
  settings: showSettings,
  mainMenu: returnToMainMenu,
  quit: quitFromPause,
})
mirrorRuntimeState()

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
  const initialProgress = initialOrderProgress(revision.definitions)
  startOpening(() => saveClient.create({
    displayName,
    camera: initialCameraRecord,
    trees: [initialTree],
    tutorialsEnabled: createTutorials.checked,
    completedTutorialMilestones: [],
    acquiredToolIds: ['sprout-spawner'],
    reputation: initialProgress.reputation,
    orders: orderRecordsFromProgress(initialProgress, revision),
  }, revision).then((created) => saveClient.load(created.slotId)))
})
saveRetry.addEventListener('click', () => writer?.retry())

const resizeObserver = new ResizeObserver(resize)
resizeObserver.observe(worldHost)

window.addEventListener('pagehide', () => {
  if (disposed) return
  disposed = true
  worldGeneration += 1
  startLifecycle.dispose()
  cancelAnimationFrame(animationFrame)
  resizeObserver.disconnect()
  input?.dispose()
  input = null
  ledger?.dispose()
  ledger = null
  orderEditor?.dispose()
  orderEditor = null
  tutorialEditor?.dispose()
  tutorialEditor = null
  ledgerView = null
  session = null
  orders = null
  tools = null
  tutorial = null
  worldState = null
  pauseMenu?.dispose()
  pauseMenu = null
  settings?.dispose()
  settings = null
  releaseWriterStatus()
  releaseWriterStatus = (): void => {}
  void writer?.dispose().catch((error: unknown) => setError(`Save shutdown failed: ${message(error)}`))
  renderer?.dispose()
  renderer = null
})

void refreshSlots()
