import { createInitialGameState } from '../../src/game/controller-state'
import '../../app/style.css'
import { reduceGame, type GameAction } from '../../src/game/controller'
import {
  mountCursebreaker,
  type CursebreakerDebugState,
  type MountedCursebreaker,
} from '../../src/game/interface/mount'
import type { CursebreakerPlatform } from '../../src/game/platform'
import { encodeGameSave } from '../../src/game/save'
import { controllerCatalog } from './controller-fixture'
import { openingCatalog } from '../../src/game/content'
import {
  artifactRuntimeCatalog,
  editorRuntimeCatalog,
  longRuntimeCatalog,
  motionRuntimeCatalog,
} from './runtime-catalog-fixture'

const host = document.querySelector<HTMLElement>('#cursebreaker')!
const scenario = new URLSearchParams(location.search).get('scenario') ?? 'null'
const activeRafs = new Set<number>()
const nativeRequestAnimationFrame = window.requestAnimationFrame.bind(window)
const nativeCancelAnimationFrame = window.cancelAnimationFrame.bind(window)
window.requestAnimationFrame = (callback: FrameRequestCallback): number => {
  let request = 0
  request = nativeRequestAnimationFrame((now) => {
    activeRafs.delete(request)
    callback(now)
  })
  activeRafs.add(request)
  return request
}
window.cancelAnimationFrame = (request: number): void => {
  activeRafs.delete(request)
  nativeCancelAnimationFrame(request)
}
const catalog = scenario === 'opening' ? openingCatalog()
  : scenario === 'artifact' ? artifactRuntimeCatalog()
    : scenario === 'editor' ? editorRuntimeCatalog()
      : scenario === 'motion' ? motionRuntimeCatalog()
        : scenario === 'long' ? longRuntimeCatalog()
          : controllerCatalog()

const restoredSave = (): unknown => {
  let state = createInitialGameState(catalog, { reducedMotion: false })
  const first = catalog.source.puzzles[0]!
  state = reduceGame(catalog, state, { kind: 'selectPuzzle', puzzle: first.id }).state
  state = reduceGame(catalog, state, { kind: 'applyStep', step: first.witness[0]! }).state
  state = reduceGame(catalog, state, { kind: 'setCultureScroll', culture: state.selectedCulture, scroll: 137 }).state
  state = reduceGame(catalog, state, { kind: 'setReducedMotion', value: true }).state
  state = reduceGame(catalog, state, { kind: 'setFullscreen', value: false }).state
  state = reduceGame(catalog, state, { kind: 'setTextSize', value: 'large' }).state
  return encodeGameSave(catalog, state)
}

type Deferred = { readonly promise: Promise<void>; resolve(): void; reject(error: Error): void }
const deferred = (): Deferred => {
  let resolve!: () => void
  let reject!: (error: Error) => void
  const promise = new Promise<void>((okay, fail) => { resolve = okay; reject = fail })
  return { promise, resolve, reject }
}

const writes: unknown[] = []
const writeGates: Deferred[] = []
const fullscreenRequests: boolean[] = []
const exits: unknown[] = []
const exitListeners = new Set<() => void>()
let gateWrites = false
let fullscreenResult: boolean | null = null
let fullscreenGate: Deferred | null = null
let unsubscribed = false

const platform: CursebreakerPlatform = {
  async loadSave() {
    if (scenario === 'corrupt') return { format: 'damaged-user-save' }
    return scenario === 'restore' ? restoredSave() : null
  },
  async writeSave(document) {
    writes.push(document)
    if (!gateWrites) return
    const gate = deferred()
    writeGates.push(gate)
    await gate.promise
  },
  async setFullscreen(fullscreen) {
    fullscreenRequests.push(fullscreen)
    if (fullscreenGate !== null) await fullscreenGate.promise
    return fullscreenResult ?? fullscreen
  },
  async requestExit(document) { exits.push(document) },
  onExitRequested(callback) {
    exitListeners.add(callback)
    return () => { unsubscribed = true; exitListeners.delete(callback) }
  },
}

const stateProjection = (debug: CursebreakerDebugState) => ({
  mode: debug.state.mode,
  activePuzzle: debug.state.activePuzzle,
  completed: [...debug.state.completed],
  cursor: debug.state.activePuzzle === null ? null : (
    debug.state.completed.has(debug.state.activePuzzle)
      ? debug.state.replays.get(debug.state.activePuzzle)?.timeline.cursor
      : debug.state.firstAttempts.get(debug.state.activePuzzle)?.timeline.cursor
  ) ?? null,
  steps: debug.state.activePuzzle === null ? [] : [...(
    debug.state.completed.has(debug.state.activePuzzle)
      ? debug.state.replays.get(debug.state.activePuzzle)?.timeline.steps
      : debug.state.firstAttempts.get(debug.state.activePuzzle)?.timeline.steps
  ) ?? []].map((step) => step.rule),
  selectedCulture: debug.state.selectedCulture,
  selectedScroll: debug.state.scrollByCulture.get(debug.state.selectedCulture),
  settings: debug.state.settings,
  transient: debug.state.transient,
  substrateSeed: debug.substrateSeed,
  hasProof: debug.proof !== null,
  hasTimeline: debug.timeline !== null,
  proofInstance: debug.proofInstance,
  proofRebuilds: debug.proof?.rebuilds ?? null,
  motionPlaying: debug.proof?.motion.playing ?? false,
  canvas: (() => {
    const node = document.querySelector<HTMLCanvasElement>('.curse-game-proof-canvas')
    if (node === null) return null
    const rect = node.getBoundingClientRect()
    return { width: node.width, height: node.height, clientWidth: rect.width, clientHeight: rect.height }
  })(),
  layout: debug.layout,
  presentation: debug.presentation,
  construction: debug.proof?.construction ?? null,
  proofRegions: debug.proofRegions,
  proofNodes: debug.proofNodes,
  saveFailure: debug.saveFailure,
})

let mounted: MountedCursebreaker | null = null
let launchError: string | null = null
try {
  mounted = await mountCursebreaker({ host, platform, catalog })
} catch (error) {
  launchError = error instanceof Error ? `${error.name}: ${error.message}` : String(error)
}

const requireMounted = (): MountedCursebreaker => {
  if (mounted === null) throw new Error(`runtime did not mount: ${launchError}`)
  return mounted
}

const fixture = {
  ready: true,
  launchError: () => launchError,
  state: () => stateProjection(requireMounted().debug()),
  writes: () => writes,
  fullscreenRequests: () => fullscreenRequests,
  exits: () => exits,
  gateWrites: (value: boolean) => { gateWrites = value },
  releaseWrite: (index: number) => writeGates[index]?.resolve(),
  failWrite: (index: number, message: string) => writeGates[index]?.reject(new Error(message)),
  setFullscreenResult: (value: boolean | null) => { fullscreenResult = value },
  deferFullscreen: () => { fullscreenGate = deferred() },
  releaseFullscreen: () => { fullscreenGate?.resolve() },
  dispatch: (action: GameAction) => requireMounted().dispatch(action),
  witness: (index: number) => {
    const active = requireMounted().debug().state.activePuzzle
    if (active === null) throw new Error('no active puzzle')
    const step = catalog.puzzle(active).witness[index]
    if (step === undefined) throw new Error(`active puzzle has no witness step ${index}`)
    requireMounted().dispatch({ kind: 'applyStep', step })
  },
  puzzles: () => catalog.source.puzzles.map(({ id }) => id),
  settle: () => requireMounted().settled(),
  nativeExit: () => { for (const callback of exitListeners) callback() },
  dispose: () => requireMounted().dispose(),
  unsubscribed: () => unsubscribed,
  activeRafs: () => activeRafs.size,
}

declare global { interface Window { __authoritativeRuntimeFixture: typeof fixture } }
window.__authoritativeRuntimeFixture = fixture
