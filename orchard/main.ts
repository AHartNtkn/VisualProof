import './style.css'
import { SettledFrameTelemetry, formatFps, frameTiming, percentile, type SettledFrameSnapshot } from './frame'
import { mountOrchardWorld, type OrchardFrameStats, type RenderMode } from './render'
import { clampGroundPosition, stepWalker, type WalkInput } from './walk'
import { loadWorldSave } from './world'

const root = document.querySelector<HTMLElement>('[data-orchard]')!
const viewport = document.querySelector<HTMLElement>('[data-viewport]')!
const form = document.querySelector<HTMLFormElement>('[data-count-form]')!
const countInput = document.querySelector<HTMLInputElement>('#tree-count')!
const countScale = document.querySelector<HTMLInputElement>('#tree-scale')!
const status = document.querySelector<HTMLElement>('[data-status]')!
const lookHint = document.querySelector<HTMLElement>('[data-look-hint]')!
const output = (selector: string): HTMLElement => document.querySelector<HTMLElement>(selector)!
const fpsOut = output('[data-fps]')
const frameMsOut = output('[data-frame-ms]')
const p95FrameMsOut = output('[data-p95-frame-ms]')
const frameSamplesOut = output('[data-frame-samples]')
const modeOut = output('[data-render-mode-output]')
const logicalOut = output('[data-logical]')
const visibleOut = output('[data-visible]')
const residentOut = output('[data-resident]')
const fullOut = output('[data-full]')
const reducedOut = output('[data-reduced]')
const markerOut = output('[data-marker]')
const culledOut = output('[data-culled]')
const pendingOut = output('[data-pending]')
const glowTilesOut = output('[data-glow-tiles]')
const pointLightsOut = output('[data-point-lights]')
const entitiesOut = output('[data-entities]')
const objectsOut = output('[data-objects]')
const drawCallsOut = output('[data-draw-calls]')
const geometriesOut = output('[data-geometries]')
const trianglesOut = output('[data-triangles]')
const buildMsOut = output('[data-build-ms]')
const transitionBuildMsOut = output('[data-transition-build-ms]')
const lodMsOut = output('[data-lod-ms]')
const applyButton = form.querySelector<HTMLButtonElement>('button')!
const presetButtons = [...document.querySelectorAll<HTMLButtonElement>('[data-preset]')]
const modeInputs = [...document.querySelectorAll<HTMLInputElement>('input[name="render-mode"]')]
const specimen = document.querySelector<HTMLElement>('.specimen')!
const MAX_TREES = 2000

const queryCount = Number(new URLSearchParams(location.search).get('trees'))
let treeCount = Number.isInteger(queryCount) && queryCount >= 1
  ? Math.min(queryCount, MAX_TREES)
  : 50
countInput.value = String(treeCount)
countScale.value = String(treeCount)

async function boot(): Promise<void> {
  await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()))
  const savedWorld = await loadWorldSave()
  const world = mountOrchardWorld(viewport, savedWorld)
  root.dataset['worldVersion'] = String(savedWorld.version)
  root.dataset['savedTreeCount'] = String(savedWorld.trees.length)
  root.dataset['renderMode'] = 'game'
  root.dataset['pointLightCount'] = '0'
  countInput.max = String(savedWorld.trees.length)
  countScale.max = String(savedWorld.trees.length)
  specimen.textContent = Object.values(savedWorld.layouts)[0]!.label

  const keys = new Set<string>()
  const removeListeners: Array<() => void> = []
  let yaw = savedWorld.player.yaw
  let pitch = savedWorld.player.pitch
  let player = { x: savedWorld.player.x, z: savedWorld.player.z }
  let previousFrame = performance.now()
  const frameTelemetry = new SettledFrameTelemetry(60)
  let lastMetricsUpdate = 0
  let buildInFlight = false
  let activeMode: RenderMode = 'game'
  let animationFrame = 0
  let disposed = false

  const listen = (target: EventTarget, type: string, listener: (event: Event) => void): void => {
    const callback = listener as EventListener
    target.addEventListener(type, callback)
    removeListeners.push(() => target.removeEventListener(type, callback))
  }

  const resize = (): void => world.resize(viewport.clientWidth, viewport.clientHeight)
  const resizeObserver = new ResizeObserver(resize)
  resizeObserver.observe(viewport)
  resize()

  const applyCount = async (requested: number): Promise<void> => {
    if (buildInFlight) return
    buildInFlight = true
    const count = Math.min(savedWorld.trees.length, Math.max(1, Math.trunc(requested)))
    countInput.value = String(count)
    countScale.value = String(count)
    countInput.disabled = true
    countScale.disabled = true
    applyButton.disabled = true
    for (const button of presetButtons) button.disabled = true
    root.dataset['building'] = 'true'
    status.textContent = `Synchronizing ${count.toLocaleString()} logical trees…`
    try {
      frameTelemetry.beginTransition()
      const build = await world.setCount(count)
      treeCount = count
      root.dataset['treeCount'] = String(build.trees)
      root.dataset['entityCount'] = String(build.entities)
      previousFrame = performance.now()
      status.textContent = `${build.trees.toLocaleString()} logical trees · representation residency updates during rendered frames`
      history.replaceState(null, '', `?trees=${count}`)
      for (const button of presetButtons) {
        button.setAttribute('aria-pressed', String(Number(button.dataset['preset']) === count))
      }
    } finally {
      root.dataset['building'] = 'false'
      buildInFlight = false
      countInput.disabled = false
      countScale.disabled = false
      applyButton.disabled = false
      for (const button of presetButtons) button.disabled = false
    }
  }

  const requestCount = (requested: number): void => {
    void applyCount(requested).catch((error: unknown) => {
      status.textContent = error instanceof Error ? error.message : String(error)
    })
  }

  const mirrorFrameDatasets = (
    rendered: OrchardFrameStats,
    settled: SettledFrameSnapshot,
    average: number,
    p95: number,
  ): void => {
    const fps = average > 0 ? 1000 / average : 0
    root.dataset['renderMode'] = activeMode
    root.dataset['logicalCount'] = String(rendered.logical)
    root.dataset['visibleCount'] = String(rendered.visible)
    root.dataset['residentCount'] = String(rendered.resident)
    root.dataset['fullCount'] = String(rendered.full)
    root.dataset['reducedCount'] = String(rendered.reduced)
    root.dataset['markerCount'] = String(rendered.marker)
    root.dataset['culledCount'] = String(rendered.culled)
    root.dataset['pendingRepresentations'] = String(rendered.pending)
    root.dataset['glowTileCount'] = String(rendered.glowTiles)
    root.dataset['pointLightCount'] = String(rendered.pointLights)
    root.dataset['representedProofEntities'] = String(rendered.representedEntities)
    root.dataset['rendererObjects'] = String(rendered.objects)
    root.dataset['instancedCount'] = String(rendered.instanced)
    root.dataset['drawCalls'] = String(rendered.drawCalls)
    root.dataset['geometries'] = String(rendered.geometries)
    root.dataset['triangles'] = String(rendered.triangles)
    root.dataset['buildMs'] = rendered.buildMs.toFixed(3)
    root.dataset['transitionBuildMs'] = settled.transitionBuildMs.toFixed(3)
    root.dataset['frameSampleCount'] = String(settled.sampleCount)
    root.dataset['fps'] = fps.toFixed(3)
    root.dataset['averageFrameMs'] = average.toFixed(3)
    root.dataset['p95FrameMs'] = p95.toFixed(3)
    root.dataset['lodCpuMs'] = rendered.lodMs.toFixed(3)
  }

  const updateMetricText = (
    rendered: OrchardFrameStats,
    settled: SettledFrameSnapshot,
    average: number,
    p95: number,
  ): void => {
    const fps = average > 0 ? 1000 / average : 0
    fpsOut.textContent = fps > 0 ? formatFps(fps) : '—'
    frameMsOut.textContent = `${average.toFixed(1)} ms`
    p95FrameMsOut.textContent = `${p95.toFixed(1)} ms`
    frameSamplesOut.textContent = `${settled.sampleCount} / 60`
    modeOut.textContent = activeMode === 'game' ? 'Game LOD' : 'Raw full detail'
    logicalOut.textContent = rendered.logical.toLocaleString()
    visibleOut.textContent = rendered.visible.toLocaleString()
    residentOut.textContent = rendered.resident.toLocaleString()
    fullOut.textContent = rendered.full.toLocaleString()
    reducedOut.textContent = rendered.reduced.toLocaleString()
    markerOut.textContent = rendered.marker.toLocaleString()
    culledOut.textContent = rendered.culled.toLocaleString()
    pendingOut.textContent = rendered.pending.toLocaleString()
    glowTilesOut.textContent = rendered.glowTiles.toLocaleString()
    pointLightsOut.textContent = String(rendered.pointLights)
    entitiesOut.textContent = rendered.representedEntities.toLocaleString()
    objectsOut.textContent = rendered.objects.toLocaleString()
    drawCallsOut.textContent = rendered.drawCalls.toLocaleString()
    geometriesOut.textContent = rendered.geometries.toLocaleString()
    trianglesOut.textContent = rendered.triangles.toLocaleString()
    buildMsOut.textContent = `${rendered.buildMs.toFixed(2)} ms`
    transitionBuildMsOut.textContent = `${settled.transitionBuildMs.toFixed(2)} ms`
    lodMsOut.textContent = `${rendered.lodMs.toFixed(2)} ms`
    status.textContent = rendered.error === null
      ? `${rendered.logical.toLocaleString()} logical · ${rendered.visible.toLocaleString()} visible · ${rendered.resident.toLocaleString()} resident · ${rendered.pending.toLocaleString()} pending`
      : `Representation error: ${rendered.error}`
  }

  const frame = (now: number): void => {
    if (disposed) return
    const timing = frameTiming(now, previousFrame)
    previousFrame = now
    const input: WalkInput = {
      forward: keys.has('KeyW') || keys.has('ArrowUp'),
      backward: keys.has('KeyS') || keys.has('ArrowDown'),
      left: keys.has('KeyA') || keys.has('ArrowLeft'),
      right: keys.has('KeyD') || keys.has('ArrowRight'),
      sprint: keys.has('ShiftLeft') || keys.has('ShiftRight'),
    }
    player = clampGroundPosition(
      stepWalker(player, input, timing.movementSeconds, yaw),
      savedWorld.terrain.bounds,
    )
    world.setPlayer(player.x, player.z, yaw, pitch)
    const rendered = world.render()
    const settled = frameTelemetry.record({
      frameMs: timing.sampleMs,
      pending: rendered.pending,
      buildMs: rendered.buildMs,
    })
    const average = settled.samples.reduce((sum, value) => sum + value, 0) / Math.max(1, settled.sampleCount)
    const p95 = percentile(settled.samples, 0.95)
    root.dataset['playerX'] = player.x.toFixed(3)
    root.dataset['playerZ'] = player.z.toFixed(3)
    mirrorFrameDatasets(rendered, settled, average, p95)
    if (now - lastMetricsUpdate >= 250) {
      updateMetricText(rendered, settled, average, p95)
      lastMetricsUpdate = now
    }
    animationFrame = requestAnimationFrame(frame)
  }

  const disposeApplication = (): void => {
    if (disposed) return
    disposed = true
    cancelAnimationFrame(animationFrame)
    resizeObserver.disconnect()
    keys.clear()
    for (const remove of removeListeners.splice(0)) remove()
    world.dispose()
  }

  listen(window, 'keydown', (rawEvent) => {
    const event = rawEvent as KeyboardEvent
    if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ShiftLeft', 'ShiftRight'].includes(event.code)) {
      event.preventDefault()
      keys.add(event.code)
    }
  })
  listen(window, 'keyup', (rawEvent) => keys.delete((rawEvent as KeyboardEvent).code))
  listen(window, 'blur', () => keys.clear())
  listen(world.canvas, 'click', () => { void world.canvas.requestPointerLock() })
  listen(document, 'pointerlockchange', () => {
    const locked = document.pointerLockElement === world.canvas
    root.dataset['pointerLocked'] = String(locked)
    lookHint.textContent = locked ? 'Mouse look active' : 'Click to look around'
    lookHint.classList.toggle('locked', locked)
  })
  listen(document, 'mousemove', (rawEvent) => {
    if (document.pointerLockElement !== world.canvas) return
    const event = rawEvent as MouseEvent
    yaw -= event.movementX * 0.0022
    pitch = Math.max(-1.35, Math.min(1.35, pitch - event.movementY * 0.0022))
  })
  listen(form, 'submit', (event) => {
    event.preventDefault()
    const requested = Number(countInput.value)
    if (!Number.isFinite(requested)) return
    requestCount(requested)
  })
  listen(countInput, 'input', () => {
    const requested = Number(countInput.value)
    if (Number.isFinite(requested)) {
      countScale.value = String(Math.min(savedWorld.trees.length, Math.max(1, Math.trunc(requested))))
    }
  })
  listen(countScale, 'input', () => { countInput.value = countScale.value })
  listen(countScale, 'change', () => requestCount(Number(countScale.value)))
  for (const button of presetButtons) {
    listen(button, 'click', () => requestCount(Number(button.dataset['preset'])))
  }
  for (const input of modeInputs) {
    listen(input, 'change', () => {
      if (!input.checked) return
      activeMode = input.value as RenderMode
      frameTelemetry.beginTransition()
      world.setMode(activeMode)
      root.dataset['renderMode'] = activeMode
      status.textContent = activeMode === 'game'
        ? 'Switching to camera-driven Game LOD…'
        : 'Switching every logical tree to Raw full detail…'
    })
  }
  listen(window, 'beforeunload', disposeApplication)

  world.setPlayer(player.x, player.z, yaw, pitch)
  animationFrame = requestAnimationFrame(frame)
  await applyCount(treeCount)
  await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()))
  root.dataset['ready'] = 'true'
}

void boot().catch((error: unknown) => {
  root.dataset['ready'] = 'error'
  status.textContent = error instanceof Error ? error.message : String(error)
  throw error
})
