import './style.css'
import { formatFps, frameTiming } from './frame'
import { mountOrchardWorld, type OrchardBuildStats } from './render'
import { clampGroundPosition, stepWalker, type WalkInput } from './walk'
import { loadWorldSave } from './world'

const root = document.querySelector<HTMLElement>('[data-orchard]')!
const viewport = document.querySelector<HTMLElement>('[data-viewport]')!
const form = document.querySelector<HTMLFormElement>('[data-count-form]')!
const countInput = document.querySelector<HTMLInputElement>('#tree-count')!
const countScale = document.querySelector<HTMLInputElement>('#tree-scale')!
const status = document.querySelector<HTMLElement>('[data-status]')!
const lookHint = document.querySelector<HTMLElement>('[data-look-hint]')!
const fpsOut = document.querySelector<HTMLElement>('[data-fps]')!
const frameMsOut = document.querySelector<HTMLElement>('[data-frame-ms]')!
const drawCallsOut = document.querySelector<HTMLElement>('[data-draw-calls]')!
const geometriesOut = document.querySelector<HTMLElement>('[data-geometries]')!
const entitiesOut = document.querySelector<HTMLElement>('[data-entities]')!
const buildMsOut = document.querySelector<HTMLElement>('[data-build-ms]')!
const applyButton = form.querySelector<HTMLButtonElement>('button')!
const presetButtons = [...document.querySelectorAll<HTMLButtonElement>('[data-preset]')]
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
  countInput.max = String(savedWorld.trees.length)
  countScale.max = String(savedWorld.trees.length)
  specimen.textContent = Object.values(savedWorld.layouts)[0]!.label
  const keys = new Set<string>()
  let yaw = savedWorld.player.yaw
  let pitch = savedWorld.player.pitch
  let player = { x: savedWorld.player.x, z: savedWorld.player.z }
  let previousFrame = performance.now()
  let recentFrameMs: number[] = []
  let lastMetricsUpdate = 0
  let latestBuild: OrchardBuildStats | null = null
  let buildInFlight = false

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
    status.textContent = `Growing ${count.toLocaleString()} separate trees…`
    try {
      latestBuild = await world.setCount(count)
      treeCount = count
      root.dataset['treeCount'] = String(latestBuild.trees)
      root.dataset['entityCount'] = String(latestBuild.entities)
      root.dataset['instancedCount'] = String(latestBuild.instanced)
      entitiesOut.textContent = latestBuild.entities.toLocaleString()
      buildMsOut.textContent = `${latestBuild.buildMs.toFixed(0)} ms`
      recentFrameMs = []
      previousFrame = performance.now()
      status.textContent = `${latestBuild.trees.toLocaleString()} independent trees · ${latestBuild.objects.toLocaleString()} renderer objects · no instancing`
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

  const frame = (now: number): void => {
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
    root.dataset['playerX'] = player.x.toFixed(3)
    root.dataset['playerZ'] = player.z.toFixed(3)
    recentFrameMs.push(timing.sampleMs)
    if (recentFrameMs.length > 90) recentFrameMs.shift()
    if (now - lastMetricsUpdate >= 250) {
      const average = recentFrameMs.reduce((sum, value) => sum + value, 0) / Math.max(1, recentFrameMs.length)
      fpsOut.textContent = average > 0 ? formatFps(1000 / average) : '—'
      frameMsOut.textContent = `${average.toFixed(1)} ms`
      drawCallsOut.textContent = rendered.drawCalls.toLocaleString()
      geometriesOut.textContent = rendered.geometries.toLocaleString()
      root.dataset['drawCalls'] = String(rendered.drawCalls)
      lastMetricsUpdate = now
      recentFrameMs = recentFrameMs.slice(-60)
    }
    requestAnimationFrame(frame)
  }

  addEventListener('keydown', (event) => {
    if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ShiftLeft', 'ShiftRight'].includes(event.code)) {
      event.preventDefault()
      keys.add(event.code)
    }
  })
  addEventListener('keyup', (event) => keys.delete(event.code))
  addEventListener('blur', () => keys.clear())
  world.canvas.addEventListener('click', () => { void world.canvas.requestPointerLock() })
  document.addEventListener('pointerlockchange', () => {
    const locked = document.pointerLockElement === world.canvas
    root.dataset['pointerLocked'] = String(locked)
    lookHint.textContent = locked ? 'Mouse look active' : 'Click to look around'
    lookHint.classList.toggle('locked', locked)
  })
  document.addEventListener('mousemove', (event) => {
    if (document.pointerLockElement !== world.canvas) return
    yaw -= event.movementX * 0.0022
    pitch = Math.max(-1.35, Math.min(1.35, pitch - event.movementY * 0.0022))
  })
  form.addEventListener('submit', (event) => {
    event.preventDefault()
    const requested = Number(countInput.value)
    if (!Number.isFinite(requested)) return
    requestCount(requested)
  })
  countInput.addEventListener('input', () => {
    const requested = Number(countInput.value)
    if (Number.isFinite(requested)) {
      countScale.value = String(Math.min(savedWorld.trees.length, Math.max(1, Math.trunc(requested))))
    }
  })
  countScale.addEventListener('input', () => { countInput.value = countScale.value })
  countScale.addEventListener('change', () => requestCount(Number(countScale.value)))
  for (const button of presetButtons) {
    button.addEventListener('click', () => requestCount(Number(button.dataset['preset'])))
  }

  requestAnimationFrame(frame)
  await applyCount(treeCount)
  root.dataset['ready'] = 'true'
}

void boot().catch((error: unknown) => {
  root.dataset['ready'] = 'error'
  status.textContent = error instanceof Error ? error.message : String(error)
  throw error
})
