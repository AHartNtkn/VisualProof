import type { Diagram } from '../kernel/diagram/diagram'
import type { Theme } from '../view/paint'
import { relationWireHues } from '../view/paint'
import { diagramSpec, type DiagramSpec } from './spec'
import { scene3, type Scene3 } from './scene'
import { SCENE_TWEEN_MS, SceneTweenTrack } from './transition'
import { escapesFraming, fitPose, type CamPose } from './camera'
import { lerp3 } from './vec3'
import { expandHover, focusPoint } from './pick'
import { mountRender, type RenderTheme } from './render'
import { OrbitInteraction } from './orbit-interaction'
import type { LambdaMotionTransition } from '../view/lambda-transition'

export type View3State = {
  diagram: Diagram
  theme: Theme
  lambdaTransition?: LambdaMotionTransition | null
}
export type View3 = { update(s: View3State): void; dispose(): void }

const renderThemeOf = (theme: Theme, diagram: Diagram): RenderTheme => ({
  mode: theme.mode,
  background: theme.canvas,
  line: theme.mode === 'dark' ? '#f2f4f8' : theme.ink,
  lineAlt: theme.frame,
  baseWire: theme.wire,
  hover: theme.interaction.hover,
  hues: relationWireHues(diagram, theme.relationHueLightness),
})

export function mountView3(container: HTMLElement, initial: View3State): View3 {
  let diagram = initial.diagram
  let theme = initial.theme
  let spec: DiagramSpec = diagramSpec(diagram)
  let scene: Scene3 = scene3(diagram)
  let presented: Scene3 = scene
  const aspectOf = (): number => container.clientWidth / Math.max(1, container.clientHeight)
  const orbit = new OrbitInteraction(fitPose(scene.center, scene.radius, aspectOf()))
  let tween: { track: SceneTweenTrack; poseFrom: CamPose; poseTo: CamPose; start: number } | null = null
  let hoverKey: string | null = null
  container.dataset['view3Hover'] = ''
  container.dataset['view3Focus'] = ''

  const renderer = mountRender(container, renderThemeOf(theme, diagram))
  renderer.setEntities(presented.entities)

  let pending = false
  const schedule = (): void => {
    if (pending) return
    pending = true
    requestAnimationFrame(frame)
  }
  const mixPose = (a: CamPose, b: CamPose, t: number): CamPose => ({
    target: lerp3(a.target, b.target, t),
    dist: a.dist + (b.dist - a.dist) * t,
    yaw: a.yaw + (b.yaw - a.yaw) * t,
    pitch: a.pitch + (b.pitch - a.pitch) * t,
  })
  const frame = (now: number): void => {
    pending = false
    if (orbit.isGliding) schedule()
    if (tween !== null) {
      const t = Math.min(1, (now - tween.start) / SCENE_TWEEN_MS)
      const e = t * t * (3 - 2 * t)
      orbit.replacePose(mixPose(tween.poseFrom, tween.poseTo, e))
      if (tween.track.completed(now)) {
        // The clean target list, not sceneAt's interpolated frame — that
        // still carries alpha-0 exits, which would otherwise linger in the
        // scene (and stay pickable) forever after the tween ends.
        presented = tween.track.target
        renderer.setEntities(presented.entities)
        tween = null
      } else {
        presented = tween.track.sample(now)
        renderer.setEntities(presented.entities)
        schedule()
      }
      if (hoverKey !== null) {
        if (!presented.entities.some((entity) => entity.key === hoverKey)) {
          hoverKey = null
          container.dataset['view3Hover'] = ''
        }
        renderer.setHoverKeys(hoverKey === null ? new Set() : expandHover(hoverKey, spec, presented.entities))
      }
    }
    renderer.setPose(orbit.poseAt(now))
    renderer.render()
  }

  const listeners: Array<() => void> = []
  const listen = <K extends keyof HTMLElementEventMap>(
    type: K, handler: (ev: HTMLElementEventMap[K]) => void,
  ): void => {
    const h = handler as EventListener
    container.addEventListener(type, h)
    listeners.push(() => container.removeEventListener(type, h))
  }

  listen('pointerdown', (ev) => {
    orbit.pointerDown(ev.button, ev.clientX, ev.clientY)
    container.setPointerCapture(ev.pointerId)
  })
  listen('pointerup', (ev) => {
    const release = orbit.pointerUp(ev.clientX, ev.clientY)
    if (release === null || release.button !== 0) return
    const rect = container.getBoundingClientRect()
    const ndcX = ((release.clientX - rect.left) / rect.width) * 2 - 1
    const ndcY = -(((release.clientY - rect.top) / rect.height) * 2 - 1)
    const key = renderer.pickAt(ndcX, ndcY)
    const to = key === null ? presented.center : focusPoint(key, presented.entities)
    if (to === null) return
    orbit.focus(to, performance.now())
    container.dataset['view3Focus'] = key ?? ''
    schedule()
  })
  listen('pointercancel', () => orbit.cancelPointer())
  listen('lostpointercapture', () => orbit.cancelPointer())
  listen('contextmenu', (ev) => ev.preventDefault())
  listen('pointermove', (ev) => {
    if (orbit.pointerMove(ev.clientX, ev.clientY, container.clientHeight, performance.now())) {
      schedule()
      return
    }
    const rect = container.getBoundingClientRect()
    const ndcX = ((ev.clientX - rect.left) / rect.width) * 2 - 1
    const ndcY = -(((ev.clientY - rect.top) / rect.height) * 2 - 1)
    const key = renderer.pickAt(ndcX, ndcY)
    if (key !== hoverKey) {
      hoverKey = key
      container.dataset['view3Hover'] = key ?? ''
      renderer.setHoverKeys(key === null ? new Set() : expandHover(key, spec, presented.entities))
      schedule()
    }
  })
  listen('wheel', (ev) => {
    ev.preventDefault()
    orbit.wheel(ev.deltaY, performance.now())
    schedule()
  })

  const ro = new ResizeObserver(() => {
    renderer.resize(container.clientWidth, container.clientHeight)
    schedule()
  })
  ro.observe(container)
  renderer.resize(container.clientWidth, container.clientHeight)
  schedule()

  return {
    update(s) {
      if (s.diagram === diagram && s.theme === theme) return
      theme = s.theme
      if (s.diagram !== diagram) {
        diagram = s.diagram
        const nextSpec = diagramSpec(diagram)
        const nextScene = scene3(diagram)
        const now = performance.now()
        const displayedPose = orbit.poseAt(now)
        const poseTo = escapesFraming(displayedPose, nextScene.center, nextScene.radius)
          ? { ...fitPose(nextScene.center, nextScene.radius, aspectOf()), yaw: displayedPose.yaw, pitch: displayedPose.pitch }
          : displayedPose
        // If a tween is already in flight, the scene currently ON SCREEN is
        // the interpolated frame at its current t, not `scene` (the last
        // COMPLETED scene) — planning from `scene` would pop the display
        // back to that stale geometry for one frame before animating on.
        const fromScene = presented
        const track = tween === null
          ? new SceneTweenTrack(fromScene, nextScene, now, theme.wire, s.lambdaTransition ?? null)
          : tween.track.begin(fromScene, nextScene, now, theme.wire, s.lambdaTransition ?? null)
        tween = { track, poseFrom: displayedPose, poseTo, start: now }
        orbit.replacePose(displayedPose)
        container.dataset['view3Focus'] = ''
        spec = nextSpec
        scene = nextScene
        hoverKey = null
        container.dataset['view3Hover'] = ''
        renderer.setHoverKeys(new Set())
      }
      renderer.setTheme(renderThemeOf(theme, diagram)) // hues depend on the diagram too
      schedule()
    },
    dispose() {
      for (const off of listeners) off()
      ro.disconnect()
      renderer.dispose()
    },
  }
}
