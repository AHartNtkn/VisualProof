import type { Diagram } from '../kernel/diagram/diagram'
import type { Theme } from '../view/paint'
import { relationWireHues } from '../view/paint'
import { diagramSpec, type DiagramSpec } from './spec'
import { scene3, type Scene3 } from './scene'
import { planTransition, sceneAt, type TweenPlan } from './transition'
import { escapesFraming, fitPose, orbited, panned, zoomed, type CamPose } from './camera'
import { lerp3, type Vec3 } from './vec3'
import { expandHover, focusPoint } from './pick'
import { mountRender, type RenderTheme } from './render'

export type View3State = { diagram: Diagram; theme: Theme }
export type View3 = { update(s: View3State): void; dispose(): void }

export const TWEEN_MS = 350
/** Glide time for click-to-focus retargeting. */
export const FOCUS_MS = 250

/** The exact scene presented by a frame. Rendering and every interaction
    consumer must share this authority while a structural tween is active. */
export function presentedScene(target: Scene3, plan: TweenPlan | null, progress: number): Scene3 {
  return plan === null ? target : sceneAt(plan, progress)
}

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
  let pose: CamPose = fitPose(scene.center, scene.radius, aspectOf())
  let tween: { plan: TweenPlan; poseFrom: CamPose; poseTo: CamPose; start: number } | null = null
  let hoverKey: string | null = null
  /** Click-to-focus: the orbit target glides to the clicked component
      (USER request 2026-08-16); orbit/zoom mechanics are unchanged. A
      click on empty space refocuses the whole scene. */
  let glide: { from: Vec3; to: Vec3; start: number } | null = null
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
    if (glide !== null) {
      const t = Math.min(1, (now - glide.start) / FOCUS_MS)
      const e = t * t * (3 - 2 * t)
      pose = { ...pose, target: lerp3(glide.from, glide.to, e) }
      if (t >= 1) glide = null
      else schedule()
    }
    if (tween !== null) {
      const t = Math.min(1, (now - tween.start) / TWEEN_MS)
      const e = t * t * (3 - 2 * t)
      pose = mixPose(tween.poseFrom, tween.poseTo, e)
      if (t >= 1) {
        // The clean target list, not sceneAt's interpolated frame — that
        // still carries alpha-0 exits, which would otherwise linger in the
        // scene (and stay pickable) forever after the tween ends.
        presented = presentedScene(scene, null, 1)
        renderer.setEntities(presented.entities)
        tween = null
      } else {
        presented = presentedScene(scene, tween.plan, t)
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
    renderer.setPose(pose)
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

  let drag: { button: number; x: number; y: number } | null = null
  let press: { button: number; x: number; y: number } | null = null
  listen('pointerdown', (ev) => {
    drag = { button: ev.button, x: ev.clientX, y: ev.clientY }
    press = { button: ev.button, x: ev.clientX, y: ev.clientY }
    container.setPointerCapture(ev.pointerId)
  })
  listen('pointerup', (ev) => {
    drag = null
    const wasPress = press
    press = null
    if (wasPress === null || wasPress.button !== 0) return
    if (Math.hypot(ev.clientX - wasPress.x, ev.clientY - wasPress.y) >= 5) return
    const rect = container.getBoundingClientRect()
    const ndcX = ((ev.clientX - rect.left) / rect.width) * 2 - 1
    const ndcY = -(((ev.clientY - rect.top) / rect.height) * 2 - 1)
    const key = renderer.pickAt(ndcX, ndcY)
    const to = key === null ? presented.center : focusPoint(key, presented.entities)
    if (to === null) return
    glide = { from: pose.target, to, start: performance.now() }
    container.dataset['view3Focus'] = key ?? ''
    schedule()
  })
  listen('contextmenu', (ev) => ev.preventDefault())
  listen('pointermove', (ev) => {
    if (drag !== null) {
      const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y
      drag = { ...drag, x: ev.clientX, y: ev.clientY }
      // A pan takes ownership of the target; let the glide yield to it.
      if (drag.button === 2) glide = null
      pose = drag.button === 2 ? panned(pose, dx, dy, container.clientHeight) : orbited(pose, dx, dy)
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
    pose = zoomed(pose, ev.deltaY)
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
        const poseTo = escapesFraming(pose, nextScene.center, nextScene.radius)
          ? { ...fitPose(nextScene.center, nextScene.radius, aspectOf()), yaw: pose.yaw, pitch: pose.pitch }
          : pose
        // If a tween is already in flight, the scene currently ON SCREEN is
        // the interpolated frame at its current t, not `scene` (the last
        // COMPLETED scene) — planning from `scene` would pop the display
        // back to that stale geometry for one frame before animating on.
        const fromScene = presented
        tween = { plan: planTransition(fromScene, nextScene, theme.wire), poseFrom: pose, poseTo, start: performance.now() }
        glide = null // the transition's pose tween owns the camera now
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
