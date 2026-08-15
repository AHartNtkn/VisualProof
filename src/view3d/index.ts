import type { Diagram } from '../kernel/diagram/diagram'
import type { Theme } from '../view/paint'
import { relationWireHues } from '../view/paint'
import { diagramSpec, type DiagramSpec } from './spec'
import { scene3, type Scene3 } from './scene'
import { planTransition, sceneAt, type TweenPlan } from './transition'
import { escapesFraming, fitPose, orbited, panned, zoomed, type CamPose } from './camera'
import { lerp3 } from './vec3'
import { expandHover } from './pick'
import { mountRender, type RenderTheme } from './render'

export type View3State = { diagram: Diagram; theme: Theme }
export type View3 = { update(s: View3State): void; dispose(): void }

export const TWEEN_MS = 350

const renderThemeOf = (theme: Theme, diagram: Diagram): RenderTheme => ({
  mode: theme.mode,
  background: theme.canvas,
  line: theme.mode === 'dark' ? '#f2f4f8' : theme.ink,
  baseWire: theme.wire,
  hover: theme.interaction.hover,
  hues: relationWireHues(diagram, theme.relationHueLightness),
})

export function mountView3(container: HTMLElement, initial: View3State): View3 {
  let diagram = initial.diagram
  let theme = initial.theme
  let spec: DiagramSpec = diagramSpec(diagram)
  let scene: Scene3 = scene3(diagram)
  const aspectOf = (): number => container.clientWidth / Math.max(1, container.clientHeight)
  let pose: CamPose = fitPose(scene.center, scene.radius, aspectOf())
  let tween: { plan: TweenPlan; poseFrom: CamPose; poseTo: CamPose; start: number } | null = null
  let hoverKey: string | null = null
  container.dataset['view3Hover'] = ''

  const renderer = mountRender(container, renderThemeOf(theme, diagram))
  renderer.setEntities(scene.entities)

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
    if (tween !== null) {
      const t = Math.min(1, (now - tween.start) / TWEEN_MS)
      const e = t * t * (3 - 2 * t)
      pose = mixPose(tween.poseFrom, tween.poseTo, e)
      if (t >= 1) {
        // The clean target list, not sceneAt's interpolated frame — that
        // still carries alpha-0 exits, which would otherwise linger in the
        // scene (and stay pickable) forever after the tween ends.
        renderer.setEntities(scene.entities)
        tween = null
      } else {
        renderer.setEntities(sceneAt(tween.plan, t).entities)
        schedule()
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
  listen('pointerdown', (ev) => {
    drag = { button: ev.button, x: ev.clientX, y: ev.clientY }
    container.setPointerCapture(ev.pointerId)
  })
  listen('pointerup', () => { drag = null })
  listen('contextmenu', (ev) => ev.preventDefault())
  listen('pointermove', (ev) => {
    if (drag !== null) {
      const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y
      drag = { ...drag, x: ev.clientX, y: ev.clientY }
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
      renderer.setHoverKeys(key === null ? new Set() : expandHover(key, spec, scene.entities))
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
        const fromScene = tween === null
          ? scene
          : sceneAt(tween.plan, Math.min(1, (performance.now() - tween.start) / TWEEN_MS))
        tween = { plan: planTransition(fromScene, nextScene), poseFrom: pose, poseTo, start: performance.now() }
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
