import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { WireId } from '../kernel/diagram/diagram'
import type { FadedEntity } from './transition'
import { FOV_DEG, eyeOf, type CamPose } from './camera'

export type RenderTheme = {
  mode: 'light' | 'dark'
  background: string
  line: string
  baseWire: string
  hover: string
  hues: Map<WireId, string>
}

export type Renderer3 = {
  setEntities(entities: readonly FadedEntity[]): void
  setTheme(t: RenderTheme): void
  setPose(p: CamPose): void
  setHoverKeys(keys: ReadonlySet<string>): void
  pickAt(ndcX: number, ndcY: number): string | null
  render(): void
  resize(w: number, h: number): void
  dispose(): void
}

const LINE_W: Record<'branch' | 'ring' | 'strand', number> = { branch: 3.5, ring: 2.2, strand: 2.2 }
const HOVER_EXTRA_W = 1.2
const BEAD_SCALE = 0.18
const BLOOM = { strength: 0.9, radius: 0.6, threshold: 0.15 }
const PICK_THRESHOLD = 0.12

function discTexture(color: string): THREE.CanvasTexture {
  const c = document.createElement('canvas')
  c.width = c.height = 64
  const ctx = c.getContext('2d')!
  ctx.fillStyle = color
  ctx.beginPath()
  ctx.arc(32, 32, 28, 0, 2 * Math.PI)
  ctx.fill()
  return new THREE.CanvasTexture(c)
}

function textSprite(text: string, color: string): THREE.Sprite {
  const c = document.createElement('canvas')
  const ctx = c.getContext('2d')!
  ctx.font = '48px Georgia, serif'
  c.width = Math.max(2, Math.ceil(ctx.measureText(text).width) + 8)
  c.height = 64
  const ctx2 = c.getContext('2d')!
  ctx2.font = '48px Georgia, serif'
  ctx2.fillStyle = color
  ctx2.textBaseline = 'middle'
  ctx2.fillText(text, 4, 32)
  const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(c), transparent: true }))
  sprite.scale.set(0.9 * (c.width / c.height), 0.9, 1)
  return sprite
}

export function mountRender(container: HTMLElement, theme: RenderTheme): Renderer3 {
  let th = theme
  const renderer = new THREE.WebGLRenderer({ antialias: true, preserveDrawingBuffer: true })
  renderer.domElement.dataset['view3'] = ''
  renderer.domElement.style.cssText = 'width:100%;height:100%;display:block;'
  container.appendChild(renderer.domElement)
  const scene = new THREE.Scene()
  const camera = new THREE.PerspectiveCamera(FOV_DEG, 1, 0.01, 5000)
  const composer = new EffectComposer(renderer)
  composer.addPass(new RenderPass(scene, camera))
  const bloom = new UnrealBloomPass(new THREE.Vector2(1, 1), BLOOM.strength, BLOOM.radius, BLOOM.threshold)
  const group = new THREE.Group()
  scene.add(group)
  const lineMaterials = new Set<LineMaterial>()
  const pickables: THREE.Line[] = []
  const raycaster = new THREE.Raycaster()
  raycaster.params.Line = { threshold: PICK_THRESHOLD }
  let size = { w: 1, h: 1 }
  let entities: readonly FadedEntity[] = []
  let hoverKeys: ReadonlySet<string> = new Set()

  const applyBackground = (): void => {
    scene.background = new THREE.Color(th.background)
    const idx = composer.passes.indexOf(bloom)
    if (th.mode === 'dark' && idx === -1) composer.addPass(bloom)
    if (th.mode !== 'dark' && idx !== -1) composer.removePass(bloom)
  }
  applyBackground()

  const colorOf = (e: FadedEntity): string =>
    e.kind === 'strand' ? (th.hues.get(e.wire) ?? th.baseWire) : th.line

  const disposeObject = (o: THREE.Object3D): void => {
    o.traverse((c) => {
      const anyC = c as unknown as { geometry?: { dispose(): void }; material?: THREE.Material & { map?: THREE.Texture | null } }
      anyC.geometry?.dispose()
      if (anyC.material !== undefined) {
        anyC.material.map?.dispose()
        anyC.material.dispose()
      }
    })
  }

  const rebuild = (): void => {
    for (const child of [...group.children]) { group.remove(child); disposeObject(child) }
    lineMaterials.clear()
    pickables.length = 0
    for (const e of entities) {
      const hovered = hoverKeys.has(e.key)
      const color = hovered ? th.hover : colorOf(e)
      const alpha = e.alpha ?? 1
      if (e.kind === 'bead') {
        const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: discTexture(color), transparent: true, opacity: alpha }))
        sprite.position.set(e.pos.x, e.pos.y, e.pos.z)
        sprite.scale.set(BEAD_SCALE, BEAD_SCALE, 1)
        sprite.userData['key'] = e.key
        group.add(sprite)
        continue
      }
      if (e.kind === 'label') {
        const sprite = textSprite(e.text, color)
        sprite.material.opacity = alpha
        sprite.position.set(e.pos.x, e.pos.y, e.pos.z)
        sprite.userData['key'] = e.key
        group.add(sprite)
        continue
      }
      const width = LINE_W[e.kind] + (hovered ? HOVER_EXTRA_W : 0)
      const geo = new LineGeometry()
      geo.setPositions(e.pts.flatMap((p) => [p.x, p.y, p.z]))
      const mat = new LineMaterial({ color, linewidth: width, transparent: true, opacity: alpha })
      mat.resolution.set(size.w, size.h)
      lineMaterials.add(mat)
      const line = new Line2(geo, mat)
      line.computeLineDistances()
      line.userData['key'] = e.key
      group.add(line)
      const pickGeo = new THREE.BufferGeometry().setFromPoints(e.pts.map((p) => new THREE.Vector3(p.x, p.y, p.z)))
      const pick = new THREE.Line(pickGeo, new THREE.LineBasicMaterial({ visible: false }))
      pick.userData['key'] = e.key
      group.add(pick)
      pickables.push(pick)
    }
  }

  return {
    setEntities(next) { entities = next; rebuild() },
    setTheme(next) { th = next; applyBackground(); rebuild() },
    setPose(p) {
      const eye = eyeOf(p)
      camera.position.set(eye.x, eye.y, eye.z)
      camera.up.set(0, 1, 0)
      camera.lookAt(p.target.x, p.target.y, p.target.z)
    },
    setHoverKeys(keys) { hoverKeys = keys; rebuild() },
    pickAt(ndcX, ndcY) {
      raycaster.setFromCamera(new THREE.Vector2(ndcX, ndcY), camera)
      const hits = raycaster.intersectObjects(pickables, false)
      const key = hits[0]?.object.userData['key']
      return typeof key === 'string' ? key : null
    },
    render() { composer.render() },
    resize(w, h) {
      size = { w, h }
      renderer.setSize(w, h, false)
      composer.setSize(w, h)
      camera.aspect = w / Math.max(1, h)
      camera.updateProjectionMatrix()
      for (const m of lineMaterials) m.resolution.set(w, h)
    },
    dispose() {
      for (const child of [...group.children]) { group.remove(child); disposeObject(child) }
      bloom.dispose()
      composer.dispose()
      renderer.dispose()
      renderer.domElement.remove()
    },
  }
}
