import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { WireId } from '../kernel/diagram/diagram'
import type { Entity } from './scene'
import type { FadedEntity } from './transition'
import { FOV_DEG, eyeOf, type CamPose } from './camera'

export type RenderTheme = {
  mode: 'light' | 'dark'
  background: string
  line: string
  /** Odd-polarity (cut) branch color: cut-nesting parity strokes branches
      in alternating line/lineAlt — sheet-parity lines strong, cut-parity
      lines gray (USER ruling 2026-08-16, confirmed after fixing the
      vanishing sheet line) — so every cut boundary is a visible color
      change and needs no marker dot. */
  lineAlt: string
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

type LineKind = 'branch' | 'ring' | 'strand'
type SpriteKind = 'label' | 'pip'

type LineRec = {
  kind: LineKind
  obj: Line2
  geo: LineGeometry
  mat: LineMaterial
  pick: THREE.Line
  pickGeo: THREE.BufferGeometry
  n: number // point count, to detect when setEntities needs a full rebuild
  baseColor: string
}
type SpriteRec = {
  kind: SpriteKind
  obj: THREE.Sprite
  baseTex: THREE.Texture
  hoverTex: THREE.Texture
}

const LINE_W: Record<LineKind, number> = { branch: 3.5, ring: 2.2, strand: 2.2 }
/** Pips live on this extra layer so render() can draw them a second time
    above the bloom composite: the bloom pass is additive, and a filled disc
    receives the blurred copy of its own full-intensity interior — clipping
    the core toward white while only the halo keeps the wire hue. Thin lines
    are unaffected (their blurred energy at their own center is far lower),
    so pips are the one entity that needs the authored color restored. */
const PIP_LAYER = 1
const HOVER_EXTRA_W = 1.2
const PIP_SCALE = 0.14
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
  const tex = new THREE.CanvasTexture(c)
  // Canvas 2D rasterizes in sRGB; the texture must say so or the renderer
  // treats the bytes as linear and the output encode lightens the color.
  tex.colorSpace = THREE.SRGBColorSpace
  return tex
}

function textTexture(text: string, color: string): { tex: THREE.CanvasTexture; w: number; h: number } {
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
  const tex = new THREE.CanvasTexture(c)
  tex.colorSpace = THREE.SRGBColorSpace // canvas 2D rasterizes in sRGB
  return { tex, w: c.width, h: c.height }
}

const isLineEntity = (e: FadedEntity): e is FadedEntity & { kind: LineKind; pts: import('./vec3').Vec3[] } =>
  e.kind === 'branch' || e.kind === 'ring' || e.kind === 'strand'

export function mountRender(container: HTMLElement, theme: RenderTheme): Renderer3 {
  let th = theme
  const renderer = new THREE.WebGLRenderer({ antialias: true, preserveDrawingBuffer: true })
  renderer.setPixelRatio(window.devicePixelRatio)
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
  const raycaster = new THREE.Raycaster()
  raycaster.params.Line = { threshold: PICK_THRESHOLD }
  let size = { w: 1, h: 1 }
  let hoverKeys: ReadonlySet<string> = new Set()
  let lastEntities: readonly FadedEntity[] = []

  const lineRecs = new Map<string, LineRec>()
  const spriteRecs = new Map<string, SpriteRec>()

  const applyBackground = (): void => {
    scene.background = new THREE.Color(th.background)
    const idx = composer.passes.indexOf(bloom)
    if (th.mode === 'dark' && idx === -1) composer.addPass(bloom)
    if (th.mode !== 'dark' && idx !== -1) composer.removePass(bloom)
  }
  applyBackground()

  // Strands stroke in their wire's order hue; an atom's ring strokes in its
  // HEAD wire's hue (matching the 2D painter's bodyStroke); refs (null
  // headWire) and structural entities keep the line color.
  const colorOf = (e: Entity): string => {
    if (e.kind === 'strand') return th.hues.get(e.wire) ?? th.baseWire
    if (e.kind === 'ring' && e.headWire !== null) return th.hues.get(e.headWire) ?? th.baseWire
    if (e.kind === 'pip' && e.ownerWire !== null) return th.hues.get(e.ownerWire) ?? th.baseWire
    if (e.kind === 'branch' && e.polarity === 1) return th.lineAlt
    return th.line
  }

  const disposeLine = (r: LineRec): void => {
    group.remove(r.obj)
    group.remove(r.pick)
    r.geo.dispose()
    r.mat.dispose()
    r.pickGeo.dispose()
  }
  const disposeSprite = (r: SpriteRec): void => {
    group.remove(r.obj)
    r.baseTex.dispose()
    r.hoverTex.dispose()
    ;(r.obj.material as THREE.SpriteMaterial).dispose()
  }

  const makeLine = (e: FadedEntity & { kind: LineKind }): LineRec => {
    const color = colorOf(e)
    const width = LINE_W[e.kind]
    const geo = new LineGeometry()
    geo.setPositions(e.pts.flatMap((p) => [p.x, p.y, p.z]))
    const mat = new LineMaterial({ color, linewidth: width, transparent: true, opacity: e.alpha ?? 1 })
    mat.resolution.set(size.w, size.h)
    const obj = new Line2(geo, mat)
    obj.computeLineDistances()
    obj.userData['key'] = e.key
    group.add(obj)
    const pickGeo = new THREE.BufferGeometry().setFromPoints(e.pts.map((p) => new THREE.Vector3(p.x, p.y, p.z)))
    const pick = new THREE.Line(pickGeo, new THREE.LineBasicMaterial({ visible: false }))
    pick.userData['key'] = e.key
    group.add(pick)
    return { kind: e.kind, obj, geo, mat, pick, pickGeo, n: e.pts.length, baseColor: color }
  }

  const makeSprite = (e: FadedEntity & { kind: SpriteKind }): SpriteRec => {
    const baseColor = colorOf(e)
    if (e.kind === 'pip') {
      // Identity pips render OVER the lines they sit on (USER law
      // 2026-08-15): depth testing off plus a high render order, or the
      // coincident branch line z-fights them into invisibility.
      const baseTex = discTexture(baseColor)
      const hoverTex = discTexture(th.hover)
      const mat = new THREE.SpriteMaterial({ map: baseTex, transparent: true, opacity: e.alpha ?? 1, depthTest: false })
      const obj = new THREE.Sprite(mat)
      obj.renderOrder = 10
      obj.layers.enable(PIP_LAYER) // also stays on layer 0 so the bloom halo survives
      obj.position.set(e.pos.x, e.pos.y, e.pos.z)
      obj.scale.set(PIP_SCALE, PIP_SCALE, 1)
      obj.userData['key'] = e.key
      group.add(obj)
      return { kind: 'pip', obj, baseTex, hoverTex }
    }
    const base = textTexture(e.text, baseColor)
    const hover = textTexture(e.text, th.hover)
    const mat = new THREE.SpriteMaterial({ map: base.tex, transparent: true, opacity: e.alpha ?? 1 })
    const obj = new THREE.Sprite(mat)
    obj.scale.set(0.9 * (base.w / base.h), 0.9, 1)
    obj.position.set(e.pos.x, e.pos.y, e.pos.z)
    obj.userData['key'] = e.key
    group.add(obj)
    return { kind: 'label', obj, baseTex: base.tex, hoverTex: hover.tex }
  }

  // Hover thickens/brightens by swapping material parameters (color,
  // linewidth, sprite texture), never by rebuilding geometry.
  const applyHover = (): void => {
    for (const [key, r] of lineRecs) {
      const hovered = hoverKeys.has(key)
      r.mat.color.set(hovered ? th.hover : r.baseColor)
      r.mat.linewidth = LINE_W[r.kind] + (hovered ? HOVER_EXTRA_W : 0)
    }
    for (const [key, r] of spriteRecs) {
      const hovered = hoverKeys.has(key)
      const mat = r.obj.material as THREE.SpriteMaterial
      mat.map = hovered ? r.hoverTex : r.baseTex
      mat.needsUpdate = true
    }
  }

  const rebuildAll = (list: readonly FadedEntity[]): void => {
    for (const r of lineRecs.values()) disposeLine(r)
    for (const r of spriteRecs.values()) disposeSprite(r)
    lineRecs.clear()
    spriteRecs.clear()
    for (const e of list) {
      if (e.kind === 'label' || e.kind === 'pip') spriteRecs.set(e.key, makeSprite(e))
      else lineRecs.set(e.key, makeLine(e))
    }
    applyHover()
  }

  return {
    setEntities(next) {
      lastEntities = next
      const nextByKey = new Map(next.map((e) => [e.key, e]))
      const curKeys = [...lineRecs.keys(), ...spriteRecs.keys()]
      let compatible = curKeys.length === next.length
      if (compatible) {
        for (const k of curKeys) if (!nextByKey.has(k)) { compatible = false; break }
      }
      if (compatible) {
        for (const [k, e] of nextByKey) {
          const lr = lineRecs.get(k)
          if (lr !== undefined) {
            if (lr.kind !== e.kind || !isLineEntity(e) || e.pts.length !== lr.n) { compatible = false; break }
            continue
          }
          const sr = spriteRecs.get(k)
          if (sr === undefined || sr.kind !== e.kind) { compatible = false; break }
        }
      }
      if (!compatible) { rebuildAll(next); return }
      for (const [k, e] of nextByKey) {
        const lr = lineRecs.get(k)
        if (lr !== undefined && isLineEntity(e)) {
          lr.geo.setPositions(e.pts.flatMap((p) => [p.x, p.y, p.z]))
          lr.obj.computeLineDistances()
          lr.pickGeo.setFromPoints(e.pts.map((p) => new THREE.Vector3(p.x, p.y, p.z)))
          lr.mat.opacity = e.alpha ?? 1
          continue
        }
        const sr = spriteRecs.get(k)!
        if ('pos' in e) sr.obj.position.set(e.pos.x, e.pos.y, e.pos.z)
        ;(sr.obj.material as THREE.SpriteMaterial).opacity = e.alpha ?? 1
      }
    },
    setTheme(next) {
      th = next
      applyBackground()
      rebuildAll(lastEntities) // colors and hover textures depend on the theme
    },
    setPose(p) {
      const eye = eyeOf(p)
      camera.position.set(eye.x, eye.y, eye.z)
      camera.up.set(0, 1, 0)
      camera.lookAt(p.target.x, p.target.y, p.target.z)
    },
    setHoverKeys(keys) { hoverKeys = keys; applyHover() },
    pickAt(ndcX, ndcY) {
      raycaster.setFromCamera(new THREE.Vector2(ndcX, ndcY), camera)
      const objs: THREE.Object3D[] = [
        ...[...lineRecs.values()].map((r) => r.pick),
        ...[...spriteRecs.values()].map((r) => r.obj),
      ]
      const hits = raycaster.intersectObjects(objs, false)
      const key = hits[0]?.object.userData['key']
      return typeof key === 'string' ? key : null
    },
    render() {
      composer.render()
      // With the bloom pass in the chain, redraw the pips over the composite:
      // the composite's disc cores are clipped toward white (see PIP_LAYER),
      // and this pass restores the authored color there while the bloom halo
      // around each disc remains from the composite underneath.
      if (composer.passes.includes(bloom)) {
        const bg = scene.background
        scene.background = null // a background draw ignores layers and would wipe the composite
        renderer.autoClear = false
        camera.layers.set(PIP_LAYER)
        renderer.render(scene, camera)
        camera.layers.set(0)
        renderer.autoClear = true
        scene.background = bg
      }
    },
    resize(w, h) {
      size = { w, h }
      renderer.setPixelRatio(window.devicePixelRatio)
      renderer.setSize(w, h, false)
      composer.setSize(w, h)
      camera.aspect = w / Math.max(1, h)
      camera.updateProjectionMatrix()
      for (const r of lineRecs.values()) r.mat.resolution.set(w, h)
    },
    dispose() {
      for (const r of lineRecs.values()) disposeLine(r)
      for (const r of spriteRecs.values()) disposeSprite(r)
      lineRecs.clear()
      spriteRecs.clear()
      bloom.dispose()
      composer.dispose()
      renderer.dispose()
      renderer.forceContextLoss()
      renderer.domElement.remove()
    },
  }
}
