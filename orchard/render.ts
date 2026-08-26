import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import type { WireId } from '../src/kernel/diagram/diagram'
import type { Entity } from '../src/view3d/scene'
import { mountGlowRenderer } from './glow-render'
import { GlowTilePlan } from './glow-tiles'
import { disposeTreeObject, makeRawTreeObject, type OrchardMaterialSource } from './tree-objects'
import type { OrchardWorldSave, SavedTreeLayout } from './world'

const MAX_PIXEL_RATIO = 1.5

export type OrchardFrameStats = {
  readonly drawCalls: number
  readonly triangles: number
  readonly geometries: number
}

export type OrchardBuildStats = {
  readonly trees: number
  readonly entities: number
  readonly objects: number
  readonly instanced: number
  readonly buildMs: number
}

export type OrchardWorld = {
  readonly canvas: HTMLCanvasElement
  setCount(count: number): Promise<OrchardBuildStats>
  setPlayer(x: number, z: number, yaw: number, pitch: number): void
  resize(width: number, height: number): void
  render(): OrchardFrameStats
  dispose(): void
}

function discTexture(color: string): THREE.CanvasTexture {
  const canvas = document.createElement('canvas')
  canvas.width = canvas.height = 64
  const context = canvas.getContext('2d')!
  context.fillStyle = color
  context.beginPath()
  context.arc(32, 32, 27, 0, Math.PI * 2)
  context.fill()
  const texture = new THREE.CanvasTexture(canvas)
  texture.colorSpace = THREE.SRGBColorSpace
  return texture
}

function textTexture(text: string, color: string): { texture: THREE.CanvasTexture; aspect: number } {
  const canvas = document.createElement('canvas')
  const measure = canvas.getContext('2d')!
  measure.font = '44px Georgia, serif'
  canvas.width = Math.max(2, Math.ceil(measure.measureText(text).width) + 12)
  canvas.height = 64
  const context = canvas.getContext('2d')!
  context.font = '44px Georgia, serif'
  context.fillStyle = color
  context.textBaseline = 'middle'
  context.fillText(text, 6, 32)
  const texture = new THREE.CanvasTexture(canvas)
  texture.colorSpace = THREE.SRGBColorSpace
  return { texture, aspect: canvas.width / canvas.height }
}

function materialsFor(
  layout: SavedTreeLayout,
  lineMaterials: Set<LineMaterial>,
  textures: Set<THREE.Texture>,
  spriteMaterials: Set<THREE.SpriteMaterial>,
  resolution: () => { readonly width: number; readonly height: number },
): OrchardMaterialSource {
  const lines = new Map<string, LineMaterial>()
  const sprites = new Map<string, THREE.SpriteMaterial>()
  const hues = new Map<WireId, string>(layout.hues)
  const colorFor = (entity: Entity): string => {
    if (entity.kind === 'branch') return entity.polarity === 0 ? layout.palette.branch : layout.palette.cutBranch
    if (entity.kind === 'strand') return hues.get(entity.wire) ?? layout.palette.baseWire
    if (entity.kind === 'ring' && entity.headWire !== null) return hues.get(entity.headWire) ?? layout.palette.baseWire
    if (entity.kind === 'pip' && entity.ownerWire !== null) return hues.get(entity.ownerWire) ?? layout.palette.baseWire
    return layout.palette.branch
  }
  const line = (
    entity: Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>,
    width: number,
  ): LineMaterial => {
    const color = colorFor(entity)
    const key = `${entity.kind}:${color}:${width}`
    let material = lines.get(key)
    if (material === undefined) {
      material = new LineMaterial({ color, linewidth: width, worldUnits: true })
      const size = resolution()
      material.resolution.set(size.width, size.height)
      lines.set(key, material)
      lineMaterials.add(material)
    }
    return material
  }
  const marker = (saved: SavedTreeLayout['lods']['marker']): THREE.SpriteMaterial => {
    const key = `marker:${saved.color}`
    let material = sprites.get(key)
    if (material === undefined) {
      const texture = discTexture('#ffffff')
      textures.add(texture)
      material = new THREE.SpriteMaterial({
        map: texture,
        color: saved.color,
        transparent: true,
        blending: THREE.AdditiveBlending,
        depthWrite: false,
      })
      sprites.set(key, material)
      spriteMaterials.add(material)
    }
    return material
  }
  const sprite = (entity: Extract<Entity, { kind: 'pip' | 'label' }>): THREE.SpriteMaterial => {
    const color = colorFor(entity)
    const key = entity.kind === 'label' ? `label:${entity.text}:${color}` : `pip:${color}`
    let material = sprites.get(key)
    if (material === undefined) {
      const authored = entity.kind === 'label' ? textTexture(entity.text, color) : null
      const texture = authored?.texture ?? discTexture(color)
      textures.add(texture)
      material = new THREE.SpriteMaterial({ map: texture, transparent: true, depthTest: entity.kind !== 'pip' })
      if (authored !== null) material.userData['aspect'] = authored.aspect
      sprites.set(key, material)
      spriteMaterials.add(material)
    }
    return material
  }
  return { line, sprite, marker }
}

export function mountOrchardWorld(
  container: HTMLElement,
  world: OrchardWorldSave,
): OrchardWorld {
  const renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'high-performance' })
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO))
  renderer.outputColorSpace = THREE.SRGBColorSpace
  renderer.shadowMap.enabled = false
  renderer.domElement.setAttribute('aria-label', 'Walkable proof-tree orchard')
  container.appendChild(renderer.domElement)

  const scene = new THREE.Scene()
  scene.background = new THREE.Color(world.terrain.sky)
  scene.fog = new THREE.Fog(world.terrain.sky, world.terrain.fogNear, world.terrain.fogFar)
  const camera = new THREE.PerspectiveCamera(67, 1, 0.08, 1800)
  camera.rotation.order = 'YXZ'

  const ground = new THREE.Mesh(
    new THREE.PlaneGeometry(world.terrain.size, world.terrain.size),
    new THREE.MeshBasicMaterial({ color: world.terrain.ground }),
  )
  ground.rotation.x = -Math.PI / 2
  ground.position.y = -0.035
  scene.add(ground)
  const glowPlan = new GlowTilePlan(128)
  const glowRenderer = mountGlowRenderer(scene, ground.position.y)

  const trees = new THREE.Group()
  trees.name = 'separate-proof-trees'
  scene.add(trees)
  const lineMaterials = new Set<LineMaterial>()
  const textures = new Set<THREE.Texture>()
  const spriteMaterials = new Set<THREE.SpriteMaterial>()
  let size = { width: 1, height: 1 }
  const materialsByLayout = new Map<string, OrchardMaterialSource>()
  for (const [layoutId, layout] of Object.entries(world.layouts)) {
    materialsByLayout.set(layoutId, materialsFor(
      layout,
      lineMaterials,
      textures,
      spriteMaterials,
      () => size,
    ))
  }
  const groups: THREE.Group[] = []

  const resize = (width: number, height: number): void => {
    size = { width, height }
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO))
    renderer.setSize(width, height, false)
    camera.aspect = width / Math.max(1, height)
    camera.updateProjectionMatrix()
    for (const material of lineMaterials) material.resolution.set(width, height)
  }

  return {
    canvas: renderer.domElement,
    async setCount(count) {
      const started = performance.now()
      if (!Number.isInteger(count) || count < 0 || count > world.trees.length) {
        throw new Error(`tree count must be between 0 and ${world.trees.length}`)
      }
      while (groups.length > count) {
        const group = groups.pop()!
        glowPlan.remove(group.name)
        trees.remove(group)
        disposeTreeObject(group)
      }
      while (groups.length < count) {
        const end = Math.min(count, groups.length + 12)
        while (groups.length < end) {
          const index = groups.length
          const saved = world.trees[index]!
          const layout = world.layouts[saved.layout]!
          const group = makeRawTreeObject(layout, {
            id: saved.id,
            index,
            x: saved.x,
            z: saved.z,
            yaw: saved.yaw,
          }, materialsByLayout.get(saved.layout)!)
          groups.push(group)
          trees.add(group)
          glowPlan.set({
            id: saved.id,
            x: saved.x,
            z: saved.z,
            radius: layout.glow.radius,
            color: layout.glow.color,
            opacity: layout.glow.opacity,
          })
        }
        if (groups.length < count) await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()))
      }
      glowRenderer.sync(glowPlan.flushDirty())
      let instanced = 0
      let objects = 0
      for (const group of groups) group.traverse((object) => {
        objects++
        if ((object as THREE.InstancedMesh).isInstancedMesh === true) instanced++
      })
      let entities = 0
      for (let index = 0; index < count; index++) {
        const saved = world.trees[index]!
        entities += world.layouts[saved.layout]!.lods.full.entities.length
      }
      return {
        trees: count,
        entities,
        objects,
        instanced,
        buildMs: performance.now() - started,
      }
    },
    setPlayer(x, z, yaw, pitch) {
      camera.position.set(x, world.player.y, z)
      camera.rotation.x = pitch
      camera.rotation.y = yaw
    },
    resize,
    render() {
      renderer.render(scene, camera)
      return {
        drawCalls: renderer.info.render.calls,
        triangles: renderer.info.render.triangles,
        geometries: renderer.info.memory.geometries,
      }
    },
    dispose() {
      for (const group of groups) disposeTreeObject(group)
      for (const material of lineMaterials) material.dispose()
      for (const material of spriteMaterials) material.dispose()
      for (const texture of textures) texture.dispose()
      glowRenderer.dispose()
      ground.geometry.dispose()
      ;(ground.material as THREE.Material).dispose()
      renderer.dispose()
      renderer.domElement.remove()
    },
  }
}
