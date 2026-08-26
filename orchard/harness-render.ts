import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { SMAAPass } from 'three/examples/jsm/postprocessing/SMAAPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import { mountGlowRenderer } from '../src/game/render/glow-render'
import {
  GameTreeRuntime,
  GameWorldLifecycle,
  makeTreeMaterialSource,
  type AntialiasingMethod,
  type GameFrameStats,
  type OrchardBuildStats,
  type RenderMode,
  type RenderTree,
} from '../src/game/render/runtime'
import {
  makeBatchedTreeObject,
  makeMarkerObject,
  makeRawTreeObject,
  type TreeMaterialSource,
} from '../src/game/render/tree-objects'
import type { TreeRenderAsset } from '../src/game/render/types'
import type { OrchardWorldSave, SavedTree, SavedTreeLayout } from './world'

const MAX_PIXEL_RATIO = 1.5

export type StressHarnessRenderer = {
  readonly canvas: HTMLCanvasElement
  setCount(count: number): Promise<OrchardBuildStats>
  setTrees(trees: readonly SavedTree[]): Promise<OrchardBuildStats>
  setMode(mode: RenderMode): void
  setAntialiasing(enabled: boolean): AntialiasingMethod
  setPlayer(x: number, z: number, yaw: number, pitch: number): void
  resize(width: number, height: number): void
  render(): GameFrameStats
  dispose(): void
}

function diagnosticAsset(layout: SavedTreeLayout): TreeRenderAsset {
  if (layout.widths.branch !== 0.10 || layout.widths.curve !== 0.05) {
    throw new Error('stress harness requires production tree widths')
  }
  if (layout.glow.color !== '#ffffff'
    || layout.glow.radius !== 32
    || layout.glow.opacity !== 0.65
    || layout.glow.bloom !== 0.8) {
    throw new Error('stress harness requires production tree glow')
  }
  return {
    bounds: layout.bounds,
    lods: layout.lods,
    hues: layout.hues,
    palette: layout.palette,
    widths: { branch: 0.10, curve: 0.05 },
    glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
  }
}

export function mountStressHarness(
  container: HTMLElement,
  world: OrchardWorldSave,
): StressHarnessRenderer {
  const renderer = new THREE.WebGLRenderer({ antialias: false, powerPreference: 'high-performance' })
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO))
  renderer.outputColorSpace = THREE.SRGBColorSpace
  renderer.shadowMap.enabled = false
  renderer.info.autoReset = false
  renderer.domElement.setAttribute('aria-label', 'Proof-tree renderer stress harness')
  container.appendChild(renderer.domElement)

  const scene = new THREE.Scene()
  scene.background = new THREE.Color(world.terrain.sky)
  scene.fog = new THREE.Fog(world.terrain.sky, world.terrain.fogNear, world.terrain.fogFar)
  const camera = new THREE.PerspectiveCamera(67, 1, 0.08, 1800)
  camera.rotation.order = 'YXZ'
  const composer = new EffectComposer(renderer)
  const bloomPass = new UnrealBloomPass(new THREE.Vector2(1, 1), 0.65, 0.45, 0.55)
  const smaaPass = new SMAAPass(1, 1)
  const outputPass = new OutputPass()
  composer.addPass(new RenderPass(scene, camera))
  composer.addPass(bloomPass)
  composer.addPass(smaaPass)
  composer.addPass(outputPass)
  let antialiasingMethod: AntialiasingMethod = 'smaa'

  const ground = new THREE.Mesh(
    new THREE.PlaneGeometry(world.terrain.size, world.terrain.size),
    new THREE.MeshBasicMaterial({ color: world.terrain.ground }),
  )
  ground.rotation.x = -Math.PI / 2
  ground.position.y = -0.035
  scene.add(ground)
  const glowRenderer = mountGlowRenderer(scene, ground.position.y)
  const activeGlowTiles = new Set<string>()
  const treeObjects = new THREE.Group()
  treeObjects.name = 'separate-proof-trees'
  scene.add(treeObjects)

  const assetsByJson = new Map<string, TreeRenderAsset>()
  const jsonByLayout = new Map<string, string>()
  for (const [layoutId, layout] of Object.entries(world.layouts)) {
    const diagramJson = JSON.stringify(layout)
    jsonByLayout.set(layoutId, diagramJson)
    assetsByJson.set(diagramJson, diagnosticAsset(layout))
  }
  const materialsByAsset = new WeakMap<TreeRenderAsset, TreeMaterialSource>()
  const lineMaterials = new Set<LineMaterial>()
  const textures = new Set<THREE.Texture>()
  const spriteMaterials = new Set<THREE.SpriteMaterial>()
  let size = { width: 1, height: 1 }
  const materialsFor = (asset: TreeRenderAsset): TreeMaterialSource => {
    let materials = materialsByAsset.get(asset)
    if (materials === undefined) {
      materials = makeTreeMaterialSource(
        asset,
        lineMaterials,
        textures,
        spriteMaterials,
        () => size,
      )
      materialsByAsset.set(asset, materials)
    }
    return materials
  }

  const runtime = new GameTreeRuntime(
    (diagramJson) => {
      const asset = assetsByJson.get(diagramJson)
      if (asset === undefined) throw new Error('stress tree asset was not registered')
      return asset
    },
    treeObjects,
    (asset, tree, lod, raw) => {
      const materials = materialsFor(asset)
      if (raw) return makeRawTreeObject(asset, tree.placement, materials)
      if (lod === 'marker') return makeMarkerObject(asset, tree.placement, materials)
      return makeBatchedTreeObject(asset, lod, tree.placement, materials)
    },
  )

  const renderTrees = (trees: readonly SavedTree[]): RenderTree[] => trees.map((tree, index) => ({
    id: tree.id,
    diagramJson: jsonByLayout.get(tree.layout)!,
    placement: { id: tree.id, index, x: tree.x, z: tree.z, yaw: tree.yaw },
  }))
  const setTrees = async (trees: readonly SavedTree[]): Promise<OrchardBuildStats> => (
    runtime.setTrees(renderTrees(trees))
  )

  const syncGlow = (): void => {
    const dirty = runtime.flushGlow()
    for (const record of dirty) {
      if (record.contributors.length === 0) activeGlowTiles.delete(record.key)
      else activeGlowTiles.add(record.key)
    }
    glowRenderer.sync(dirty)
  }
  const resize = (width: number, height: number): void => {
    size = { width, height }
    const pixelRatio = Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO)
    renderer.setPixelRatio(pixelRatio)
    renderer.setSize(width, height, false)
    composer.setPixelRatio(pixelRatio)
    composer.setSize(width, height)
    bloomPass.setSize(width * pixelRatio, height * pixelRatio)
    camera.aspect = width / Math.max(1, height)
    camera.updateProjectionMatrix()
    for (const material of lineMaterials) material.resolution.set(width, height)
  }
  const lifecycle = new GameWorldLifecycle([
    () => runtime.dispose(),
    () => { for (const material of lineMaterials) material.dispose() },
    () => { for (const material of spriteMaterials) material.dispose() },
    () => { for (const texture of textures) texture.dispose() },
    () => glowRenderer.dispose(),
    () => activeGlowTiles.clear(),
    () => ground.geometry.dispose(),
    () => (ground.material as THREE.Material).dispose(),
    () => bloomPass.dispose(),
    () => smaaPass.dispose(),
    () => outputPass.dispose(),
    () => composer.dispose(),
    () => renderer.dispose(),
    () => renderer.domElement.remove(),
  ])

  return {
    canvas: renderer.domElement,
    async setCount(count) {
      if (!Number.isInteger(count) || count < 0 || count > world.trees.length) {
        throw new Error(`tree count must be between 0 and ${world.trees.length}`)
      }
      return setTrees(world.trees.slice(0, count))
    },
    setTrees,
    setMode(mode) {
      runtime.setMode(mode)
    },
    setAntialiasing(enabled) {
      smaaPass.enabled = enabled
      antialiasingMethod = enabled ? 'smaa' : 'off'
      return antialiasingMethod
    },
    setPlayer(x, z, yaw, pitch) {
      camera.position.set(x, world.player.y, z)
      camera.rotation.x = pitch
      camera.rotation.y = yaw
    },
    resize,
    render() {
      const lod = runtime.updateGame(camera, world.terrain.fogFar, size.height)
      const work = runtime.processOperations()
      syncGlow()
      renderer.info.reset()
      composer.render()
      const current = runtime.snapshot()
      return {
        antialiasingMethod,
        drawCalls: renderer.info.render.calls,
        triangles: renderer.info.render.triangles,
        geometries: renderer.info.memory.geometries,
        objects: current.objects,
        instanced: current.instanced,
        logical: current.logical,
        visible: current.visible,
        resident: current.resident,
        full: current.full,
        reduced: current.reduced,
        marker: current.marker,
        culled: current.culled,
        pending: current.pending,
        glowTiles: activeGlowTiles.size,
        pointLights: current.pointLights,
        representedEntities: current.representedEntities,
        representationOperations: work.completed,
        buildMs: current.buildMs,
        lodMs: lod.lodMs,
        error: current.error,
        representationErrors: current.failureCount,
      }
    },
    dispose() {
      lifecycle.dispose()
    },
  }
}
