import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { SMAAPass } from 'three/examples/jsm/postprocessing/SMAAPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { Diagram } from '../../kernel/diagram'
import { diagramToJson } from '../../kernel/diagram'
import type { GameTree, TreeTarget } from '../model'
import { DARK } from '../../view/paint'
import { TreeRenderAssetCache } from './assets'
import { mountGlowRenderer } from './glow-render'
import {
  GameTreeRuntime,
  GameWorldLifecycle,
  makeTreeMaterialSource,
  type GameFrameStats,
  type RenderMode,
  type RenderTree,
} from './runtime'
import {
  DynamicTreeObjects,
} from './dynamic-tree'
import {
  makeBatchedTreeObject,
  makeDynamicTreeObject,
  makeMarkerObject,
  makeRawTreeObject,
  type TreeMaterialSource,
} from './tree-objects'
import type { DisplayCameraPose, TreeRenderAsset } from './types'

const MAX_PIXEL_RATIO = 1.5
const TERRAIN_SIZE = 4000
const TERRAIN_COLOR = '#010101'
const SKY_COLOR = '#000000'
const FOG_NEAR = 170
const FOG_FAR = 780

export type GameWorldRenderer = {
  readonly canvas: HTMLCanvasElement
  setTrees(trees: readonly GameTree[]): void
  setCamera(pose: DisplayCameraPose): void
  pickTree(ndcX: number, ndcY: number): TreeTarget | null
  setRenderMode(mode: RenderMode): void
  beginTreeTween(treeId: string, before: Diagram, after: Diagram): void
  resize(width: number, height: number): void
  render(now: number): GameFrameStats
  dispose(): void
}

export function mountGameWorld(
  container: HTMLElement,
  initialTrees: readonly GameTree[],
  clock: () => number = () => performance.now(),
): GameWorldRenderer {
  const renderer = new THREE.WebGLRenderer({ antialias: false, powerPreference: 'high-performance' })
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO))
  renderer.outputColorSpace = THREE.SRGBColorSpace
  renderer.shadowMap.enabled = false
  renderer.info.autoReset = false
  renderer.domElement.setAttribute('aria-label', 'Proof-tree orchard view')
  container.appendChild(renderer.domElement)

  const scene = new THREE.Scene()
  scene.background = new THREE.Color(SKY_COLOR)
  scene.fog = new THREE.Fog(SKY_COLOR, FOG_NEAR, FOG_FAR)
  const camera = new THREE.PerspectiveCamera(67, 1, 0.08, 1800)
  const composer = new EffectComposer(renderer)
  const renderPass = new RenderPass(scene, camera)
  const bloomPass = new UnrealBloomPass(new THREE.Vector2(1, 1), 0.65, 0.45, 0.55)
  const smaaPass = new SMAAPass(1, 1)
  const outputPass = new OutputPass()
  composer.addPass(renderPass)
  composer.addPass(bloomPass)
  composer.addPass(smaaPass)
  composer.addPass(outputPass)

  const ground = new THREE.Mesh(
    new THREE.PlaneGeometry(TERRAIN_SIZE, TERRAIN_SIZE),
    new THREE.MeshBasicMaterial({ color: TERRAIN_COLOR }),
  )
  ground.rotation.x = -Math.PI / 2
  ground.position.y = -0.035
  scene.add(ground)
  const glowRenderer = mountGlowRenderer(scene, ground.position.y)
  const activeGlowTiles = new Set<string>()

  const treeObjects = new THREE.Group()
  treeObjects.name = 'separate-proof-trees'
  scene.add(treeObjects)
  const assetCache = new TreeRenderAssetCache(DARK)
  const assetsByJson = new Map<string, TreeRenderAsset>()
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
      if (asset === undefined) throw new Error('tree render asset was not registered')
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
  const renderTreesById = new Map<string, RenderTree>()
  const logicalTreeTargets = new Map<string, { readonly target: TreeTarget; readonly sphere: THREE.Sphere }>()
  const treeRaycaster = new THREE.Raycaster()
  const treeHitPoint = new THREE.Vector3()

  const renderTrees = (trees: readonly GameTree[]): RenderTree[] => trees.map((tree, index) => {
    assetsByJson.set(tree.diagramJson, assetCache.get(tree.diagramJson, tree.diagram))
    return {
      id: tree.id,
      diagramJson: tree.diagramJson,
      placement: { id: tree.id, index, ...tree.placement },
    }
  })

  const setTrees = (trees: readonly GameTree[]): void => {
    dynamicTrees.clear()
    const rendered = renderTrees(trees)
    renderTreesById.clear()
    for (const tree of rendered) renderTreesById.set(tree.id, tree)
    logicalTreeTargets.clear()
    for (const tree of rendered) {
      const asset = assetsByJson.get(tree.diagramJson)
      if (asset === undefined) throw new Error('tree render asset was not registered')
      const local = asset.bounds.center
      const cosine = Math.cos(tree.placement.yaw)
      const sine = Math.sin(tree.placement.yaw)
      const center = {
        x: tree.placement.x + local.x * cosine + local.z * sine,
        y: local.y,
        z: tree.placement.z - local.x * sine + local.z * cosine,
      }
      const target = { treeId: tree.id, center, radius: asset.bounds.radius }
      logicalTreeTargets.set(tree.id, {
        target,
        sphere: new THREE.Sphere(new THREE.Vector3(center.x, center.y, center.z), target.radius),
      })
    }
    runtime.setTrees(rendered)
  }

  const dynamicTrees = new DynamicTreeObjects(
    treeObjects,
    runtime,
    (snapshot, tree) => {
      const asset = assetsByJson.get(tree.diagramJson)
      if (asset === undefined) throw new Error('dynamic tree render asset was not registered')
      return makeDynamicTreeObject(snapshot, tree.placement, materialsFor(asset))
    },
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
    () => dynamicTrees.dispose(),
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

  setTrees(initialTrees)

  return {
    canvas: renderer.domElement,
    setTrees,
    setCamera(pose) {
      camera.position.set(pose.eye.x, pose.eye.y, pose.eye.z)
      camera.lookAt(
        pose.eye.x + pose.forward.x,
        pose.eye.y + pose.forward.y,
        pose.eye.z + pose.forward.z,
      )
    },
    pickTree(ndcX, ndcY) {
      treeRaycaster.setFromCamera({ x: ndcX, y: ndcY } as THREE.Vector2, camera)
      let nearest: TreeTarget | null = null
      let nearestDistanceSquared = Number.POSITIVE_INFINITY
      for (const { target, sphere } of logicalTreeTargets.values()) {
        if (treeRaycaster.ray.intersectSphere(sphere, treeHitPoint) === null) continue
        const distanceSquared = treeRaycaster.ray.origin.distanceToSquared(treeHitPoint)
        if (distanceSquared < nearestDistanceSquared) {
          nearest = target
          nearestDistanceSquared = distanceSquared
        }
      }
      return nearest
    },
    setRenderMode(mode) {
      runtime.setMode(mode)
    },
    beginTreeTween(treeId, before, after) {
      const current = renderTreesById.get(treeId)
      if (current === undefined) throw new Error(`unknown rendered tree '${treeId}'`)
      const beforeJson = JSON.stringify(diagramToJson(before))
      const afterJson = JSON.stringify(diagramToJson(after))
      const beforeAsset = assetCache.get(beforeJson, before)
      const afterAsset = assetCache.get(afterJson, after)
      assetsByJson.set(beforeJson, beforeAsset)
      assetsByJson.set(afterJson, afterAsset)
      const target = { ...current, diagramJson: afterJson }
      renderTreesById.set(treeId, target)
      dynamicTrees.begin(target, beforeAsset.lods.full, afterAsset.lods.full, clock())
    },
    resize,
    render(now) {
      dynamicTrees.update(now)
      const lod = runtime.updateGame(camera, FOG_FAR, size.height)
      const representationWork = runtime.processOperations()
      syncGlow()
      renderer.info.reset()
      composer.render()
      const current = runtime.snapshot()
      return {
        antialiasingMethod: 'smaa',
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
        representationOperations: representationWork.completed,
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
