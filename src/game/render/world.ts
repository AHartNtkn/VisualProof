import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { SMAAPass } from 'three/examples/jsm/postprocessing/SMAAPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { Diagram } from '../../kernel/diagram'
import { diagramToJson } from '../../kernel/diagram'
import type { GameTree } from '../model'
import type { PointedTreePart } from '../session'
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
  pointAtTreeAssets,
  pointAtVisibleParts,
  type EntityKeyFilter,
  type TreeMaterialSource,
} from './tree-objects'
import type { DisplayCameraPose, TreeRenderAsset } from './types'

const MAX_PIXEL_RATIO = 1.5
const TERRAIN_SIZE = 4000
const TERRAIN_COLOR = '#010101'
const SKY_COLOR = '#000000'
const FOG_NEAR = 170
const FOG_FAR = 780
const INTERACTION_REACH = 100

export type GameWorldRenderer = {
  readonly canvas: HTMLCanvasElement
  setTrees(trees: readonly GameTree[]): void
  setCamera(pose: DisplayCameraPose): void
  setRenderMode(mode: RenderMode): void
  pointAt(ndcX: number, ndcY: number, orbitTarget: string | null): PointedTreePart | null
  pointAtBranch(ndcX: number, ndcY: number, orbitTarget: string | null): PointedTreePart | null
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
  renderer.domElement.setAttribute('aria-label', 'Walkable proof-tree game world')
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
  const raycaster = new THREE.Raycaster()

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

  const preparePointRay = (ndcX: number, ndcY: number): void => {
    camera.updateMatrixWorld()
    treeObjects.updateMatrixWorld(true)
    raycaster.setFromCamera(new THREE.Vector2(ndcX, ndcY), camera)
  }

  const assetCandidates = (trees: readonly RenderTree[]) => (
    trees.flatMap((tree) => {
      if (dynamicTrees.objects(tree.id).length > 0) return []
      const asset = assetsByJson.get(tree.diagramJson)
      return asset === undefined ? [] : [{ treeId: tree.id, placement: tree.placement, asset }]
    })
  )

  const closest = (
    dynamic: PointedTreePart | null,
    staticPart: PointedTreePart | null,
  ): PointedTreePart | null => {
    if (dynamic === null) return staticPart
    if (staticPart === null) return dynamic
    return dynamic.distance <= staticPart.distance ? dynamic : staticPart
  }

  const pointAtAny = (
    ndcX: number,
    ndcY: number,
    orbitTarget: string | null,
  ): PointedTreePart | null => {
    preparePointRay(ndcX, ndcY)
    const dynamic = pointAtVisibleParts(
      raycaster,
      dynamicTrees.objects(),
      INTERACTION_REACH,
      orbitTarget,
    )
    const staticPart = pointAtTreeAssets(
      raycaster.ray,
      assetCandidates(runtime.interactionTrees(raycaster.ray, INTERACTION_REACH)),
      INTERACTION_REACH,
      orbitTarget,
    )
    return closest(dynamic, staticPart)
  }

  const pointAtBranch = (
    ndcX: number,
    ndcY: number,
    orbitTarget: string | null,
  ): PointedTreePart | null => {
    preparePointRay(ndcX, ndcY)
    const acceptsBranch: EntityKeyFilter = (entityKey) => entityKey.startsWith('b:')
    const dynamic = pointAtVisibleParts(
      raycaster,
      dynamicTrees.objects(),
      INTERACTION_REACH,
      orbitTarget,
      acceptsBranch,
    )
    const staticBranch = pointAtTreeAssets(
      raycaster.ray,
      assetCandidates(runtime.interactionTrees(raycaster.ray, INTERACTION_REACH)),
      INTERACTION_REACH,
      orbitTarget,
      acceptsBranch,
    )
    return closest(dynamic, staticBranch)
  }

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
    setRenderMode(mode) {
      runtime.setMode(mode)
    },
    pointAt(ndcX, ndcY, orbitTarget) {
      return pointAtAny(ndcX, ndcY, orbitTarget)
    },
    pointAtBranch(ndcX, ndcY, orbitTarget) {
      return pointAtBranch(ndcX, ndcY, orbitTarget)
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
