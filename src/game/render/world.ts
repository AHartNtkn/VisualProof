import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { SMAAPass } from 'three/examples/jsm/postprocessing/SMAAPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { GameTree, TreeTarget } from '../model'
import { snapshotFromDiagram } from '../diagram-snapshot'
import type { PointedTreePart, TreeChange } from '../session'
import { DiagramBuilder } from '../../kernel/diagram/builder'
import { DARK } from '../../view/paint'
import { TreeRenderAssetCache } from './assets'
import { mountGlowRenderer } from './glow-render'
import { localPointToWorld, worldSphere } from './placement'
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
  type EntityFilter,
  type TreeMaterialSource,
} from './tree-objects'
import type { DisplayCameraPose, TreeRenderAsset } from './types'
import type { Entity } from '../../view3d/scene'
import { focusPoint } from '../../view3d/pick'
import type { Vec3 } from '../../view3d/vec3'

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
  pickTree(ndcX: number, ndcY: number): TreeTarget | null
  pickTreeFocus(ndcX: number, ndcY: number, treeId: string): {
    readonly treeId: string
    readonly entity: Entity | null
    readonly worldFocus: Vec3
  } | null
  pointAtBranch(ndcX: number, ndcY: number, orbitTarget: string | null): PointedTreePart | null
  setRenderMode(mode: RenderMode): void
  prepareTreeChange(change: TreeChange): PreparedTreeChange
  commitTreeChange(prepared: PreparedTreeChange): void
  discardTreeChange(prepared: PreparedTreeChange): void
  resize(width: number, height: number): void
  render(now: number): GameFrameStats
  dispose(): void
}

const preparedTreeChange: unique symbol = Symbol('prepared tree change')

export type PreparedTreeChange = {
  readonly [preparedTreeChange]: true
}

type PreparedTreeChangePayload = {
  readonly treeId: string
  readonly before: RenderTree
  readonly after: RenderTree
  readonly target: { readonly target: TreeTarget; readonly sphere: THREE.Sphere }
  readonly beforeAsset: TreeRenderAsset
  readonly afterAsset: TreeRenderAsset
  readonly dynamic: ReturnType<DynamicTreeObjects['prepare']>
}

const blankTreeSnapshot = snapshotFromDiagram(new DiagramBuilder().build())

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
  const preparedPayloads = new WeakMap<PreparedTreeChange, PreparedTreeChangePayload>()
  const outstandingPrepared = new Set<PreparedTreeChange>()
  const preparedByTreeId = new Map<string, PreparedTreeChange>()
  let disposed = false
  const treeRaycaster = new THREE.Raycaster()
  const treeHitPoint = new THREE.Vector3()

  const renderTrees = (trees: readonly GameTree[]): RenderTree[] => trees.map((tree, index) => {
    assetsByJson.set(tree.snapshot.json, assetCache.get(tree.snapshot))
    return {
      id: tree.id,
      diagramJson: tree.snapshot.json,
      placement: { id: tree.id, index, ...tree.placement },
    }
  })

  const setTrees = (trees: readonly GameTree[]): void => {
    discardOutstandingPrepared()
    dynamicTrees.clear()
    const rendered = renderTrees(trees)
    renderTreesById.clear()
    for (const tree of rendered) renderTreesById.set(tree.id, tree)
    logicalTreeTargets.clear()
    for (const tree of rendered) {
      const asset = assetsByJson.get(tree.diagramJson)
      if (asset === undefined) throw new Error('tree render asset was not registered')
      const center = localPointToWorld(asset.bounds.center, tree.placement)
      const target = { treeId: tree.id, center, radius: asset.bounds.radius }
      logicalTreeTargets.set(tree.id, {
        target,
        sphere: worldSphere(asset.bounds, tree.placement),
      })
    }
    runtime.setTrees(rendered)
  }

  const matchesTree = (rendered: RenderTree, tree: GameTree): boolean => {
    return rendered.id === tree.id
      && rendered.diagramJson === tree.snapshot.json
      && rendered.placement.x === tree.placement.x
      && rendered.placement.z === tree.placement.z
      && rendered.placement.yaw === tree.placement.yaw
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
  const discardOutstandingPrepared = (): void => {
    for (const prepared of outstandingPrepared) {
      const payload = preparedPayloads.get(prepared)
      if (payload === undefined) continue
      preparedPayloads.delete(prepared)
      if (preparedByTreeId.get(payload.treeId) === prepared) {
        preparedByTreeId.delete(payload.treeId)
      }
      dynamicTrees.discard(payload.dynamic)
    }
    outstandingPrepared.clear()
  }
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
    () => {
      disposed = true
      discardOutstandingPrepared()
    },
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

  const assetCandidates = (): readonly {
    readonly treeId: string
    readonly placement: RenderTree['placement']
    readonly asset: TreeRenderAsset
  }[] => runtime.interactionTrees(treeRaycaster.ray, INTERACTION_REACH).flatMap((tree) => {
    if (dynamicTrees.objects(tree.id).length > 0) return []
    const asset = assetsByJson.get(tree.diagramJson)
    return asset === undefined ? [] : [{ treeId: tree.id, placement: tree.placement, asset }]
  })

  const closest = (
    dynamic: PointedTreePart | null,
    staticPart: PointedTreePart | null,
  ): PointedTreePart | null => {
    if (dynamic === null) return staticPart
    if (staticPart === null) return dynamic
    return dynamic.distance <= staticPart.distance ? dynamic : staticPart
  }

  const pointAtEntity = (
    ndcX: number,
    ndcY: number,
    orbitTarget: string | null,
    accepts: EntityFilter = () => true,
  ): PointedTreePart | null => {
    treeRaycaster.setFromCamera({ x: ndcX, y: ndcY } as THREE.Vector2, camera)
    const dynamic = pointAtVisibleParts(
      treeRaycaster,
      dynamicTrees.objects(),
      INTERACTION_REACH,
      orbitTarget,
      accepts,
    )
    const staticBranch = pointAtTreeAssets(
      treeRaycaster.ray,
      assetCandidates(),
      INTERACTION_REACH,
      orbitTarget,
      accepts,
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
    pickTreeFocus(ndcX, ndcY, treeId) {
      const rendered = renderTreesById.get(treeId)
      if (rendered === undefined) return null
      const asset = assetsByJson.get(rendered.diagramJson)
      if (asset === undefined) return null
      const pointed = pointAtEntity(ndcX, ndcY, treeId)
      if (pointed === null) {
        return {
          treeId,
          entity: null,
          worldFocus: localPointToWorld(asset.lods.full.center, rendered.placement),
        }
      }
      const entity = asset.lods.full.entities.find(({ key }) => key === pointed.entity.key)
      if (entity === undefined) return null
      const localFocus = focusPoint(entity.key, asset.lods.full.entities)
      if (localFocus === null) return null
      return {
        treeId,
        entity,
        worldFocus: localPointToWorld(localFocus, rendered.placement),
      }
    },
    pointAtBranch(ndcX, ndcY, orbitTarget) {
      return pointAtEntity(ndcX, ndcY, orbitTarget, (entity) => entity.kind === 'branch')
    },
    setRenderMode(mode) {
      runtime.setMode(mode)
    },
    prepareTreeChange(change) {
      if (disposed) throw new Error('game world renderer is disposed')
      if (change.treeId !== change.after.id) throw new Error('tree change identity is inconsistent')
      if (preparedByTreeId.has(change.treeId)) {
        throw new Error(`tree change for '${change.treeId}' is already prepared`)
      }
      let current: RenderTree
      let beforeAsset: TreeRenderAsset
      if (change.kind === 'update') {
        if (change.treeId !== change.before.id) throw new Error('tree change identity is inconsistent')
        const live = renderTreesById.get(change.treeId)
        if (live === undefined || !matchesTree(live, change.before)) {
          throw new Error(`stale tree change for '${change.treeId}'`)
        }
        current = live
        beforeAsset = assetCache.get(change.before.snapshot)
      } else {
        if (renderTreesById.has(change.treeId)) {
          throw new Error(`tree '${change.treeId}' already exists`)
        }
        const indices = [
          ...[...renderTreesById.values()].map(({ placement }) => placement.index),
          ...[...outstandingPrepared].flatMap((prepared) => {
            const payload = preparedPayloads.get(prepared)
            return payload === undefined ? [] : [payload.after.placement.index]
          }),
        ]
        current = {
          id: change.treeId,
          diagramJson: blankTreeSnapshot.json,
          placement: {
            id: change.treeId,
            index: indices.length === 0 ? 0 : Math.max(...indices) + 1,
            ...change.after.placement,
          },
        }
        beforeAsset = assetCache.get(blankTreeSnapshot)
      }
      const afterAsset = assetCache.get(change.after.snapshot)
      const after: RenderTree = {
        id: change.after.id,
        diagramJson: change.after.snapshot.json,
        placement: {
          id: change.after.id,
          index: current.placement.index,
          ...change.after.placement,
        },
      }
      const center = localPointToWorld(afterAsset.bounds.center, after.placement)
      const target = {
        target: { treeId: after.id, center, radius: afterAsset.bounds.radius },
        sphere: worldSphere(afterAsset.bounds, after.placement),
      }
      const dynamic = dynamicTrees.prepare(
        after,
        beforeAsset.lods.full,
        afterAsset.lods.full,
        clock(),
        (snapshot, tree) => makeDynamicTreeObject(
          snapshot,
          tree.placement,
          materialsFor(afterAsset),
        ),
      )
      const payload: PreparedTreeChangePayload = {
        treeId: change.treeId,
        before: current,
        after,
        target,
        beforeAsset,
        afterAsset,
        dynamic,
      }
      const prepared: PreparedTreeChange = { [preparedTreeChange]: true }
      preparedPayloads.set(prepared, payload)
      outstandingPrepared.add(prepared)
      preparedByTreeId.set(change.treeId, prepared)
      return prepared
    },
    commitTreeChange(prepared) {
      const payload = preparedPayloads.get(prepared)
      if (payload === undefined || disposed) return
      preparedPayloads.delete(prepared)
      outstandingPrepared.delete(prepared)
      if (preparedByTreeId.get(payload.treeId) === prepared) preparedByTreeId.delete(payload.treeId)
      assetsByJson.set(payload.before.diagramJson, payload.beforeAsset)
      assetsByJson.set(payload.after.diagramJson, payload.afterAsset)
      dynamicTrees.commit(payload.dynamic)
      renderTreesById.set(payload.treeId, payload.after)
      // Logical selection follows the authoritative after-tree immediately;
      // the dynamic tween is presentation of that already-committed state.
      logicalTreeTargets.set(payload.treeId, payload.target)
    },
    discardTreeChange(prepared) {
      const payload = preparedPayloads.get(prepared)
      if (payload === undefined) return
      preparedPayloads.delete(prepared)
      outstandingPrepared.delete(prepared)
      if (preparedByTreeId.get(payload.treeId) === prepared) preparedByTreeId.delete(payload.treeId)
      dynamicTrees.discard(payload.dynamic)
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
