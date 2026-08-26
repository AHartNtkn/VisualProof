import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import type { WireId } from '../../kernel/diagram/diagram'
import type { Entity } from '../../view3d/scene'
import { GlowTilePlan, type DirtyGlowTile } from './glow-tiles'
import { projectedDiameterPx, selectLod, type LodLevel } from './lod-policy'
import { SpatialIndex } from './spatial-index'
import { disposeTreeObject, type TreeMaterialSource } from './tree-objects'
import type { TreePlacement } from './placement'
import type { TreeLodAssets, TreeRenderAsset } from './types'

const MAX_REPRESENTATION_OPERATIONS = 12
const SPATIAL_CELL_SIZE = 128

export type RenderMode = 'game' | 'raw'
export type AntialiasingMethod = 'smaa' | 'off'
type ResidentLod = Exclude<LodLevel, 'culled'>

export type GameFrameStats = {
  readonly antialiasingMethod: AntialiasingMethod
  readonly drawCalls: number
  readonly triangles: number
  readonly geometries: number
  readonly objects: number
  readonly instanced: number
  readonly logical: number
  readonly visible: number
  readonly resident: number
  readonly full: number
  readonly reduced: number
  readonly marker: number
  readonly culled: number
  readonly pending: number
  readonly glowTiles: number
  readonly pointLights: number
  readonly representedEntities: number
  readonly representationOperations: number
  readonly buildMs: number
  readonly lodMs: number
  readonly error: string | null
  readonly representationErrors: number
}

export type OrchardBuildStats = {
  readonly trees: number
  readonly entities: number
  readonly objects: number
  readonly instanced: number
  readonly buildMs: number
}

export type RenderTree = {
  readonly id: string
  readonly diagramJson: string
  readonly placement: TreePlacement
}

export type TreeObjectBuilder = (
  asset: TreeRenderAsset,
  tree: RenderTree,
  lod: ResidentLod,
  raw: boolean,
) => THREE.Group

type TreeRenderState = {
  tree: RenderTree
  asset: TreeRenderAsset
  sphere: THREE.Sphere
  desired: LodLevel
  resident: LodLevel
  object: THREE.Group | null
  objectNodes: number
  objectInstanced: number
  objectPointLights: number
  representedEntities: number
  queued: boolean
  operationNode: RepresentationOperationNode | null
  active: boolean
  suspended: boolean
  needsReplacement: boolean
}

type SpatialTree = {
  readonly id: string
  readonly x: number
  readonly z: number
  readonly state: TreeRenderState
}

type RepresentationOperation =
  | { readonly kind: 'state'; readonly state: TreeRenderState }
  | { readonly kind: 'retired'; readonly object: THREE.Group }

type RepresentationOperationNode = {
  readonly operation: RepresentationOperation
  previous: RepresentationOperationNode | null
  next: RepresentationOperationNode | null
}

type RepresentationFailure = {
  readonly desired: LodLevel
  readonly message: string
}

export type RepresentationWork = {
  readonly completed: number
  readonly examined: number
}

export class GameWorldLifecycle {
  private disposed = false

  public constructor(private readonly releases: readonly (() => void)[]) {}

  public dispose(): void {
    if (this.disposed) return
    this.disposed = true
    for (const release of this.releases) release()
  }
}

export type TreeRuntimeSnapshot = {
  readonly logical: number
  readonly logicalEntities: number
  readonly visible: number
  readonly resident: number
  readonly full: number
  readonly reduced: number
  readonly marker: number
  readonly culled: number
  readonly pending: number
  readonly objects: number
  readonly instanced: number
  readonly pointLights: number
  readonly representedEntities: number
  readonly buildMs: number
  readonly error: string | null
  readonly failureCount: number
}

export function treeWorldSphere(tree: RenderTree, asset: TreeRenderAsset): THREE.Sphere {
  const center = new THREE.Vector3(
    asset.bounds.center.x,
    asset.bounds.center.y,
    asset.bounds.center.z,
  )
  center.applyAxisAngle(new THREE.Vector3(0, 1, 0), tree.placement.yaw)
  center.x += tree.placement.x
  center.z += tree.placement.z
  return new THREE.Sphere(center, asset.bounds.radius)
}

function objectCardinality(object: THREE.Group): {
  readonly nodes: number
  readonly instanced: number
  readonly pointLights: number
} {
  let nodes = 0
  let instanced = 0
  let pointLights = 0
  object.traverse((child) => {
    nodes++
    if ((child as THREE.InstancedMesh).isInstancedMesh === true) instanced++
    if ((child as THREE.PointLight).isPointLight === true) pointLights++
  })
  return { nodes, instanced, pointLights }
}

function sameRenderTree(left: RenderTree, right: RenderTree): boolean {
  return left.diagramJson === right.diagramJson
    && left.placement.index === right.placement.index
    && left.placement.x === right.placement.x
    && left.placement.z === right.placement.z
    && left.placement.yaw === right.placement.yaw
}

export type LodUpdate = { readonly visited: number; readonly lodMs: number }

export type GameTreeRuntimeApi = {
  setTrees(trees: readonly RenderTree[]): OrchardBuildStats
  suspend(treeId: string): void
  resume(tree: RenderTree): void
  residentObjects(treeId?: string): readonly THREE.Object3D[]
  updateGame(camera: THREE.PerspectiveCamera, fogFar: number, viewportHeight: number): LodUpdate
  processOperations(budget?: number): RepresentationWork
}

export class GameTreeRuntime implements GameTreeRuntimeApi {
  private readonly states = new Map<string, TreeRenderState>()
  private readonly spatial = new SpatialIndex<SpatialTree>(SPATIAL_CELL_SIZE)
  private readonly glowPlan = new GlowTilePlan(SPATIAL_CELL_SIZE)
  private operationHead: RepresentationOperationNode | null = null
  private operationTail: RepresentationOperationNode | null = null
  private readonly tracked = new Set<TreeRenderState>()
  private readonly failures = new Map<string, RepresentationFailure>()
  private maxRadius = 0
  private readonly lodCounts: Record<LodLevel, number> = { full: 0, reduced: 0, marker: 0, culled: 0 }
  private mode: RenderMode = 'game'
  private logicalEntities = 0
  private pending = 0
  private resident = 0
  private objects = 0
  private instanced = 0
  private pointLights = 0
  private representedEntities = 0
  private buildMs = 0
  private disposed = false

  public constructor(
    private readonly resolveAsset: (diagramJson: string) => TreeRenderAsset,
    private readonly parent: THREE.Group,
    private readonly buildObject: TreeObjectBuilder,
    private readonly releaseObject: (object: THREE.Group) => void = disposeTreeObject,
  ) {}

  public setTrees(trees: readonly RenderTree[]): OrchardBuildStats {
    this.assertActive()
    const started = performance.now()
    const incoming = new Map<string, { readonly tree: RenderTree; readonly asset: TreeRenderAsset }>()
    trees.forEach((tree) => {
      if (incoming.has(tree.id)) throw new Error(`duplicate active tree id '${tree.id}'`)
      if (tree.placement.id !== tree.id) {
        throw new Error(`tree '${tree.id}' placement id must match its tree id`)
      }
      incoming.set(tree.id, { tree, asset: this.resolveAsset(tree.diagramJson) })
    })

    for (const [id, state] of this.states) {
      if (!incoming.has(id)) this.removeState(state)
    }

    for (const { tree, asset } of incoming.values()) {
      const current = this.states.get(tree.id)
      if (current === undefined) this.insertState(tree, asset)
      else this.updateState(current, tree, asset)
    }
    this.recomputeMaxRadius()

    return {
      trees: this.states.size,
      entities: this.logicalEntities,
      objects: this.objects,
      instanced: this.instanced,
      buildMs: performance.now() - started,
    }
  }

  public setMode(mode: RenderMode): void {
    this.assertActive()
    if (mode === this.mode) return
    this.mode = mode
    for (const state of this.states.values()) {
      this.clearFailure(state)
      this.setDesired(state, mode === 'raw' ? 'full' : 'culled')
      this.enqueueState(state, true)
    }
  }

  public getMode(): RenderMode {
    return this.mode
  }

  public suspend(treeId: string): void {
    this.assertActive()
    const state = this.states.get(treeId)
    if (state === undefined || state.suspended) return
    state.suspended = true
    this.cancelStateOperation(state)
    this.detachResidentObject(state)
    this.tracked.delete(state)
  }

  public resume(tree: RenderTree): void {
    this.assertActive()
    if (tree.placement.id !== tree.id) {
      throw new Error(`tree '${tree.id}' placement id must match its tree id`)
    }
    const asset = this.resolveAsset(tree.diagramJson)
    const state = this.states.get(tree.id)
    if (state === undefined) {
      this.insertState(tree, asset)
      this.recomputeMaxRadius()
      return
    }
    this.updateState(state, tree, asset)
    state.suspended = false
    this.recomputeMaxRadius()
    if (state.object !== null
      && !state.needsReplacement
      && state.resident === state.desired
      && state.desired !== 'culled') {
      this.attachResidentObject(state)
      return
    }
    if (state.desired !== 'culled' || state.needsReplacement) this.enqueueState(state)
  }

  public residentObjects(treeId?: string): readonly THREE.Object3D[] {
    this.assertActive()
    if (treeId !== undefined) {
      const object = this.states.get(treeId)?.object
      return object?.parent === this.parent ? [object] : []
    }
    return [...this.states.values()]
      .map(({ object }) => object)
      .filter((object): object is THREE.Group => object?.parent === this.parent)
  }

  public updateGame(
    camera: THREE.PerspectiveCamera,
    fogFar: number,
    viewportHeight: number,
  ): LodUpdate {
    this.assertActive()
    const started = performance.now()
    if (this.mode !== 'game') return { visited: 0, lodMs: performance.now() - started }

    camera.updateMatrixWorld()
    const projectionView = new THREE.Matrix4().multiplyMatrices(camera.projectionMatrix, camera.matrixWorldInverse)
    const frustum = new THREE.Frustum().setFromProjectionMatrix(projectionView)
    const reach = fogFar + this.maxRadius
    const candidates = this.spatial.query({
      minX: camera.position.x - reach,
      maxX: camera.position.x + reach,
      minZ: camera.position.z - reach,
      maxZ: camera.position.z + reach,
    })
    const candidateStates = new Set(candidates.map(({ state }) => state))
    const visitedStates = new Set(this.tracked)
    for (const state of candidateStates) visitedStates.add(state)
    const cameraSpace = new THREE.Vector3()
    const verticalFov = THREE.MathUtils.degToRad(camera.fov)

    for (const state of visitedStates) {
      if (!state.active || state.suspended) continue
      let desired: LodLevel = 'culled'
      if (candidateStates.has(state)) {
        const inFog = state.sphere.distanceToPoint(camera.position) <= fogFar
        const inView = inFog && frustum.intersectsSphere(state.sphere)
        cameraSpace.copy(state.sphere.center).applyMatrix4(camera.matrixWorldInverse)
        const pixels = projectedDiameterPx(state.sphere.radius, -cameraSpace.z, viewportHeight, verticalFov)
        desired = selectLod(state.desired, pixels, inView)
      }
      this.setDesired(state, desired)
      this.enqueueState(state)
      this.pruneTracked(state)
    }

    return { visited: visitedStates.size, lodMs: performance.now() - started }
  }

  public processOperations(requestedBudget = MAX_REPRESENTATION_OPERATIONS): RepresentationWork {
    this.assertActive()
    const started = performance.now()
    const budget = Math.min(MAX_REPRESENTATION_OPERATIONS, Math.max(0, Math.trunc(requestedBudget)))
    let completed = 0
    let examined = 0
    while (completed < budget && examined < budget && this.operationHead !== null) {
      const operation = this.shiftOperation()
      examined++
      if (operation.kind === 'retired') {
        this.pending--
        this.releaseObject(operation.object)
        completed++
        continue
      }
      const state = operation.state
      state.queued = false
      state.operationNode = null
      this.pending--
      this.replaceStateObject(state)
      completed++
      this.pruneTracked(state)
    }
    this.buildMs = performance.now() - started
    return { completed, examined }
  }

  public flushGlow(): DirtyGlowTile[] {
    this.assertActive()
    return this.glowPlan.flushDirty()
  }

  public snapshot(): TreeRuntimeSnapshot {
    const firstFailure = this.failures.entries().next().value as readonly [string, RepresentationFailure] | undefined
    return {
      logical: this.states.size,
      logicalEntities: this.logicalEntities,
      visible: this.states.size - this.lodCounts.culled,
      resident: this.resident,
      full: this.lodCounts.full,
      reduced: this.lodCounts.reduced,
      marker: this.lodCounts.marker,
      culled: this.lodCounts.culled,
      pending: this.pending,
      objects: this.objects,
      instanced: this.instanced,
      pointLights: this.pointLights,
      representedEntities: this.representedEntities,
      buildMs: this.buildMs,
      error: firstFailure === undefined
        ? null
        : `tree '${firstFailure[0]}' ${firstFailure[1].desired} representation failed: ${firstFailure[1].message}`,
      failureCount: this.failures.size,
    }
  }

  public dispose(): void {
    if (this.disposed) return
    this.disposed = true
    const objects = new Set<THREE.Group>()
    for (const state of this.states.values()) {
      if (state.object !== null) objects.add(state.object)
      state.object?.removeFromParent()
      state.object = null
      state.active = false
      state.queued = false
    }
    for (let node = this.operationHead; node !== null; node = node.next) {
      if (node.operation.kind === 'retired') objects.add(node.operation.object)
    }
    this.operationHead = null
    this.operationTail = null
    this.pending = 0
    for (const object of objects) this.releaseObject(object)
    this.states.clear()
    this.tracked.clear()
    this.failures.clear()
    this.resident = 0
    this.objects = 0
    this.instanced = 0
    this.pointLights = 0
    this.representedEntities = 0
  }

  private insertState(tree: RenderTree, asset: TreeRenderAsset): void {
    const desired: LodLevel = this.mode === 'raw' ? 'full' : 'culled'
    const state: TreeRenderState = {
      tree,
      asset,
      sphere: treeWorldSphere(tree, asset),
      desired,
      resident: 'culled',
      object: null,
      objectNodes: 0,
      objectInstanced: 0,
      objectPointLights: 0,
      representedEntities: 0,
      queued: false,
      operationNode: null,
      active: true,
      suspended: false,
      needsReplacement: false,
    }
    this.states.set(tree.id, state)
    this.lodCounts[desired]++
    this.logicalEntities += asset.lods.full.entities.length
    this.indexState(state)
    this.setGlow(state)
    if (desired !== 'culled') this.enqueueState(state)
  }

  private updateState(state: TreeRenderState, tree: RenderTree, asset: TreeRenderAsset): void {
    const previous = state.tree
    const previousAsset = state.asset
    const assetChanged = previous.diagramJson !== tree.diagramJson
    if (sameRenderTree(previous, tree)) {
      if (state.object !== null) this.applyPlacement(state.object, tree)
      return
    }

    state.tree = tree
    state.asset = asset
    state.sphere = treeWorldSphere(tree, asset)
    this.clearFailure(state)
    this.indexState(state)
    this.setGlow(state)
    if (assetChanged) {
      this.logicalEntities += asset.lods.full.entities.length - previousAsset.lods.full.entities.length
      state.needsReplacement = true
      this.detachResidentObject(state)
      if (!state.suspended) this.enqueueState(state)
    } else if (state.object !== null) {
      this.applyPlacement(state.object, tree)
    } else if (!state.suspended && state.desired !== 'culled') {
      this.enqueueState(state)
    }
  }

  private removeState(state: TreeRenderState): void {
    this.states.delete(state.tree.id)
    this.spatial.remove(state.tree.id)
    this.glowPlan.remove(state.tree.id)
    this.logicalEntities -= state.asset.lods.full.entities.length
    this.lodCounts[state.desired]--
    this.clearFailure(state)
    state.active = false
    this.cancelStateOperation(state)
    this.tracked.delete(state)
    if (state.object !== null) {
      this.detachResidentObject(state)
      const object = state.object
      state.object = null
      state.resident = 'culled'
      this.appendOperation({ kind: 'retired', object })
      this.pending++
    }
  }

  private indexState(state: TreeRenderState): void {
    this.spatial.insert({
      id: state.tree.id,
      x: state.sphere.center.x,
      z: state.sphere.center.z,
      state,
    })
  }

  private setGlow(state: TreeRenderState): void {
    const glow = state.asset.glow
    this.glowPlan.set({
      id: state.tree.id,
      x: state.tree.placement.x,
      z: state.tree.placement.z,
      radius: glow.radius,
      color: glow.color,
      opacity: glow.opacity,
    })
  }

  private setDesired(state: TreeRenderState, desired: LodLevel): void {
    if (state.desired === desired) return
    this.lodCounts[state.desired]--
    state.desired = desired
    this.lodCounts[desired]++
    this.clearFailure(state)
    this.detachResidentObject(state)
    if (!state.suspended) this.tracked.add(state)
  }

  private enqueueState(state: TreeRenderState, force = false): void {
    if (!state.active) return
    if (force) {
      state.needsReplacement = true
      this.detachResidentObject(state)
    }
    if (state.queued) return
    if (!state.needsReplacement && state.resident === state.desired && state.object !== null) return
    if (!state.needsReplacement && state.desired === 'culled' && state.object === null) return
    if (state.suspended) return
    if (!force && this.failures.get(state.tree.id)?.desired === state.desired) return
    state.queued = true
    state.operationNode = this.appendOperation({ kind: 'state', state })
    this.pending++
    this.tracked.add(state)
  }

  private cancelStateOperation(state: TreeRenderState): void {
    if (!state.queued) return
    state.queued = false
    this.removeOperation(state.operationNode!)
    state.operationNode = null
    this.pending--
  }

  private appendOperation(operation: RepresentationOperation): RepresentationOperationNode {
    const node: RepresentationOperationNode = {
      operation,
      previous: this.operationTail,
      next: null,
    }
    if (this.operationTail === null) this.operationHead = node
    else this.operationTail.next = node
    this.operationTail = node
    return node
  }

  private shiftOperation(): RepresentationOperation {
    const node = this.operationHead!
    this.removeOperation(node)
    return node.operation
  }

  private removeOperation(node: RepresentationOperationNode): void {
    if (node.previous === null) this.operationHead = node.next
    else node.previous.next = node.next
    if (node.next === null) this.operationTail = node.previous
    else node.next.previous = node.previous
    node.previous = null
    node.next = null
  }

  private detachResidentObject(state: TreeRenderState): void {
    if (state.object === null || state.representedEntities === 0 && state.object.parent === null) return
    state.object.visible = false
    state.object.removeFromParent()
    if (state.objectNodes > 0) {
      this.objects -= state.objectNodes
      this.instanced -= state.objectInstanced
      this.pointLights -= state.objectPointLights
      this.resident--
      this.representedEntities -= state.representedEntities
      state.objectNodes = 0
      state.objectInstanced = 0
      state.objectPointLights = 0
      state.representedEntities = 0
    }
  }

  private replaceStateObject(state: TreeRenderState): void {
    if (state.object !== null) {
      this.detachResidentObject(state)
      this.releaseObject(state.object)
      state.object = null
      state.resident = 'culled'
    }
    state.needsReplacement = false
    if (state.desired === 'culled' || state.suspended) return
    try {
      const object = this.buildObject(
        state.asset,
        state.tree,
        state.desired,
        this.mode === 'raw',
      )
      this.applyPlacement(object, state.tree)
      object.visible = true
      this.parent.add(object)
      const cardinality = objectCardinality(object)
      state.object = object
      state.resident = state.desired
      state.objectNodes = cardinality.nodes
      state.objectInstanced = cardinality.instanced
      state.objectPointLights = cardinality.pointLights
      state.representedEntities = state.desired === 'marker'
        ? 0
        : state.asset.lods[state.desired].entities.length
      this.resident++
      this.objects += cardinality.nodes
      this.instanced += cardinality.instanced
      this.pointLights += cardinality.pointLights
      this.representedEntities += state.representedEntities
      this.clearFailure(state)
    } catch (error) {
      this.failures.set(state.tree.id, {
        desired: state.desired,
        message: error instanceof Error ? error.message : String(error),
      })
    }
  }

  private clearFailure(state: TreeRenderState): void {
    this.failures.delete(state.tree.id)
  }

  private applyPlacement(object: THREE.Group, tree: RenderTree): void {
    object.position.set(tree.placement.x, 0, tree.placement.z)
    object.rotation.y = tree.placement.yaw
    object.userData['treeId'] = tree.id
    object.userData['treeIndex'] = tree.placement.index
    object.traverse((child) => {
      if (child === object) return
      child.userData['treeId'] = tree.id
      child.userData['treeIndex'] = tree.placement.index
    })
  }

  private attachResidentObject(state: TreeRenderState): void {
    const object = state.object
    if (object === null || object.parent === this.parent || state.resident === 'culled') return
    object.visible = true
    this.parent.add(object)
    const cardinality = objectCardinality(object)
    state.objectNodes = cardinality.nodes
    state.objectInstanced = cardinality.instanced
    state.objectPointLights = cardinality.pointLights
    state.representedEntities = state.resident === 'marker'
      ? 0
      : state.asset.lods[state.resident].entities.length
    this.resident++
    this.objects += cardinality.nodes
    this.instanced += cardinality.instanced
    this.pointLights += cardinality.pointLights
    this.representedEntities += state.representedEntities
  }

  private recomputeMaxRadius(): void {
    this.maxRadius = [...this.states.values()].reduce(
      (maximum, state) => Math.max(maximum, state.asset.bounds.radius),
      0,
    )
  }

  private pruneTracked(state: TreeRenderState): void {
    if (state.active
      && !state.suspended
      && (state.desired !== 'culled' || state.object !== null || state.queued)) return
    this.tracked.delete(state)
  }

  private assertActive(): void {
    if (this.disposed) throw new Error('game tree runtime is disposed')
  }
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

/** Authored bloom is a bounded radiance contribution: multiplier = 1 + bloom, for [1, 2]× color. */
function bloomRadiance(color: string, bloom: number): THREE.Color {
  return new THREE.Color(color).multiplyScalar(1 + bloom)
}

export function makeTreeMaterialSource(
  asset: TreeRenderAsset,
  lineMaterials: Set<LineMaterial>,
  textures: Set<THREE.Texture>,
  spriteMaterials: Set<THREE.SpriteMaterial>,
  resolution: () => { readonly width: number; readonly height: number },
): TreeMaterialSource {
  const lines = new Map<string, LineMaterial>()
  const sprites = new Map<string, THREE.SpriteMaterial>()
  const hues = new Map<WireId, string>(asset.hues)
  const colorFor = (entity: Entity): string => {
    if (entity.kind === 'branch') return entity.polarity === 0 ? asset.palette.branch : asset.palette.cutBranch
    if (entity.kind === 'strand') return hues.get(entity.wire) ?? asset.palette.baseWire
    if (entity.kind === 'ring' && entity.headWire !== null) return hues.get(entity.headWire) ?? asset.palette.baseWire
    if (entity.kind === 'pip' && entity.ownerWire !== null) return hues.get(entity.ownerWire) ?? asset.palette.baseWire
    return asset.palette.branch
  }
  const line = (
    entity: Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>,
    width: number,
  ): LineMaterial => {
    const color = colorFor(entity)
    const key = `${entity.kind}:${color}:${width}`
    let material = lines.get(key)
    if (material === undefined) {
      material = new LineMaterial({ color: bloomRadiance(color, asset.glow.bloom), linewidth: width, worldUnits: true })
      const size = resolution()
      material.resolution.set(size.width, size.height)
      lines.set(key, material)
      lineMaterials.add(material)
    }
    return material
  }
  const marker = (markerAsset: TreeLodAssets['marker']): THREE.SpriteMaterial => {
    const key = `marker:${markerAsset.color}`
    let material = sprites.get(key)
    if (material === undefined) {
      const texture = discTexture('#ffffff')
      textures.add(texture)
      material = new THREE.SpriteMaterial({
        map: texture,
        color: bloomRadiance(markerAsset.color, asset.glow.bloom),
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
      material = new THREE.SpriteMaterial({
        map: texture,
        color: bloomRadiance('#ffffff', asset.glow.bloom),
        transparent: true,
        depthTest: entity.kind !== 'pip',
      })
      if (authored !== null) material.userData['aspect'] = authored.aspect
      sprites.set(key, material)
      spriteMaterials.add(material)
    }
    return material
  }
  return { line, sprite, marker }
}
