import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js'
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js'
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js'
import { SMAAPass } from 'three/examples/jsm/postprocessing/SMAAPass.js'
import { UnrealBloomPass } from 'three/examples/jsm/postprocessing/UnrealBloomPass.js'
import type { WireId } from '../src/kernel/diagram/diagram'
import type { Entity } from '../src/view3d/scene'
import { mountGlowRenderer } from './glow-render'
import { GlowTilePlan, type DirtyGlowTile } from './glow-tiles'
import { projectedDiameterPx, selectLod, type LodLevel } from './lod-policy'
import { SpatialIndex } from './spatial-index'
import {
  disposeTreeObject,
  makeBatchedTreeObject,
  makeMarkerObject,
  makeRawTreeObject,
  type OrchardMaterialSource,
} from './tree-objects'
import type { OrchardWorldSave, SavedTree, SavedTreeLayout } from './world'

const MAX_PIXEL_RATIO = 1.5
const MAX_REPRESENTATION_OPERATIONS = 12
const SPATIAL_CELL_SIZE = 128

export type RenderMode = 'game' | 'raw'
export type AntialiasingMethod = 'smaa' | 'off'
type ResidentLod = Exclude<LodLevel, 'culled'>

export type OrchardFrameStats = {
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

export type OrchardWorld = {
  readonly canvas: HTMLCanvasElement
  setCount(count: number): Promise<OrchardBuildStats>
  setTrees(trees: readonly SavedTree[]): Promise<OrchardBuildStats>
  setMode(mode: RenderMode): void
  setAntialiasing(enabled: boolean): AntialiasingMethod
  setPlayer(x: number, z: number, yaw: number, pitch: number): void
  resize(width: number, height: number): void
  render(): OrchardFrameStats
  dispose(): void
}

export type TreeObjectBuilder = (
  layout: SavedTreeLayout,
  saved: SavedTree,
  index: number,
  lod: ResidentLod,
  raw: boolean,
) => THREE.Group

type TreeRenderState = {
  saved: SavedTree
  index: number
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

export class OrchardWorldLifecycle {
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

export function treeWorldSphere(saved: SavedTree, layout: SavedTreeLayout): THREE.Sphere {
  const center = new THREE.Vector3(
    layout.bounds.center.x,
    layout.bounds.center.y,
    layout.bounds.center.z,
  )
  center.applyAxisAngle(new THREE.Vector3(0, 1, 0), saved.yaw)
  center.x += saved.x
  center.z += saved.z
  return new THREE.Sphere(center, layout.bounds.radius)
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

function sameSavedTree(left: SavedTree, right: SavedTree): boolean {
  return left.layout === right.layout
    && left.x === right.x
    && left.z === right.z
    && left.yaw === right.yaw
}

export class OrchardTreeRuntime {
  private readonly states = new Map<string, TreeRenderState>()
  private readonly spatial = new SpatialIndex<SpatialTree>(SPATIAL_CELL_SIZE)
  private readonly glowPlan = new GlowTilePlan(SPATIAL_CELL_SIZE)
  private operationHead: RepresentationOperationNode | null = null
  private operationTail: RepresentationOperationNode | null = null
  private readonly tracked = new Set<TreeRenderState>()
  private readonly failures = new Map<string, RepresentationFailure>()
  private readonly maxRadius: number
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
    private readonly layouts: Readonly<Record<string, SavedTreeLayout>>,
    private readonly parent: THREE.Group,
    private readonly buildObject: TreeObjectBuilder,
    private readonly releaseObject: (object: THREE.Group) => void = disposeTreeObject,
  ) {
    this.maxRadius = Object.values(layouts).reduce((maximum, layout) => Math.max(maximum, layout.bounds.radius), 0)
  }

  public setTrees(trees: readonly SavedTree[]): OrchardBuildStats {
    this.assertActive()
    const started = performance.now()
    const incoming = new Map<string, { readonly saved: SavedTree; readonly index: number }>()
    trees.forEach((tree, index) => {
      if (incoming.has(tree.id)) throw new Error(`duplicate active tree id '${tree.id}'`)
      if (this.layouts[tree.layout] === undefined) throw new Error(`unknown active tree layout '${tree.layout}'`)
      incoming.set(tree.id, { saved: tree, index })
    })

    for (const [id, state] of this.states) {
      if (!incoming.has(id)) this.removeState(state)
    }

    for (const { saved, index } of incoming.values()) {
      const current = this.states.get(saved.id)
      if (current === undefined) this.insertState(saved, index)
      else this.updateState(current, saved, index)
    }

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

  public updateGame(
    camera: THREE.PerspectiveCamera,
    fogFar: number,
    viewportHeight: number,
  ): { readonly visited: number; readonly lodMs: number } {
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
      if (!state.active) continue
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

  private insertState(saved: SavedTree, index: number): void {
    const layout = this.layouts[saved.layout]!
    const desired: LodLevel = this.mode === 'raw' ? 'full' : 'culled'
    const state: TreeRenderState = {
      saved,
      index,
      sphere: treeWorldSphere(saved, layout),
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
      needsReplacement: false,
    }
    this.states.set(saved.id, state)
    this.lodCounts[desired]++
    this.logicalEntities += layout.lods.full.entities.length
    this.indexState(state)
    this.setGlow(state)
    if (desired !== 'culled') this.enqueueState(state)
  }

  private updateState(state: TreeRenderState, saved: SavedTree, index: number): void {
    const previous = state.saved
    const previousLayout = this.layouts[previous.layout]!
    const nextLayout = this.layouts[saved.layout]!
    const layoutChanged = previous.layout !== saved.layout
    state.index = index
    if (sameSavedTree(previous, saved)) {
      if (state.object !== null) this.applyPlacement(state.object, saved, index)
      return
    }

    state.saved = saved
    state.sphere = treeWorldSphere(saved, nextLayout)
    this.clearFailure(state)
    this.indexState(state)
    this.setGlow(state)
    if (layoutChanged) {
      this.logicalEntities += nextLayout.lods.full.entities.length - previousLayout.lods.full.entities.length
      this.detachSelectedObject(state)
      this.enqueueState(state, true)
    } else if (state.object !== null) {
      this.applyPlacement(state.object, saved, index)
    } else if (state.desired !== 'culled') {
      this.enqueueState(state)
    }
  }

  private removeState(state: TreeRenderState): void {
    this.states.delete(state.saved.id)
    this.spatial.remove(state.saved.id)
    this.glowPlan.remove(state.saved.id)
    this.logicalEntities -= this.layouts[state.saved.layout]!.lods.full.entities.length
    this.lodCounts[state.desired]--
    this.clearFailure(state)
    state.active = false
    this.cancelStateOperation(state)
    this.tracked.delete(state)
    if (state.object !== null) {
      this.detachSelectedObject(state)
      const object = state.object
      state.object = null
      state.resident = 'culled'
      this.appendOperation({ kind: 'retired', object })
      this.pending++
    }
  }

  private indexState(state: TreeRenderState): void {
    this.spatial.insert({
      id: state.saved.id,
      x: state.sphere.center.x,
      z: state.sphere.center.z,
      state,
    })
  }

  private setGlow(state: TreeRenderState): void {
    const glow = this.layouts[state.saved.layout]!.glow
    this.glowPlan.set({
      id: state.saved.id,
      x: state.saved.x,
      z: state.saved.z,
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
    this.detachSelectedObject(state)
    this.tracked.add(state)
  }

  private enqueueState(state: TreeRenderState, force = false): void {
    if (!state.active) return
    if (force) {
      state.needsReplacement = true
      this.detachSelectedObject(state)
    }
    if (state.queued) return
    if (!state.needsReplacement && state.resident === state.desired && state.object !== null) return
    if (!state.needsReplacement && state.desired === 'culled' && state.object === null) return
    if (!force && this.failures.get(state.saved.id)?.desired === state.desired) return
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

  private detachSelectedObject(state: TreeRenderState): void {
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
      this.detachSelectedObject(state)
      this.releaseObject(state.object)
      state.object = null
      state.resident = 'culled'
    }
    state.needsReplacement = false
    if (state.desired === 'culled') return
    try {
      const layout = this.layouts[state.saved.layout]!
      const object = this.buildObject(
        layout,
        state.saved,
        state.index,
        state.desired,
        this.mode === 'raw',
      )
      this.applyPlacement(object, state.saved, state.index)
      object.visible = true
      this.parent.add(object)
      const cardinality = objectCardinality(object)
      state.object = object
      state.resident = state.desired
      state.objectNodes = cardinality.nodes
      state.objectInstanced = cardinality.instanced
      state.objectPointLights = cardinality.pointLights
      state.representedEntities = state.desired === 'marker' ? 0 : layout.lods[state.desired].entities.length
      this.resident++
      this.objects += cardinality.nodes
      this.instanced += cardinality.instanced
      this.pointLights += cardinality.pointLights
      this.representedEntities += state.representedEntities
      this.clearFailure(state)
    } catch (error) {
      this.failures.set(state.saved.id, {
        desired: state.desired,
        message: error instanceof Error ? error.message : String(error),
      })
    }
  }

  private clearFailure(state: TreeRenderState): void {
    this.failures.delete(state.saved.id)
  }

  private applyPlacement(object: THREE.Group, saved: SavedTree, index: number): void {
    object.position.set(saved.x, 0, saved.z)
    object.rotation.y = saved.yaw
    object.userData['treeId'] = saved.id
    object.userData['treeIndex'] = index
    object.traverse((child) => {
      if (child === object) return
      child.userData['treeId'] = saved.id
      child.userData['treeIndex'] = index
    })
  }

  private pruneTracked(state: TreeRenderState): void {
    if (state.active && (state.desired !== 'culled' || state.object !== null || state.queued)) return
    this.tracked.delete(state)
  }

  private assertActive(): void {
    if (this.disposed) throw new Error('orchard tree runtime is disposed')
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

/** Saved bloom is a bounded radiance contribution: multiplier = 1 + bloom, for [1, 2]× authored color. */
function bloomRadiance(color: string, bloom: number): THREE.Color {
  return new THREE.Color(color).multiplyScalar(1 + bloom)
}

export function makeOrchardMaterialSource(
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
      material = new LineMaterial({ color: bloomRadiance(color, layout.glow.bloom), linewidth: width, worldUnits: true })
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
        color: bloomRadiance(saved.color, layout.glow.bloom),
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
        color: bloomRadiance('#ffffff', layout.glow.bloom),
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

export function mountOrchardWorld(
  container: HTMLElement,
  world: OrchardWorldSave,
): OrchardWorld {
  const renderer = new THREE.WebGLRenderer({ antialias: false, powerPreference: 'high-performance' })
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, MAX_PIXEL_RATIO))
  renderer.outputColorSpace = THREE.SRGBColorSpace
  renderer.shadowMap.enabled = false
  renderer.info.autoReset = false
  renderer.domElement.setAttribute('aria-label', 'Walkable proof-tree orchard')
  container.appendChild(renderer.domElement)

  const scene = new THREE.Scene()
  scene.background = new THREE.Color(world.terrain.sky)
  scene.fog = new THREE.Fog(world.terrain.sky, world.terrain.fogNear, world.terrain.fogFar)
  const camera = new THREE.PerspectiveCamera(67, 1, 0.08, 1800)
  camera.rotation.order = 'YXZ'
  const composer = new EffectComposer(renderer)
  const renderPass = new RenderPass(scene, camera)
  const bloomPass = new UnrealBloomPass(new THREE.Vector2(1, 1), 0.65, 0.45, 0.55)
  const smaaPass = new SMAAPass(1, 1)
  const outputPass = new OutputPass()
  composer.addPass(renderPass)
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

  const trees = new THREE.Group()
  trees.name = 'separate-proof-trees'
  scene.add(trees)
  const lineMaterials = new Set<LineMaterial>()
  const textures = new Set<THREE.Texture>()
  const spriteMaterials = new Set<THREE.SpriteMaterial>()
  let size = { width: 1, height: 1 }
  const materialsByLayout = new Map<string, OrchardMaterialSource>()
  for (const [layoutId, layout] of Object.entries(world.layouts)) {
    materialsByLayout.set(layoutId, makeOrchardMaterialSource(
      layout,
      lineMaterials,
      textures,
      spriteMaterials,
      () => size,
    ))
  }
  const runtime = new OrchardTreeRuntime(
    world.layouts,
    trees,
    (layout, saved, index, lod, raw) => {
      const placement = {
        id: saved.id,
        index,
        x: saved.x,
        z: saved.z,
        yaw: saved.yaw,
      }
      const materials = materialsByLayout.get(saved.layout)!
      if (raw) return makeRawTreeObject(layout, placement, materials)
      if (lod === 'marker') return makeMarkerObject(layout, placement, materials)
      return makeBatchedTreeObject(layout, lod, placement, materials)
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

  const setTrees = async (savedTrees: readonly SavedTree[]): Promise<OrchardBuildStats> => runtime.setTrees(savedTrees)
  const lifecycle = new OrchardWorldLifecycle([
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
      const representationWork = runtime.processOperations()
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
