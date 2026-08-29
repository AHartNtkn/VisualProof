import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const host = vi.hoisted(() => {
  const viewport = {
    renderer: [0, 0] as [number, number],
    postprocess: [0, 0] as [number, number],
    scaledEffect: [0, 0] as [number, number],
  }
  const resources: Array<{ released: boolean }> = []
  return {
    attached: false,
    canvasAttributes: new Map<string, string>(),
    framePresented: false,
    rendererAcceptedFrame: false,
    viewport,
    resources,
    potObjects: [] as unknown[],
    targetSnapshotJson: new Set<string>(),
    snapshotBounds: new Map<string, { center: { x: number; y: number; z: number }; radius: number }>(),
    trackResource() {
      const resource = { released: false }
      resources.push(resource)
      return resource
    },
    viewportReady(width: number, height: number, pixelRatio: number) {
      return viewport.renderer[0] === width && viewport.renderer[1] === height
        && viewport.postprocess[0] === width && viewport.postprocess[1] === height
        && viewport.scaledEffect[0] === width * pixelRatio
        && viewport.scaledEffect[1] === height * pixelRatio
    },
    allResourcesReleased() {
      return resources.length > 0 && resources.every(({ released }) => released)
    },
  }
})

vi.mock('three', async (importOriginal) => {
  const actual = await importOriginal<typeof import('three')>()

  class TestWebGlRenderer {
    private readonly resource = host.trackResource()
    public readonly domElement: HTMLCanvasElement
    public readonly shadowMap = { enabled: true }
    public readonly info = {
      autoReset: true,
      render: { calls: 0, triangles: 0 },
      memory: { geometries: 0 },
      reset: () => {
        this.info.render.calls = 0
        this.info.render.triangles = 0
      },
    }
    public outputColorSpace = ''

    public constructor() {
      this.domElement = {
        width: 0,
        height: 0,
        setAttribute(name: string, value: string) {
          host.canvasAttributes.set(name, value)
        },
        remove() {
          host.attached = false
        },
      } as unknown as HTMLCanvasElement
    }

    public setPixelRatio(): void {}

    public setSize(width: number, height: number): void {
      this.domElement.width = width
      this.domElement.height = height
      host.viewport.renderer = [width, height]
    }

    public present(): void { host.rendererAcceptedFrame = true }

    public dispose(): void { this.resource.released = true }
  }

  return { ...actual, WebGLRenderer: TestWebGlRenderer }
})

vi.mock('three/examples/jsm/postprocessing/EffectComposer.js', () => ({
  EffectComposer: class TestEffectComposer {
    private readonly resource = host.trackResource()
    public constructor(private readonly renderer: {
      readonly info: { readonly render: { calls: number; triangles: number } }
      present(): void
    }) {}

    public addPass(): void {}
    public setPixelRatio(): void {}
    public setSize(width: number, height: number): void {
      host.viewport.postprocess = [width, height]
    }
    public render(): void {
      this.renderer.present()
      host.framePresented = host.rendererAcceptedFrame
      this.renderer.info.render.calls = 3
      this.renderer.info.render.triangles = 7
    }
    public dispose(): void { this.resource.released = true }
  },
}))

vi.mock('three/examples/jsm/postprocessing/RenderPass.js', () => ({
  RenderPass: class TestRenderPass {},
}))

vi.mock('three/examples/jsm/postprocessing/UnrealBloomPass.js', () => ({
  UnrealBloomPass: class TestUnrealBloomPass {
    private readonly resource = host.trackResource()
    public setSize(width: number, height: number): void {
      host.viewport.scaledEffect = [width, height]
    }
    public dispose(): void { this.resource.released = true }
  },
}))

vi.mock('three/examples/jsm/postprocessing/SMAAPass.js', () => ({
  SMAAPass: class TestSmaaPass {
    private readonly resource = host.trackResource()
    public dispose(): void { this.resource.released = true }
  },
}))

vi.mock('three/examples/jsm/postprocessing/OutputPass.js', () => ({
  OutputPass: class TestOutputPass {
    private readonly resource = host.trackResource()
    public dispose(): void { this.resource.released = true }
  },
}))

vi.mock('../../../src/game/render/glow-render', () => ({
  mountGlowRenderer: () => {
    const resource = host.trackResource()
    return {
      sync() {},
      dispose() { resource.released = true },
    }
  },
}))

vi.mock('../../../src/game/render/assets', async (importOriginal) => {
  const actual = await importOriginal<typeof import('../../../src/game/render/assets')>()

  class TestTreeRenderAssetCache extends actual.TreeRenderAssetCache {
    public override get(snapshot: import('../../../src/game/diagram-snapshot').DiagramSnapshot) {
      const asset = super.get(snapshot)
      const specified = host.snapshotBounds.get(snapshot.json)
      if (specified === undefined && !host.targetSnapshotJson.has(snapshot.json)) return asset

      const center = specified?.center ?? { x: 3, y: 2, z: 4 }
      const radius = specified?.radius ?? 5
      return {
        ...asset,
        bounds: { center, radius },
        lods: {
          ...asset.lods,
          full: { ...asset.lods.full, center, radius },
          reduced: { ...asset.lods.reduced, center, radius },
        },
      }
    }
  }

  return { ...actual, TreeRenderAssetCache: TestTreeRenderAssetCache }
})

vi.mock('../../../src/game/render/pots', async (importOriginal) => {
  const actual = await importOriginal<typeof import('../../../src/game/render/pots')>()
  return {
    ...actual,
    makePotObject(...args: Parameters<typeof actual.makePotObject>) {
      const object = actual.makePotObject(...args)
      host.potObjects.push(object)
      return object
    },
  }
})

import type { GameTree } from '../../../src/game/model'
import { snapshotFromDiagram } from '../../../src/game/diagram-snapshot'
import { mountGameWorld } from '../../../src/game/render/world'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { scene3 } from '../../../src/view3d/scene'
import { focusPoint } from '../../../src/view3d/pick'
import type { TreeChange } from '../../../src/game/session'
import { gameSession, publishTreeChange } from '../../../src/game/session'
import { SaveWriter } from '../../../src/game/save-writer'
import { treeUpdateFromGameTree } from '../../../src/game/save-client'
import { ORDER_CATALOG, STARTER_ORDER_ID, type OrderProgress } from '../../../src/game/orders/catalog'
import { orderSession, publishOrderMutation } from '../../../src/game/orders/session'
import type { PotObject, PotRender } from '../../../src/game/render/pots'

beforeEach(() => {
  host.attached = false
  host.canvasAttributes.clear()
  host.framePresented = false
  host.rendererAcceptedFrame = false
  host.viewport.renderer = [0, 0]
  host.viewport.postprocess = [0, 0]
  host.viewport.scaledEffect = [0, 0]
  host.resources.length = 0
  host.potObjects.length = 0
  host.targetSnapshotJson.clear()
  host.snapshotBounds.clear()
  vi.stubGlobal('window', { devicePixelRatio: 2 })
  vi.stubGlobal('document', {
    createElement: () => ({
      width: 0,
      height: 0,
      getContext: () => ({
        fillStyle: '',
        font: '',
        textBaseline: '',
        beginPath() {},
        arc() {},
        fill() {},
        fillText() {},
        measureText: () => ({ width: 24 }),
      }),
    }),
  })
})

afterEach(() => {
  vi.restoreAllMocks()
  vi.unstubAllGlobals()
})

function blankTree(id = 'tree-a', x = 0, z = -20): GameTree {
  const diagram = new DiagramBuilder().build()
  return {
    id,
    snapshot: snapshotFromDiagram(diagram),
    placement: { x, z, yaw: 0 },
  }
}

function targetTree(id: string, x: number, z: number, yaw: number): GameTree {
  const builder = new DiagramBuilder()
  builder.cut(builder.root)
  const snapshot = snapshotFromDiagram(builder.build())
  host.targetSnapshotJson.add(snapshot.json)
  return {
    id,
    snapshot,
    placement: { x, z, yaw },
  }
}

function container(): HTMLElement {
  return {
    appendChild() { host.attached = true },
  } as unknown as HTMLElement
}

function pointCameraAtBranch(world: ReturnType<typeof mountGameWorld>, tree: GameTree): void {
  const branch = scene3(tree.snapshot.diagram).entities[0]!
  if (!('pts' in branch)) throw new Error('expected a branch')
  const point = branch.pts[0]!
  const group = new THREE.Object3D()
  group.position.set(tree.placement.x, 0, tree.placement.z)
  group.rotation.y = tree.placement.yaw
  group.updateMatrixWorld(true)
  const worldPoint = new THREE.Vector3(point.x, point.y, point.z).applyMatrix4(group.matrixWorld)
  world.setCamera({
    eye: {
      x: worldPoint.x,
      y: worldPoint.y,
      z: worldPoint.z + 20,
    },
    forward: { x: 0, y: 0, z: -1 },
  })
}

function starterPot(x = 0, z = -20): PotRender {
  const goal = ORDER_CATALOG.find(({ id }) => id === STARTER_ORDER_ID)?.goal
  if (goal === undefined) throw new Error('missing starter order goal')
  return {
    orderId: STARTER_ORDER_ID,
    placement: { x, z, yaw: 0 },
    goal,
  }
}

function pendingStarterOrder(): OrderProgress {
  return { reputation: 0, orders: new Map([[STARTER_ORDER_ID, { kind: 'pending' as const }]]) }
}

function authoredGoal(orderId: string) {
  return ORDER_CATALOG.find(({ id }) => id === orderId)?.goal
}

function mountOrderWorld(
  trees: readonly GameTree[] = [],
  goalForOrder: (orderId: string) => ReturnType<typeof authoredGoal> = authoredGoal,
): ReturnType<typeof mountGameWorld> {
  return mountGameWorld(container(), trees, { goalForOrder })
}

function latestPot(): PotObject {
  const object = host.potObjects.at(-1)
  if (object === undefined) throw new Error('expected a created pot')
  return object as PotObject
}

function potResourceSpies(object: PotObject) {
  const geometries = new Set<THREE.BufferGeometry>()
  const materials = new Set<THREE.Material>()
  object.group.traverse((candidate) => {
    if ('geometry' in candidate) {
      const geometry = (candidate as THREE.Mesh).geometry
      if (geometry instanceof THREE.BufferGeometry) geometries.add(geometry)
    }
    if (candidate.userData['ownsMaterial'] === true && 'material' in candidate) {
      const material = (candidate as THREE.Mesh).material
      for (const entry of Array.isArray(material) ? material : [material]) {
        if (entry instanceof THREE.Material) materials.add(entry)
      }
    }
  })
  return {
    geometries: [...geometries].map((geometry) => vi.spyOn(geometry, 'dispose')),
    materials: [...materials].map((material) => vi.spyOn(material, 'dispose')),
  }
}

function expectResourcesDisposedOnce(resources: ReturnType<typeof potResourceSpies>): void {
  expect(resources.geometries.length).toBeGreaterThan(2)
  expect(resources.materials.length).toBeGreaterThan(2)
  for (const resource of resources.geometries) expect(resource).toHaveBeenCalledTimes(1)
  for (const resource of resources.materials) expect(resource).toHaveBeenCalledTimes(1)
}

describe('production game world', () => {
  it('rejects preparation against a stale tree without changing the live target', () => {
    const current = targetTree('tree', 10, -20, Math.PI / 2)
    const stale = blankTree('tree', 10, -20)
    const after = { ...stale, snapshot: snapshotFromDiagram(applyDoubleCutIntro(stale.snapshot.diagram, {
      region: stale.snapshot.diagram.root, regions: [], nodes: [], wires: [],
    })) }
    const mutation: TreeChange = { kind: 'update', treeId: current.id, before: stale, after }
    const world = mountGameWorld(container(), [current])
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(() => world.prepareTreeChange(mutation)).toThrow(/stale tree change/)
    expect(world.pickTree(0, 0)).toEqual({
      treeId: 'tree', center: { x: 14, y: 2, z: -23 }, radius: 5,
    })
    world.dispose()
  })

  it('publishes fresh logical target bounds with a committed tree update', () => {
    const before = blankTree('tree', 0, -20)
    const after: GameTree = {
      ...before,
      snapshot: snapshotFromDiagram(applyDoubleCutIntro(before.snapshot.diagram, {
        region: before.snapshot.diagram.root, regions: [], nodes: [], wires: [],
      })),
    }
    host.snapshotBounds.set(before.snapshot.json, {
      center: { x: -8, y: 2, z: 4 }, radius: 1,
    })
    host.snapshotBounds.set(after.snapshot.json, {
      center: { x: 8, y: 2, z: 4 }, radius: 1,
    })
    const mutation: TreeChange = { kind: 'update', treeId: before.id, before, after }
    const world = mountGameWorld(container(), [before], () => 0)

    const prepared = world.prepareTreeChange(mutation)
    world.commitTreeChange(prepared)
    world.setCamera({ eye: { x: 8, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toEqual({
      treeId: 'tree', center: { x: 8, y: 2, z: -16 }, radius: 1,
    })
    world.render(350)
    world.setCamera({ eye: { x: 8, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toEqual({
      treeId: 'tree', center: { x: 8, y: 2, z: -16 }, radius: 1,
    })
    world.setCamera({ eye: { x: -8, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toBeNull()
    world.dispose()
  })

  it('commits a prepared update only once', () => {
    const before = blankTree('tree', 0, -20)
    const after = {
      ...before,
      snapshot: snapshotFromDiagram(applyDoubleCutIntro(before.snapshot.diagram, {
        region: before.snapshot.diagram.root, regions: [], nodes: [], wires: [],
      })),
    }
    const world = mountGameWorld(container(), [before])
    const disposeGeometry = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose')
    const prepared = world.prepareTreeChange({ kind: 'update', treeId: before.id, before, after })
    const beforeCommit = disposeGeometry.mock.calls.length

    world.commitTreeChange(prepared)
    const afterFirstCommit = disposeGeometry.mock.calls.length
    world.commitTreeChange(prepared)

    expect(afterFirstCommit).toBeGreaterThanOrEqual(beforeCommit)
    expect(disposeGeometry.mock.calls).toHaveLength(afterFirstCommit)
    world.dispose()
  })

  it('invalidates and disposes prepared updates before replacing all trees', () => {
    const before = blankTree('tree', 0, -20)
    const after = {
      ...before,
      snapshot: snapshotFromDiagram(applyDoubleCutIntro(before.snapshot.diagram, {
        region: before.snapshot.diagram.root, regions: [], nodes: [], wires: [],
      })),
    }
    const replacement = targetTree('replacement', 10, -20, Math.PI / 2)
    const world = mountGameWorld(container(), [before])
    const disposeGeometry = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose')
    const prepared = world.prepareTreeChange({ kind: 'update', treeId: before.id, before, after })
    const beforeReplacement = disposeGeometry.mock.calls.length

    world.setTrees([replacement])
    world.commitTreeChange(prepared)

    expect(disposeGeometry.mock.calls.length).toBeGreaterThan(beforeReplacement)
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toMatchObject({ treeId: 'replacement' })
    world.dispose()
  })

  it('disposes an uncommitted preparation and ignores its later commit', () => {
    const before = blankTree('tree', 0, -20)
    const after = {
      ...before,
      snapshot: snapshotFromDiagram(applyDoubleCutIntro(before.snapshot.diagram, {
        region: before.snapshot.diagram.root, regions: [], nodes: [], wires: [],
      })),
    }
    const world = mountGameWorld(container(), [before])
    const disposeGeometry = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose')
    const prepared = world.prepareTreeChange({ kind: 'update', treeId: before.id, before, after })
    const beforeDispose = disposeGeometry.mock.calls.length

    world.dispose()

    expect(disposeGeometry.mock.calls.length).toBeGreaterThan(beforeDispose)
    expect(() => world.commitTreeChange(prepared)).not.toThrow()
  })

  it('rejects a sibling preparation for the same live tree', () => {
    const before = blankTree('tree', 0, -20)
    const after = {
      ...before,
      snapshot: snapshotFromDiagram(applyDoubleCutIntro(before.snapshot.diagram, {
        region: before.snapshot.diagram.root, regions: [], nodes: [], wires: [],
      })),
    }
    const world = mountGameWorld(container(), [before])
    const first = world.prepareTreeChange({ kind: 'update', treeId: before.id, before, after })

    expect(() => world.prepareTreeChange({ kind: 'update', treeId: before.id, before, after }))
      .toThrow(/already prepared/)

    world.commitTreeChange(first)
    world.dispose()
  })

  it('publishes an inserted tree as a target at commit and settles it into the runtime', () => {
    const inserted = targetTree('inserted', 0, -20, 0)
    const world = mountGameWorld(container(), [], () => 0)
    world.setRenderMode('raw')
    world.setCamera({ eye: { x: 3, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })

    const prepared = world.prepareTreeChange({
      kind: 'insert', treeId: inserted.id, after: inserted,
    })
    expect(world.pickTree(0, 0)).toBeNull()

    world.commitTreeChange(prepared)
    expect(world.pickTree(0, 0)).toMatchObject({ treeId: inserted.id })
    expect(world.render(350)).toMatchObject({ logical: 1, resident: 1 })
    expect(world.pickTree(0, 0)).toMatchObject({ treeId: inserted.id })
    world.dispose()
  })

  it('discards an inserted tree without making it targetable or represented', () => {
    const inserted = targetTree('discarded', 0, -20, 0)
    const world = mountGameWorld(container(), [], () => 0)
    world.setRenderMode('raw')
    world.setCamera({ eye: { x: 3, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })

    const prepared = world.prepareTreeChange({
      kind: 'insert', treeId: inserted.id, after: inserted,
    })
    world.discardTreeChange(prepared)
    world.commitTreeChange(prepared)

    expect(world.pickTree(0, 0)).toBeNull()
    expect(world.render(350)).toMatchObject({ logical: 0, resident: 0 })
    world.dispose()
  })

  it('rejects insertion when the tree identity is already live or prepared', () => {
    const existing = blankTree('duplicate')
    const inserted = targetTree(existing.id, 0, -20, 0)
    const world = mountGameWorld(container(), [existing])

    expect(() => world.prepareTreeChange({
      kind: 'insert', treeId: inserted.id, after: inserted,
    })).toThrow(/already exists/)

    const fresh = { ...inserted, id: 'fresh' }
    const first = world.prepareTreeChange({ kind: 'insert', treeId: fresh.id, after: fresh })
    expect(() => world.prepareTreeChange({
      kind: 'insert', treeId: fresh.id, after: fresh,
    })).toThrow(/already prepared/)
    world.discardTreeChange(first)
    world.dispose()
  })

  it('discards a prepared update when save enqueue rejects without publishing live state', async () => {
    const before = targetTree('tree', 10, -20, Math.PI / 2)
    const session = gameSession(new Map([[before.id, before]]))
    const mutation = session.planDoubleCut({
      treeId: before.id,
      entity: {
        kind: 'branch', key: 'pointed', region: before.snapshot.diagram.root,
        polarity: 0, pts: [],
      },
      distance: 5,
    })
    const world = mountGameWorld(container(), [before])
    const writer = new SaveWriter('slot-a', {
      updateTree: async () => 1,
      insertTree: async () => 1,
      updateCamera: async () => {},
      acceptOrder: async () => {},
      abandonOrder: async () => {},
      completeOrder: async () => 1,
    })
    await writer.dispose()
    expect(() => publishTreeChange(
      session,
      mutation,
      world,
      (tree) => writer.tree(treeUpdateFromGameTree(tree)),
    )).toThrow('disposed')
    expect(session.trees.get(before.id)).toBe(before)
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toEqual({
      treeId: 'tree', center: { x: 14, y: 2, z: -23 }, radius: 5,
    })
    world.dispose()
  })

  it('discards a prepared insertion when save enqueue rejects without publishing the new tree', async () => {
    // Catches the production renderer leaking a prepared insertion after the durable writer refuses it.
    const inserted = targetTree('inserted', 0, -20, 0)
    const session = gameSession(new Map())
    const insertion: TreeChange = { kind: 'insert', treeId: inserted.id, after: inserted }
    const world = mountGameWorld(container(), [], () => 0)
    const writer = new SaveWriter('slot-a', {
      updateTree: async () => 1,
      insertTree: async () => 1,
      updateCamera: async () => {},
      acceptOrder: async () => {},
      abandonOrder: async () => {},
      completeOrder: async () => 1,
    })
    await writer.dispose()

    expect(() => publishTreeChange(
      session,
      insertion,
      world,
      (tree) => writer.insertTree(treeUpdateFromGameTree(tree)),
    )).toThrow('disposed')
    expect(session.trees.has(inserted.id)).toBe(false)
    world.setCamera({ eye: { x: 3, y: 2, z: 4 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pickTree(0, 0)).toBeNull()
    expect(world.render(350)).toMatchObject({ logical: 0, resident: 0 })
    world.dispose()
  })

  it('mounts a generic tree, resizes its canvas, renders without representation failures, and tears down', () => {
    const world = mountGameWorld(container(), [blankTree()])
    world.setCamera({ eye: { x: 0, y: 1.7, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    world.setRenderMode('raw')
    world.resize(640, 360)

    const rendered = world.render(16)

    expect(host.attached).toBe(true)
    expect(host.canvasAttributes.get('aria-label')).toBe('Proof-tree orchard view')
    expect([world.canvas.width, world.canvas.height]).toEqual([640, 360])
    expect(host.viewportReady(640, 360, 1.5)).toBe(true)
    expect(host.framePresented).toBe(true)
    expect(rendered).toMatchObject({
      logical: 1,
      visible: 1,
      resident: 1,
      full: 1,
      pointLights: 0,
      representedEntities: 1,
      representationErrors: 0,
      error: null,
    })

    world.dispose()
    world.dispose()
    expect(host.attached).toBe(false)
    expect(host.allResourcesReleased()).toBe(true)
  })

  it('keeps removal authoritative while a tween is active', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    const after = applyDoubleCutIntro(tree.snapshot.diagram, {
      region: tree.snapshot.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.setRenderMode('raw')
    world.render(0)
    const afterTree = { ...tree, snapshot: snapshotFromDiagram(after) }
    const prepared = world.prepareTreeChange({ kind: 'update', treeId: tree.id, before: tree, after: afterTree })
    world.commitTreeChange(prepared)

    world.setTrees([])

    expect(world.render(350)).toMatchObject({ logical: 0, resident: 0, representedEntities: 0 })
    world.dispose()
  })

  it('renders replacement diagram and placement after a tween is superseded', () => {
    const original = blankTree()
    const replacementBuilder = new DiagramBuilder()
    replacementBuilder.cut(replacementBuilder.root)
    const replacementDiagram = replacementBuilder.build()
    const replacement: GameTree = {
      id: original.id,
      snapshot: snapshotFromDiagram(replacementDiagram),
      placement: { x: 50, z: -60, yaw: 0 },
    }
    const staleTarget = applyDoubleCutIntro(original.snapshot.diagram, {
      region: original.snapshot.diagram.root, regions: [], nodes: [], wires: [],
    })
    const world = mountGameWorld(container(), [original], () => 0)
    world.setRenderMode('raw')
    world.render(0)
    const staleTree = { ...original, snapshot: snapshotFromDiagram(staleTarget) }
    const prepared = world.prepareTreeChange({
      kind: 'update', treeId: original.id, before: original, after: staleTree,
    })
    world.commitTreeChange(prepared)

    world.setTrees([replacement])
    const rendered = world.render(350)

    expect(rendered).toMatchObject({
      logical: 1,
      resident: 1,
      representedEntities: scene3(replacementDiagram).entities.length,
    })
    world.dispose()
  })

  it('returns the nearest logical tree target before its first render', () => {
    const world = mountGameWorld(container(), [
      targetTree('far', 10, -60, Math.PI / 2),
      targetTree('near', 10, -20, Math.PI / 2),
    ])
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(world.pickTree(0, 0)).toEqual({
      treeId: 'near',
      center: { x: 14, y: 2, z: -23 },
      radius: 5,
    })

    world.dispose()
  })

  it('uses the rendered placement transform for a rotated logical target', () => {
    const tree = targetTree('shared-transform', 17, -11, Math.PI / 3)
    const transform = new THREE.Object3D()
    transform.position.set(17, 0, -11)
    transform.rotation.y = Math.PI / 3
    transform.updateMatrixWorld(true)
    const center = new THREE.Vector3(3, 2, 4).applyMatrix4(transform.matrixWorld)
    const world = mountGameWorld(container(), [tree])
    world.setCamera({
      eye: { x: center.x, y: center.y, z: center.z + 20 },
      forward: { x: 0, y: 0, z: -1 },
    })

    const pointed = world.pickTree(0, 0)
    expect(pointed).toMatchObject({ treeId: tree.id, radius: 5 })
    expect(pointed!.center.x).toBeCloseTo(center.x)
    expect(pointed!.center.y).toBeCloseTo(center.y)
    expect(pointed!.center.z).toBeCloseTo(center.z)

    world.dispose()
  })

  it('returns null when the ray misses every logical tree', () => {
    const world = mountGameWorld(container(), [targetTree('only', 10, -20, Math.PI / 2)])
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(world.pickTree(0.8, 0)).toBeNull()

    world.dispose()
  })

  it('keeps the logical target stable across render modes and LOD changes', () => {
    const world = mountGameWorld(container(), [targetTree('tree', 10, -20, Math.PI / 2)])
    const center = { treeId: 'tree', center: { x: 14, y: 2, z: -23 }, radius: 5 }
    world.resize(640, 360)
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(world.pickTree(0, 0)).toEqual(center)
    world.setRenderMode('raw')
    expect(world.pickTree(0, 0)).toEqual(center)
    world.setRenderMode('game')
    world.render(0)
    world.setCamera({ eye: { x: 14, y: 2, z: 200 }, forward: { x: 0, y: 0, z: -1 } })
    world.render(16)
    expect(world.pickTree(0, 0)).toEqual(center)

    world.dispose()
  })

  it('points a reachable branch only on the orbit target tree', () => {
    const background = blankTree('background')
    const orbit = blankTree('orbit')
    const world = mountGameWorld(container(), [background, orbit])
    pointCameraAtBranch(world, orbit)

    expect(world.pointAtBranch(0, 0, 'orbit')).toMatchObject({
      treeId: 'orbit',
      entity: { kind: 'branch', key: 'b:r0', region: 'r0' },
    })
    world.dispose()
  })

  it('returns the nearest semantic branch or pot rather than terrain', () => {
    const branch = blankTree('branch', 0, -20)
    const world = mountGameWorld(container(), [branch])
    world.setPots([starterPot(0, -10)])
    world.setCamera({ eye: { x: 0, y: 1, z: 0 }, forward: { x: 0, y: -0.05, z: -1 } })

    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({
      kind: 'pot', orderId: STARTER_ORDER_ID,
    })

    world.setPots([starterPot(0, -40)])
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({
      kind: 'branch', pointed: { treeId: branch.id, entity: { kind: 'branch' } },
    })
    world.dispose()
  })

  it('orders close semantic branch and pot hits by their ray distances', () => {
    const branch = blankTree('branch', 0, -20)
    const world = mountGameWorld(container(), [branch])
    world.setCamera({ eye: { x: 0, y: 1, z: 0 }, forward: { x: 0, y: -0.05, z: -1 } })

    world.setPots([starterPot(0, -20)])
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({ kind: 'pot', orderId: STARTER_ORDER_ID })

    world.setPots([starterPot(0, -21.5)])
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({
      kind: 'branch', pointed: { treeId: branch.id },
    })
    world.dispose()
  })

  it('returns terrain only when the camera ray actually hits it', () => {
    const world = mountGameWorld(container(), [])
    world.setCamera({ eye: { x: 2, y: 3, z: 4 }, forward: { x: 0, y: -1, z: 0 } })

    const terrain = world.pointAtToolTarget(0, 0, null)
    expect(terrain).toMatchObject({ kind: 'ground', point: { x: 2 }, distance: expect.any(Number) })
    expect(terrain?.kind === 'ground' && terrain.point.z).toBeCloseTo(4, 3)

    world.setCamera({ eye: { x: 2, y: 3, z: 4 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()

    world.setCamera({ eye: { x: 2001, y: 3, z: 4 }, forward: { x: 0, y: -1, z: 0 } })
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('restricts branch targeting to the orbit tree without restricting pots', () => {
    const orbit = blankTree('orbit', 10, -20)
    const other = blankTree('other', 0, -10)
    const world = mountGameWorld(container(), [orbit, other])
    pointCameraAtBranch(world, other)

    expect(world.pointAtToolTarget(0, 0, orbit.id)).toBeNull()
    world.setPots([starterPot(0, -10)])
    expect(world.pointAtToolTarget(0, 0, orbit.id)).toMatchObject({
      kind: 'pot', orderId: STARTER_ORDER_ID,
    })
    world.dispose()
  })

  it('prepares pot appearance and removal without publishing either until commit', () => {
    const world = mountOrderWorld()
    const pending = pendingStarterOrder()
    const accept = orderSession(pending).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })
    world.setCamera({ eye: { x: 0, y: 0.55, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    const preparedAppearance = world.prepareOrderChange(accept)
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()
    world.commitOrderChange(preparedAppearance)
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({ kind: 'pot', orderId: STARTER_ORDER_ID })

    const accepted = accept.after
    const remove = orderSession(accepted).planAbandon(STARTER_ORDER_ID)
    const preparedRemoval = world.prepareOrderChange(remove)
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({ kind: 'pot', orderId: STARTER_ORDER_ID })
    world.commitOrderChange(preparedRemoval)
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('rejects stale prepared pot changes and disposes discarded prepared appearance', () => {
    const world = mountOrderWorld()
    const pending = pendingStarterOrder()
    const accept = orderSession(pending).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })
    const disposeGeometry = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose')
    const prepared = world.prepareOrderChange(accept)
    const beforeDiscard = disposeGeometry.mock.calls.length

    world.discardOrderChange(prepared)
    expect(disposeGeometry.mock.calls.length).toBeGreaterThan(beforeDiscard)
    expect(() => world.prepareOrderChange(orderSession(accept.after).planAbandon(STARTER_ORDER_ID)))
      .toThrow(/stale order change/)
    world.dispose()
  })

  it('uses an injected authored goal and rejects missing goals without catalog fallback', () => {
    const customGoal = snapshotFromDiagram(new DiagramBuilder().build())
    const world = mountOrderWorld([], () => customGoal)
    const accept = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })

    const prepared = world.prepareOrderChange(accept)
    expect(latestPot().render.goal).toBe(customGoal)
    world.discardOrderChange(prepared)
    world.dispose()

    const missing = mountOrderWorld([], () => undefined)
    expect(() => missing.prepareOrderChange(accept)).toThrow(/missing authored goal/i)
    const unknown = {
      ...accept,
      orderId: 'unknown-order',
      before: { reputation: 0, orders: new Map([['unknown-order', { kind: 'pending' as const }]]) },
      after: {
        reputation: 0,
        orders: new Map([['unknown-order', { kind: 'accepted' as const, pot: { x: 0, z: -20, yaw: 0 } }]]),
      },
    }
    expect(() => missing.prepareOrderChange(unknown)).toThrow(/missing authored goal/i)
    missing.dispose()
  })

  it('updates cloned hologram line materials when the world resizes', () => {
    const world = mountOrderWorld()
    world.setPots([starterPot()])
    const hologram = latestPot().group.getObjectByName('goal-hologram')!
    const lines: LineMaterial[] = []
    hologram.traverse((object) => {
      if ('material' in object && (object as THREE.Mesh).material instanceof LineMaterial) {
        lines.push((object as THREE.Mesh).material as LineMaterial)
      }
    })
    expect(lines.length).toBeGreaterThan(0)

    world.resize(640, 360)

    expect(lines.map(({ resolution }) => resolution.toArray())).toEqual(lines.map(() => [640, 360]))
    world.dispose()
  })

  it('disposes each prepared appearance resource exactly once when discarded', () => {
    const world = mountOrderWorld()
    const accept = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })
    const prepared = world.prepareOrderChange(accept)
    const resources = potResourceSpies(latestPot())

    world.discardOrderChange(prepared)
    world.discardOrderChange(prepared)

    expectResourcesDisposedOnce(resources)
    world.dispose()
  })

  it('disposes each live pot resource exactly once when setPots replaces it', () => {
    const world = mountOrderWorld()
    world.setPots([starterPot()])
    const resources = potResourceSpies(latestPot())

    world.setPots([starterPot(4, -20)])

    expectResourcesDisposedOnce(resources)
    world.dispose()
  })

  it('disposes each live pot resource exactly once after committed removal', () => {
    const world = mountOrderWorld()
    const accepted = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 }).after
    world.setPots([starterPot()])
    const resources = potResourceSpies(latestPot())
    const removal = orderSession(accepted).planAbandon(STARTER_ORDER_ID)

    world.commitOrderChange(world.prepareOrderChange(removal))

    expectResourcesDisposedOnce(resources)
    world.dispose()
  })

  it('disposes each live pot resource exactly once when the world is disposed', () => {
    const world = mountOrderWorld()
    world.setPots([starterPot()])
    const resources = potResourceSpies(latestPot())

    world.dispose()
    world.dispose()

    expectResourcesDisposedOnce(resources)
  })

  it('removes a completed order pot only at its prepared commit', () => {
    const world = mountOrderWorld()
    const accepted = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 }).after
    world.setPots([starterPot()])
    world.setCamera({ eye: { x: 0, y: 0.55, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    const complete = {
      kind: 'complete' as const,
      orderId: STARTER_ORDER_ID,
      reward: 1,
      before: accepted,
      after: { reputation: 1, orders: new Map([[STARTER_ORDER_ID, { kind: 'completed' as const }]]) },
    }

    const prepared = world.prepareOrderChange(complete)
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({ kind: 'pot' })
    world.commitOrderChange(prepared)
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('discards prepared completion when save enqueue rejects without removing the accepted pot', async () => {
    // Catches the production renderer removing a pot or awarding progress before durable acceptance.
    const accepted = orderSession(pendingStarterOrder())
    accepted.commit(accepted.prepare(accepted.planAccept(
      STARTER_ORDER_ID,
      { x: 0, z: -20, yaw: 0 },
    )))
    const completion = accepted.planDelivery(STARTER_ORDER_ID, {
      name: 'starter source',
      diagram: ORDER_CATALOG[0]!.goal.diagram,
    })
    const world = mountOrderWorld()
    world.setPots([starterPot()])
    world.setCamera({ eye: { x: 0, y: 0.55, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    const writer = new SaveWriter('slot-a', {
      updateTree: async () => 1,
      insertTree: async () => 1,
      updateCamera: async () => {},
      acceptOrder: async () => {},
      abandonOrder: async () => {},
      completeOrder: async () => 1,
    })
    await writer.dispose()

    expect(() => publishOrderMutation(
      accepted,
      completion,
      world,
      (mutation) => {
        if (mutation.kind !== 'complete') throw new Error('expected completion')
        writer.completeOrder(mutation.orderId, mutation.reward)
      },
    )).toThrow('disposed')
    expect(accepted.progress).toBe(completion.before)
    expect(accepted.progress.reputation).toBe(0)
    expect(world.pointAtToolTarget(0, 0, null)).toMatchObject({
      kind: 'pot', orderId: STARTER_ORDER_ID,
    })
    world.dispose()
  })

  it('invalidates prepared pot tokens when setPots replaces authoritative state', () => {
    const world = mountOrderWorld()
    const accept = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })
    const prepared = world.prepareOrderChange(accept)

    world.setPots([])
    world.commitOrderChange(prepared)

    world.setCamera({ eye: { x: 0, y: 0.55, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    expect(world.pointAtToolTarget(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('invalidates prepared pot tokens when the world is disposed', () => {
    const world = mountOrderWorld()
    const accept = orderSession(pendingStarterOrder()).planAccept(STARTER_ORDER_ID, { x: 0, z: -20, yaw: 0 })
    const prepared = world.prepareOrderChange(accept)
    const incoming = latestPot()

    world.dispose()

    expect(incoming.group.parent).toBeNull()
    expect(() => world.commitOrderChange(prepared)).toThrow(/stale prepared order change/i)
    expect(() => world.discardOrderChange(prepared)).toThrow(/stale prepared order change/i)
    expect(incoming.group.parent).toBeNull()
  })

  it('points a branch through the same rotated placement used for rendering', () => {
    const orbit = blankTree('rotated-orbit', 17, -11)
    const rotated = { ...orbit, placement: { ...orbit.placement, yaw: Math.PI / 3 } }
    const world = mountGameWorld(container(), [rotated])
    pointCameraAtBranch(world, rotated)

    expect(world.pointAtBranch(0, 0, rotated.id)).toMatchObject({
      treeId: rotated.id,
      entity: { kind: 'branch', region: rotated.snapshot.diagram.root },
    })
    world.dispose()
  })

  it('picks a semantic entity and returns its shared focus in world placement', () => {
    const tree = blankTree('semantic-focus', 17, -11)
    const rotated = { ...tree, placement: { ...tree.placement, yaw: Math.PI / 3 } }
    const world = mountGameWorld(container(), [rotated])
    pointCameraAtBranch(world, rotated)

    expect(world.pickTreeFocus(0, 0, rotated.id)).toMatchObject({
      treeId: rotated.id,
      entity: { kind: 'branch', key: 'b:r0', region: 'r0' },
      worldFocus: { x: 17, y: 0.25, z: -11 },
    })
    world.dispose()
  })

  it('focuses empty space on the owning tree authoritative placed scene center', () => {
    const tree = blankTree('empty-focus', 17, -11)
    const rotated = { ...tree, placement: { ...tree.placement, yaw: Math.PI / 3 } }
    const world = mountGameWorld(container(), [rotated])
    pointCameraAtBranch(world, rotated)

    const focus = world.pickTreeFocus(0.9, 0.9, rotated.id)
    expect(focus).toMatchObject({ treeId: rotated.id, entity: null })
    expect(focus!.worldFocus.x).toBeCloseTo(17, 12)
    expect(focus!.worldFocus.y).toBeCloseTo(0.25, 12)
    expect(focus!.worldFocus.z).toBeCloseTo(-11, 12)
    world.dispose()
  })

  it('does not recenter from outgoing visible geometry absent from the committed scene', () => {
    const before = targetTree('transition-focus', 0, -20, 0)
    const after = blankTree(before.id, 0, -20)
    const beforeScene = scene3(before.snapshot.diagram)
    const outgoing = beforeScene.entities.find((entity) =>
      entity.kind === 'branch' && entity.region !== before.snapshot.diagram.root,
    )
    if (outgoing === undefined) throw new Error('fixture has no outgoing branch')
    const localFocus = focusPoint(outgoing.key, beforeScene.entities)
    if (localFocus === null) throw new Error('outgoing branch has no focus')
    const world = mountGameWorld(container(), [before], () => 0)
    world.setCamera({
      eye: { x: localFocus.x, y: localFocus.y, z: localFocus.z },
      forward: { x: 0, y: 0, z: -1 },
    })
    const prepared = world.prepareTreeChange({
      kind: 'update',
      treeId: before.id,
      before,
      after,
    })
    world.commitTreeChange(prepared)

    expect(world.pointAtBranch(0, 0, before.id)).toMatchObject({
      entity: { key: outgoing.key },
    })
    expect(world.pickTreeFocus(0, 0, before.id)).toBeNull()
    world.dispose()
  })

})
