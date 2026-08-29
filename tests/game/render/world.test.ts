import * as THREE from 'three'
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

import type { GameTree } from '../../../src/game/model'
import { snapshotFromDiagram } from '../../../src/game/diagram-snapshot'
import { mountGameWorld } from '../../../src/game/render/world'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { scene3 } from '../../../src/view3d/scene'
import type { TreeMutation } from '../../../src/game/session'
import { gameSession, publishTreeMutation } from '../../../src/game/session'
import { SaveWriter } from '../../../src/game/save-writer'
import { treeUpdateFromGameTree } from '../../../src/game/save-client'

beforeEach(() => {
  host.attached = false
  host.canvasAttributes.clear()
  host.framePresented = false
  host.rendererAcceptedFrame = false
  host.viewport.renderer = [0, 0]
  host.viewport.postprocess = [0, 0]
  host.viewport.scaledEffect = [0, 0]
  host.resources.length = 0
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

describe('production game world', () => {
  it('rejects preparation against a stale tree without changing the live target', () => {
    const current = targetTree('tree', 10, -20, Math.PI / 2)
    const stale = blankTree('tree', 10, -20)
    const after = { ...stale, snapshot: snapshotFromDiagram(applyDoubleCutIntro(stale.snapshot.diagram, {
      region: stale.snapshot.diagram.root, regions: [], nodes: [], wires: [],
    })) }
    const mutation: TreeMutation = { treeId: current.id, before: stale, after }
    const world = mountGameWorld(container(), [current])
    world.setCamera({ eye: { x: 14, y: 2, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(() => world.prepareTreeUpdate(mutation)).toThrow(/stale tree mutation/)
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
    const mutation: TreeMutation = { treeId: before.id, before, after }
    const world = mountGameWorld(container(), [before], () => 0)

    const prepared = world.prepareTreeUpdate(mutation)
    world.commitTreeUpdate(prepared)
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
    const prepared = world.prepareTreeUpdate({ treeId: before.id, before, after })
    const beforeCommit = disposeGeometry.mock.calls.length

    world.commitTreeUpdate(prepared)
    const afterFirstCommit = disposeGeometry.mock.calls.length
    world.commitTreeUpdate(prepared)

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
    const prepared = world.prepareTreeUpdate({ treeId: before.id, before, after })
    const beforeReplacement = disposeGeometry.mock.calls.length

    world.setTrees([replacement])
    world.commitTreeUpdate(prepared)

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
    const prepared = world.prepareTreeUpdate({ treeId: before.id, before, after })
    const beforeDispose = disposeGeometry.mock.calls.length

    world.dispose()

    expect(disposeGeometry.mock.calls.length).toBeGreaterThan(beforeDispose)
    expect(() => world.commitTreeUpdate(prepared)).not.toThrow()
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
    const first = world.prepareTreeUpdate({ treeId: before.id, before, after })

    expect(() => world.prepareTreeUpdate({ treeId: before.id, before, after }))
      .toThrow(/already prepared/)

    world.commitTreeUpdate(first)
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
      updateCamera: async () => {},
    })
    await writer.dispose()
    expect(() => publishTreeMutation(
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
    const prepared = world.prepareTreeUpdate({ treeId: tree.id, before: tree, after: afterTree })
    world.commitTreeUpdate(prepared)

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
    const prepared = world.prepareTreeUpdate({
      treeId: original.id, before: original, after: staleTree,
    })
    world.commitTreeUpdate(prepared)

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

})
