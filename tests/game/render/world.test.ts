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

import type { GameTree } from '../../../src/game/model'
import { mountGameWorld } from '../../../src/game/render/world'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson } from '../../../src/kernel/diagram/json'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { scene3 } from '../../../src/view3d/scene'

beforeEach(() => {
  host.attached = false
  host.canvasAttributes.clear()
  host.framePresented = false
  host.rendererAcceptedFrame = false
  host.viewport.renderer = [0, 0]
  host.viewport.postprocess = [0, 0]
  host.viewport.scaledEffect = [0, 0]
  host.resources.length = 0
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
  vi.unstubAllGlobals()
})

function blankTree(id = 'tree-a', x = 0, z = -20): GameTree {
  const diagram = new DiagramBuilder().build()
  return {
    id,
    diagram,
    diagramJson: JSON.stringify(diagramToJson(diagram)),
    placement: { x, z, yaw: 0 },
  }
}

function representativeTree(id = 'representative', x = 0, z = 0): GameTree {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const outer = builder.atom(builder.root, relSig([IOTA]))
  const inner = builder.atom(cut, relSig([IOTA]))
  const reference = builder.ref(cut, 'Def', relSig([IOTA]))
  builder.wire([
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
    { node: reference, port: { kind: 'arg', index: 0 } },
  ])
  const diagram = builder.build()
  return {
    id,
    diagram,
    diagramJson: JSON.stringify(diagramToJson(diagram)),
    placement: { x, z, yaw: 0 },
  }
}

function container(): HTMLElement {
  return {
    appendChild() { host.attached = true },
  } as unknown as HTMLElement
}

function pointCameraAtBranch(world: ReturnType<typeof mountGameWorld>, tree: GameTree): void {
  const branch = scene3(tree.diagram).entities[0]!
  if (!('pts' in branch)) throw new Error('expected production branch')
  const point = branch.pts[0]!
  world.setCamera({
    eye: {
      x: tree.placement.x + point.x,
      y: point.y,
      z: tree.placement.z + point.z + 20,
    },
    forward: { x: 0, y: 0, z: -1 },
  })
}

describe('production game world', () => {
  it('mounts a generic tree, resizes its canvas, renders without representation failures, and tears down', () => {
    const world = mountGameWorld(container(), [blankTree()])
    world.setCamera({ eye: { x: 0, y: 1.7, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    world.setRenderMode('raw')
    world.resize(640, 360)

    const rendered = world.render(16)

    expect(host.attached).toBe(true)
    expect(host.canvasAttributes.get('aria-label')).toBe('Walkable proof-tree game world')
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

  it('points ordinary full-detail geometry and completes a real 350 ms tree tween', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    pointCameraAtBranch(world, tree)
    world.setRenderMode('raw')
    world.render(0)

    expect(world.pointAt(0, 0, null)).toMatchObject({
      treeId: 'tree-a', entityKey: 'b:r0',
    })

    const after = applyDoubleCutIntro(tree.diagram, {
      region: tree.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.beginTreeTween(tree.id, tree.diagram, after)

    expect(world.render(349).resident).toBe(0)
    expect(world.render(350)).toMatchObject({ resident: 1, representedEntities: 3 })
    world.dispose()
  })

  it('points a branch inside 100 units in normal game mode without changing its marker LOD', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    const branch = scene3(tree.diagram).entities[0]!
    if (!('pts' in branch)) throw new Error('expected production branch')
    const point = branch.pts[0]!
    world.resize(800, 450)
    world.setCamera({
      eye: { x: point.x, y: point.y, z: point.z + tree.placement.z + 99.999 },
      forward: { x: 0, y: 0, z: -1 },
    })
    const near = world.render(0)

    expect(near).toMatchObject({ marker: 1, full: 0, reduced: 0 })
    expect(world.pointAt(0, 0, null)).toMatchObject({ treeId: 'tree-a', entityKey: 'b:r0' })
    expect(world.pointAtBranch(0, 0, null)).toMatchObject({ treeId: 'tree-a', entityKey: 'b:r0' })
    expect(world.render(16)).toMatchObject({ marker: 1, full: 0, reduced: 0 })

    world.setCamera({
      eye: { x: point.x, y: point.y, z: point.z + tree.placement.z + 100.001 },
      forward: { x: 0, y: 0, z: -1 },
    })
    expect(world.pointAt(0, 0, null)).toBeNull()
    expect(world.pointAtBranch(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('points full derived entities while the normal-game representation remains reduced', () => {
    const tree = representativeTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    world.resize(800, 450)
    world.setCamera({ eye: { x: 80, y: 0.7, z: 0 }, forward: { x: -1, y: 0, z: 0 } })

    expect(world.render(0)).toMatchObject({ reduced: 1, full: 0, marker: 0 })
    expect(world.pointAt(0, 0, null)).toMatchObject({ treeId: tree.id })
    expect(world.pointAt(0, 0, null)?.entityKey.startsWith('b:')).toBe(false)
    expect(world.pointAtBranch(0, 0, null)).toMatchObject({ treeId: tree.id, entityKey: 'b:r0' })
    expect(world.render(16)).toMatchObject({ reduced: 1, full: 0, marker: 0 })
    world.dispose()
  })

  it('points pending and unresident normal-game trees only within reach and the orbit target', () => {
    const near = blankTree('near', 0, -20)
    const background = blankTree('background', 0, -30)
    const far = blankTree('far', 0, -120)
    const world = mountGameWorld(container(), [near, background, far], () => 0)
    world.resize(800, 450)
    pointCameraAtBranch(world, near)

    expect(world.pointAt(0, 0, 'near')).toMatchObject({ treeId: near.id, entityKey: 'b:r0' })
    expect(world.pointAtBranch(0, 0, 'near')).toMatchObject({ treeId: near.id, entityKey: 'b:r0' })
    expect(world.pointAt(0, 0, 'background')).toMatchObject({ treeId: background.id })
    expect(world.pointAt(0, 0, 'far')).toBeNull()
    expect(world.render(0)).toMatchObject({ full: 0, reduced: 0, marker: 3 })

    const after = applyDoubleCutIntro(near.diagram, {
      region: near.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.setTrees([{ ...near, diagram: after, diagramJson: JSON.stringify(diagramToJson(after)) }])
    expect(world.pointAt(0, 0, 'near')).toMatchObject({ treeId: near.id })
    expect(world.render(16)).toMatchObject({ full: 0, reduced: 1, marker: 0 })
    world.dispose()
  })

  it('restricts normal-game pointing to the orbit target when nearby trees overlap', () => {
    const background = blankTree('background')
    const orbit = blankTree('orbit')
    const world = mountGameWorld(container(), [background, orbit], () => 0)
    const branch = scene3(orbit.diagram).entities[0]!
    if (!('pts' in branch)) throw new Error('expected production branch')
    const point = branch.pts[0]!
    world.resize(800, 450)
    world.setCamera({
      eye: { x: point.x, y: point.y, z: point.z + orbit.placement.z + 99 },
      forward: { x: 0, y: 0, z: -1 },
    })
    const frame = world.render(0)

    expect(frame).toMatchObject({ marker: 2, full: 0, reduced: 0 })
    expect(world.pointAt(0, 0, 'orbit')).toMatchObject({
      treeId: 'orbit', entityKey: 'b:r0',
    })
    expect(world.pointAtBranch(0, 0, 'orbit')).toMatchObject({
      treeId: 'orbit', entityKey: 'b:r0',
    })
    world.dispose()
  })

  it('lets the double-cut tool point through nearer ordinary parts to the closest branch', () => {
    const tree = representativeTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    world.setRenderMode('raw')
    world.resize(800, 450)
    world.setCamera({
      eye: { x: 10, y: 0.7, z: 0 },
      forward: { x: -1, y: 0, z: 0 },
    })
    world.render(0)

    const ordinary = world.pointAt(0, 0, null)
    expect(ordinary?.treeId).toBe(tree.id)
    expect(ordinary?.entityKey.startsWith('b:')).toBe(false)
    expect(world.pointAtBranch(0, 0, null)).toMatchObject({
      treeId: tree.id,
      entityKey: 'b:r0',
    })
    world.dispose()
  })

  it('chooses the closest branch across static trees and trees currently tweening', () => {
    const staticTree = blankTree('static', 0, -20)
    const tweeningTree = blankTree('tweening', 0, -40)
    const world = mountGameWorld(container(), [staticTree, tweeningTree], () => 0)
    const after = applyDoubleCutIntro(tweeningTree.diagram, {
      region: tweeningTree.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.setRenderMode('raw')
    world.resize(800, 450)
    world.setCamera({ eye: { x: 0, y: 0, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    world.render(0)
    world.beginTreeTween(tweeningTree.id, tweeningTree.diagram, after)
    world.render(100)

    expect(world.pointAtBranch(0, 0, null)).toMatchObject({
      treeId: staticTree.id,
      entityKey: 'b:r0',
    })
    world.dispose()
  })

  it('keeps removal authoritative while a tween is active', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree], () => 0)
    const after = applyDoubleCutIntro(tree.diagram, {
      region: tree.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.setRenderMode('raw')
    world.render(0)
    world.beginTreeTween(tree.id, tree.diagram, after)

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
      diagram: replacementDiagram,
      diagramJson: JSON.stringify(diagramToJson(replacementDiagram)),
      placement: { x: 50, z: -60, yaw: 0 },
    }
    const staleTarget = applyDoubleCutIntro(original.diagram, {
      region: original.diagram.root, regions: [], nodes: [], wires: [],
    })
    const world = mountGameWorld(container(), [original], () => 0)
    world.setRenderMode('raw')
    world.render(0)
    world.beginTreeTween(original.id, original.diagram, staleTarget)

    world.setTrees([replacement])
    pointCameraAtBranch(world, replacement)
    const rendered = world.render(350)

    expect(rendered).toMatchObject({
      logical: 1,
      resident: 1,
      representedEntities: scene3(replacementDiagram).entities.length,
    })
    expect(world.pointAt(0, 0, null)).toMatchObject({ treeId: original.id })
    world.dispose()
  })

})
