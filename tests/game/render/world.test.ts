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
    const world = mountGameWorld(container(), [tree])
    pointCameraAtBranch(world, tree)
    world.setRenderMode('raw')
    world.render(0)

    expect(world.pointAt(0, 0, null)).toMatchObject({
      treeId: 'tree-a', entityKey: 'b:r0',
    })

    const after = applyDoubleCutIntro(tree.diagram, {
      region: tree.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.beginTreeTween(tree.id, tree.diagram, after, 0)

    expect(world.render(349).resident).toBe(0)
    expect(world.render(350)).toMatchObject({ resident: 1, representedEntities: 3 })
    world.dispose()
  })

  it('points a production branch just inside 100 units but not just outside it', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree])
    const branch = scene3(tree.diagram).entities[0]!
    if (!('pts' in branch)) throw new Error('expected production branch')
    const point = branch.pts[0]!
    world.setRenderMode('raw')
    world.setCamera({
      eye: { x: point.x, y: point.y, z: point.z + tree.placement.z + 99.999 },
      forward: { x: 0, y: 0, z: -1 },
    })
    world.render(0)

    expect(world.pointAt(0, 0, null)).toMatchObject({ treeId: 'tree-a', entityKey: 'b:r0' })

    world.setCamera({
      eye: { x: point.x, y: point.y, z: point.z + tree.placement.z + 100.001 },
      forward: { x: 0, y: 0, z: -1 },
    })
    expect(world.pointAt(0, 0, null)).toBeNull()
    world.dispose()
  })

  it('keeps removal authoritative while a tween is active', () => {
    const tree = blankTree()
    const world = mountGameWorld(container(), [tree])
    const after = applyDoubleCutIntro(tree.diagram, {
      region: tree.diagram.root, regions: [], nodes: [], wires: [],
    })
    world.setRenderMode('raw')
    world.render(0)
    world.beginTreeTween(tree.id, tree.diagram, after, 0)

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
    const world = mountGameWorld(container(), [original])
    world.setRenderMode('raw')
    world.render(0)
    world.beginTreeTween(original.id, original.diagram, staleTarget, 0)

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

  it('settles 2,000 production-built raw trees without representation failures or analytic lights', () => {
    const diagram = new DiagramBuilder().build()
    const diagramJson = JSON.stringify(diagramToJson(diagram))
    const trees: GameTree[] = Array.from({ length: 2_000 }, (_, index) => ({
      id: `tree-${index}`,
      diagram,
      diagramJson,
      placement: {
        x: (index % 50) * 18,
        z: -20 - Math.floor(index / 50) * 18,
        yaw: (index * 0.37) % (Math.PI * 2),
      },
    }))
    const world = mountGameWorld(container(), trees)
    world.setRenderMode('raw')
    world.resize(800, 450)

    let rendered = world.render(0)
    for (let frame = 1; rendered.pending > 0 && frame <= 1_000; frame++) {
      rendered = world.render(frame * 16)
    }

    expect(rendered).toMatchObject({
      logical: 2_000,
      visible: 2_000,
      resident: 2_000,
      full: 2_000,
      pending: 0,
      pointLights: 0,
      representedEntities: 2_000,
      representationErrors: 0,
      error: null,
    })
    world.dispose()
  })
})
