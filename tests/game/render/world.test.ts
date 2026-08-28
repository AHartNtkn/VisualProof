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

vi.mock('../../../src/game/render/assets', async (importOriginal) => {
  const actual = await importOriginal<typeof import('../../../src/game/render/assets')>()

  class TestTreeRenderAssetCache extends actual.TreeRenderAssetCache {
    public override get(diagramJson: string, diagram: import('../../../src/kernel/diagram').Diagram) {
      const asset = super.get(diagramJson, diagram)
      if (!diagramJson.startsWith('target:')) return asset

      const center = { x: 3, y: 2, z: 4 }
      const radius = 5
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

function targetTree(id: string, x: number, z: number, yaw: number): GameTree {
  const tree = blankTree(id, x, z)
  return {
    ...tree,
    diagramJson: `target:${id}`,
    placement: { x, z, yaw },
  }
}

function container(): HTMLElement {
  return {
    appendChild() { host.attached = true },
  } as unknown as HTMLElement
}

describe('production game world', () => {
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

})
