import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

const host = vi.hoisted(() => ({
  attached: false,
  canvas: null as HTMLCanvasElement | null,
  canvasAttributes: new Map<string, string>(),
  rendererDisposals: 0,
  rendererPixelRatio: 0,
  composerDisposals: 0,
  composerRenders: 0,
  composerPixelRatio: 0,
  composerSize: [0, 0] as [number, number],
  bloomSize: [0, 0] as [number, number],
  bloomDisposals: 0,
  smaaDisposals: 0,
  outputDisposals: 0,
  glowSyncs: 0,
  glowDisposals: 0,
}))

vi.mock('three', async (importOriginal) => {
  const actual = await importOriginal<typeof import('three')>()

  class TestWebGlRenderer {
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
      const canvas = {
        width: 0,
        height: 0,
        setAttribute(name: string, value: string) {
          host.canvasAttributes.set(name, value)
        },
        remove() {
          host.attached = false
        },
      } as unknown as HTMLCanvasElement
      this.domElement = canvas
      host.canvas = canvas
    }

    public setPixelRatio(ratio: number): void {
      host.rendererPixelRatio = ratio
    }

    public setSize(width: number, height: number): void {
      this.domElement.width = width
      this.domElement.height = height
    }

    public dispose(): void {
      host.rendererDisposals++
    }
  }

  return { ...actual, WebGLRenderer: TestWebGlRenderer }
})

vi.mock('three/examples/jsm/postprocessing/EffectComposer.js', () => ({
  EffectComposer: class TestEffectComposer {
    public constructor(private readonly renderer: {
      readonly info: { readonly render: { calls: number; triangles: number } }
    }) {}

    public addPass(): void {}

    public setPixelRatio(ratio: number): void {
      host.composerPixelRatio = ratio
    }

    public setSize(width: number, height: number): void {
      host.composerSize = [width, height]
    }

    public render(): void {
      host.composerRenders++
      this.renderer.info.render.calls = 3
      this.renderer.info.render.triangles = 7
    }

    public dispose(): void {
      host.composerDisposals++
    }
  },
}))

vi.mock('three/examples/jsm/postprocessing/RenderPass.js', () => ({
  RenderPass: class TestRenderPass {},
}))

vi.mock('three/examples/jsm/postprocessing/UnrealBloomPass.js', () => ({
  UnrealBloomPass: class TestUnrealBloomPass {
    public setSize(width: number, height: number): void {
      host.bloomSize = [width, height]
    }

    public dispose(): void {
      host.bloomDisposals++
    }
  },
}))

vi.mock('three/examples/jsm/postprocessing/SMAAPass.js', () => ({
  SMAAPass: class TestSmaaPass {
    public dispose(): void {
      host.smaaDisposals++
    }
  },
}))

vi.mock('three/examples/jsm/postprocessing/OutputPass.js', () => ({
  OutputPass: class TestOutputPass {
    public dispose(): void {
      host.outputDisposals++
    }
  },
}))

vi.mock('../../../src/game/render/glow-render', () => ({
  mountGlowRenderer: () => ({
    sync: () => { host.glowSyncs++ },
    dispose: () => { host.glowDisposals++ },
  }),
}))

import type { GameTree } from '../../../src/game/model'
import { mountGameWorld } from '../../../src/game/render/world'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson } from '../../../src/kernel/diagram/json'
import { applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { scene3 } from '../../../src/view3d/scene'

beforeEach(() => {
  host.attached = false
  host.canvas = null
  host.canvasAttributes.clear()
  host.rendererDisposals = 0
  host.rendererPixelRatio = 0
  host.composerDisposals = 0
  host.composerRenders = 0
  host.composerPixelRatio = 0
  host.composerSize = [0, 0]
  host.bloomSize = [0, 0]
  host.bloomDisposals = 0
  host.smaaDisposals = 0
  host.outputDisposals = 0
  host.glowSyncs = 0
  host.glowDisposals = 0
  vi.stubGlobal('window', { devicePixelRatio: 2 })
})

afterEach(() => {
  vi.unstubAllGlobals()
})

describe('production game world', () => {
  it('owns initial generic trees, resize/render routing, and idempotent teardown', () => {
    const diagram = new DiagramBuilder().build()
    const tree: GameTree = {
      id: 'tree-a',
      diagram,
      diagramJson: JSON.stringify(diagramToJson(diagram)),
      placement: { x: 0, z: -20, yaw: 0 },
    }
    const container = {
      appendChild(node: HTMLCanvasElement) {
        host.attached = true
        expect(node).toBe(host.canvas)
      },
    } as unknown as HTMLElement

    const world = mountGameWorld(container, [tree])
    world.setCamera({ eye: { x: 0, y: 1.7, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    world.setRenderMode('raw')
    world.resize(640, 360)
    const rendered = world.render(16)

    expect(world.canvas).toBe(host.canvas)
    expect(host.attached).toBe(true)
    expect(host.canvasAttributes.get('aria-label')).toBe('Walkable proof-tree game world')
    expect([world.canvas.width, world.canvas.height]).toEqual([640, 360])
    expect(host.rendererPixelRatio).toBe(1.5)
    expect(host.composerPixelRatio).toBe(1.5)
    expect(host.composerSize).toEqual([640, 360])
    expect(host.bloomSize).toEqual([960, 540])
    expect(host.composerRenders).toBe(1)
    expect(host.glowSyncs).toBe(1)
    expect(rendered).toMatchObject({
      antialiasingMethod: 'smaa',
      drawCalls: 3,
      triangles: 7,
      logical: 1,
      visible: 1,
      resident: 1,
      full: 1,
      pending: 0,
      pointLights: 0,
      representedEntities: 1,
      representationErrors: 0,
      error: null,
    })

    world.dispose()
    world.dispose()

    expect(host.attached).toBe(false)
    expect(host.rendererDisposals).toBe(1)
    expect(host.composerDisposals).toBe(1)
    expect(host.bloomDisposals).toBe(1)
    expect(host.smaaDisposals).toBe(1)
    expect(host.outputDisposals).toBe(1)
    expect(host.glowDisposals).toBe(1)
  })

  it('picks ordinary visible geometry and completes a real 350 ms tree tween', () => {
    const diagram = new DiagramBuilder().build()
    const diagramJson = JSON.stringify(diagramToJson(diagram))
    const tree: GameTree = {
      id: 'tree-a', diagram, diagramJson,
      placement: { x: 0, z: -20, yaw: 0 },
    }
    const container = {
      appendChild() { host.attached = true },
    } as unknown as HTMLElement
    const world = mountGameWorld(container, [tree])
    const rendered = scene3(diagram)
    const branch = rendered.entities[0]!
    if (!('pts' in branch)) throw new Error('expected branch fixture')
    const point = branch.pts[0]!
    const eye = { x: point.x, y: point.y, z: point.z + 20 }
    world.setCamera({ eye, forward: { x: 0, y: 0, z: -1 } })
    world.setRenderMode('raw')
    world.render(0)

    expect(world.pointAt(0, 0, 100, null)).toMatchObject({
      treeId: 'tree-a', entityKey: 'b:r0',
    })

    const after = applyDoubleCutIntro(diagram, {
      region: diagram.root, regions: [], nodes: [], wires: [],
    })
    world.beginTreeTween('tree-a', diagram, after, 0)
    expect(world.render(349).resident).toBe(0)
    expect(world.render(350).resident).toBe(1)
    world.dispose()
  })
})
