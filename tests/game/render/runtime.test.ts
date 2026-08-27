import * as THREE from 'three'
import { describe, expect, it } from 'vitest'
import {
  GameTreeRuntime,
  type RenderTree,
  type TreeObjectBuilder,
} from '../../../src/game/render/runtime'
import type { TreeRenderAsset } from '../../../src/game/render/types'

function asset(center = { x: 0, y: 2, z: 0 }, entityCount = 4, radius = 5): TreeRenderAsset {
  const entities = Array.from({ length: entityCount }, (_, index) => ({
    kind: 'branch' as const,
    key: `branch-${index}`,
    polarity: 0 as const,
    pts: [{ x: 0, y: index, z: 0 }, { x: 0, y: index + 1, z: 0 }],
  }))
  return {
    bounds: { center, radius },
    lods: {
      full: { center, radius, entities },
      reduced: { center, radius, entities: entities.slice(0, 2) },
      marker: { color: '#ffffff', size: 1 },
    },
    hues: [],
    palette: { branch: '#ffffff', cutBranch: '#777777', baseWire: '#eeeeee' },
    widths: { branch: 0.1, curve: 0.05 },
    glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
  }
}

const tree = (id: string, x: number, z: number, diagramJson = 'a', yaw = 0, index = 0): RenderTree => ({
  id,
  diagramJson,
  placement: { id, index, x, z, yaw },
})

const resolve = (assets: Readonly<Record<string, TreeRenderAsset>>) => (diagramJson: string): TreeRenderAsset => {
  const resolved = assets[diagramJson]
  if (resolved === undefined) throw new Error(`unknown tree render asset '${diagramJson}'`)
  return resolved
}

const buildObject: TreeObjectBuilder = (_asset, renderTree) => {
  const group = new THREE.Group()
  group.name = renderTree.id
  group.position.set(renderTree.placement.x, 0, renderTree.placement.z)
  group.rotation.y = renderTree.placement.yaw
  group.add(new THREE.Object3D())
  return group
}

function settle(runtime: GameTreeRuntime): void {
  for (let frame = 0; frame < 1_000 && runtime.snapshot().pending > 0; frame++) {
    runtime.processOperations()
  }
  expect(runtime.snapshot().pending).toBe(0)
}

function cameraAt(x = 0, z = 0, lookZ = -1): THREE.PerspectiveCamera {
  const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
  camera.position.set(x, 1.7, z)
  camera.lookAt(x, 1.7, z + lookZ)
  return camera
}

describe('game tree runtime', () => {
  it('renders the latest placement and diagram for a stable tree ID', () => {
    const runtime = new GameTreeRuntime(
      resolve({ a: asset(), b: asset({ x: 1, y: 2, z: 0 }, 6) }),
      new THREE.Group(),
      buildObject,
    )
    runtime.setMode('raw')
    runtime.setTrees([tree('stable', 1, 2)])
    settle(runtime)

    runtime.setTrees([tree('stable', -9, 12, 'a', 0.75)])
    expect(runtime.residentObjects('stable')[0]!.position.toArray()).toEqual([-9, 0, 12])
    expect(runtime.residentObjects('stable')[0]!.rotation.y).toBe(0.75)

    runtime.setTrees([tree('stable', 5, -30, 'b', 0.25)])
    expect(runtime.snapshot()).toMatchObject({ logical: 1, resident: 0, representedEntities: 0 })
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({
      logical: 1,
      logicalEntities: 6,
      resident: 1,
      representedEntities: 6,
      error: null,
    })
    expect(runtime.residentObjects('stable')[0]!.position.toArray()).toEqual([5, 0, -30])
  })

  it('settles the current tree after a pending representation request is replaced', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), buildObject)
    runtime.setMode('raw')
    runtime.setTrees(Array.from({ length: 24 }, (_, index) => tree(`old-${index}`, index, 0)))
    runtime.setTrees([])
    runtime.setTrees([tree('current', 0, -20)])

    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({ logical: 1, resident: 1, representedEntities: 4 })
    expect(runtime.residentObjects().map(({ name }) => name)).toEqual(['current'])
  })

  it('suspends and resumes one tree without disturbing another tree', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), buildObject)
    const first = tree('first', 0, -20, 'a', 0, 0)
    const second = tree('second', 2, -20, 'a', 0, 1)
    runtime.setMode('raw')
    runtime.setTrees([first, second])
    settle(runtime)

    runtime.suspend('first')
    expect(runtime.snapshot()).toMatchObject({ logical: 2, resident: 1, representedEntities: 4 })
    expect(runtime.residentObjects().map(({ name }) => name)).toEqual(['second'])

    runtime.resume(first)
    settle(runtime)
    expect(runtime.snapshot()).toMatchObject({ logical: 2, resident: 2, representedEntities: 8 })
  })

  it('resumes a suspended tree with its changed diagram', () => {
    const runtime = new GameTreeRuntime(
      resolve({ a: asset(), b: asset({ x: 1, y: 2, z: 0 }, 6) }),
      new THREE.Group(),
      buildObject,
    )
    runtime.setMode('raw')
    runtime.setTrees([tree('changing', 0, -20, 'a')])
    settle(runtime)
    runtime.suspend('changing')

    runtime.resume(tree('changing', 0, -20, 'b'))
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({
      logicalEntities: 6,
      resident: 1,
      representedEntities: 6,
      error: null,
    })
  })

  it('chooses full, reduced, marker, and culled representations from camera distance', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), buildObject)
    runtime.setTrees([
      tree('full', 0, -20, 'a', 0, 0),
      tree('reduced', 0, -80, 'a', 0, 1),
      tree('marker', 0, -300, 'a', 0, 2),
      tree('culled', 0, -900, 'a', 0, 3),
    ])

    runtime.updateGame(cameraAt(), 780, 720)
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({
      logical: 4,
      visible: 3,
      resident: 3,
      full: 1,
      reduced: 1,
      marker: 1,
      culled: 1,
      representedEntities: 6,
      error: null,
    })
  })

  it('finds nearby logical interaction candidates before any representation is resident', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), buildObject)
    runtime.setTrees([
      tree('near', 0, -20),
      tree('bounds-touching', 5, -40),
      tree('off-ray', 6, -40),
      tree('past-reach', 0, -106),
      tree('behind', 0, 6),
    ])

    const candidates = runtime.interactionTrees(
      new THREE.Ray(new THREE.Vector3(0, 1.7, 0), new THREE.Vector3(0, 0, -1)),
      100,
    )

    expect(runtime.snapshot()).toMatchObject({ logical: 5, resident: 0 })
    expect(candidates.map(({ id }) => id).sort()).toEqual(['bounds-touching', 'near'])
  })

  it('uses the rotated derived bounds when deciding whether a tree is nearby', () => {
    const runtime = new GameTreeRuntime(
      resolve({ offset: asset({ x: 3, y: 1.7, z: 2 }, 4, 0.1) }),
      new THREE.Group(),
      buildObject,
    )
    runtime.setTrees([tree('offset', 10, -4, 'offset', Math.PI / 2)])
    const camera = cameraAt(12, -7, 1)

    runtime.updateGame(camera, 0.5, 720)
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({ visible: 1, full: 1, resident: 1 })
  })

  it('makes removal authoritative immediately and settles without a representation', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), buildObject)
    runtime.setMode('raw')
    runtime.setTrees([tree('removed', 0, -20)])
    settle(runtime)

    runtime.setTrees([])

    expect(runtime.snapshot()).toMatchObject({ logical: 0, resident: 0, representedEntities: 0 })
    settle(runtime)
    expect(runtime.residentObjects()).toEqual([])
  })

  it('reports representation failure and recovers after the requested tree changes', () => {
    let canRender = false
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (...args) => {
      if (!canRender) throw new Error('render failed')
      return buildObject(...args)
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('moving', 0, -20)])
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({
      resident: 0,
      failureCount: 1,
      error: "tree 'moving' full representation failed: render failed",
    })

    canRender = true
    runtime.setTrees([tree('moving', 1, -20)])
    settle(runtime)

    expect(runtime.snapshot()).toMatchObject({ resident: 1, failureCount: 0, error: null })
  })

  it('reports analytic lights introduced by a representation', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (_asset, renderTree) => {
      const group = buildObject(_asset, renderTree, 'full', true)
      group.add(new THREE.PointLight('#ffffff'))
      return group
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('lit', 0, -20)])
    settle(runtime)

    expect(runtime.snapshot().pointLights).toBe(1)
  })
})
