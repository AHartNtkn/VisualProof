import * as THREE from 'three'
import { describe, expect, it, vi } from 'vitest'
import {
  GameWorldLifecycle,
  GameTreeRuntime,
  makeTreeMaterialSource,
  treeWorldSphere,
  type RenderTree,
  type TreeObjectBuilder,
} from '../../../src/game/render/runtime'
import type { TreeRenderAsset } from '../../../src/game/render/types'

function asset(center = { x: 0, y: 2, z: 0 }, entityCount = 4): TreeRenderAsset {
  const entities = Array.from({ length: entityCount }, (_, index) => ({
    kind: 'branch' as const,
    key: `branch-${index}`,
    polarity: 0 as const,
    pts: [{ x: 0, y: index, z: 0 }, { x: 0, y: index + 1, z: 0 }],
  }))
  return {
    bounds: { center, radius: 5 },
    lods: {
      full: { center, radius: 5, entities },
      reduced: { center, radius: 5, entities: entities.slice(0, 2) },
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

function objectBuilder(): {
  readonly build: TreeObjectBuilder
  readonly groups: THREE.Group[]
  readonly geometries: THREE.BufferGeometry[]
} {
  const groups: THREE.Group[] = []
  const geometries: THREE.BufferGeometry[] = []
  return {
    groups,
    geometries,
    build(_asset, tree, lod, raw) {
      const group = new THREE.Group()
      const geometry = new THREE.BufferGeometry()
      const mesh = new THREE.Mesh(geometry, new THREE.MeshBasicMaterial())
      group.name = tree.id
      group.userData['treeIndex'] = tree.placement.index
      group.userData['representation'] = raw ? 'raw' : lod
      group.position.set(tree.placement.x, 0, tree.placement.z)
      group.rotation.y = tree.placement.yaw
      group.add(mesh)
      groups.push(group)
      geometries.push(geometry)
      return group
    },
  }
}

describe('game tree runtime', () => {
  it('rotates an off-center derived bound before translating its world sphere', () => {
    const sphere = treeWorldSphere(tree('off-center', 10, -4, 'a', Math.PI / 2), asset({ x: 3, y: 7, z: 2 }))

    expect(sphere.center.x).toBeCloseTo(12)
    expect(sphere.center.y).toBe(7)
    expect(sphere.center.z).toBeCloseTo(-7)
    expect(sphere.radius).toBe(5)
  })

  it('diffs stable IDs, updates placement in place, and replaces only a changed render asset', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const release = vi.fn((group: THREE.Group) => {
      for (const child of group.children) (child as THREE.Mesh).geometry.dispose()
    })
    const runtime = new GameTreeRuntime(
      resolve({ a: asset(), b: asset({ x: 1, y: 2, z: 0 }, 6) }),
      parent,
      factory.build,
      release,
    )
    runtime.setMode('raw')
    runtime.setTrees([tree('stable', 1, 2)])
    expect(runtime.processOperations(12).completed).toBe(1)
    const original = factory.groups[0]!

    runtime.setTrees([tree('stable', -9, 12, 'a', 0.75)])

    expect(runtime.snapshot()).toMatchObject({ logical: 1, logicalEntities: 4, pending: 0, resident: 1 })
    expect(original.position.toArray()).toEqual([-9, 0, 12])
    expect(original.rotation.y).toBe(0.75)
    expect(factory.groups).toHaveLength(1)

    runtime.setTrees([tree('stable', -9, 12, 'b', 0.75)])
    expect(original.visible).toBe(false)
    expect(original.parent).toBeNull()
    expect(runtime.processOperations(12).completed).toBe(1)

    expect(factory.groups).toHaveLength(2)
    expect(factory.groups[1]!.userData['representation']).toBe('raw')
    expect(release).toHaveBeenCalledTimes(1)
    expect(runtime.snapshot()).toMatchObject({ logical: 1, logicalEntities: 6, pending: 0, resident: 1 })
  })

  it('shares one twelve-operation budget between retired disposal and new creation', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const release = vi.fn()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build, release)
    runtime.setMode('raw')
    runtime.setTrees(Array.from({ length: 6 }, (_, index) => tree(`old-${index}`, index, 0)))
    expect(runtime.processOperations(12).completed).toBe(6)

    runtime.setTrees([])
    runtime.setTrees(Array.from({ length: 12 }, (_, index) => tree(`new-${index}`, index, -20)))
    const buildsBefore = factory.groups.length
    const releasesBefore = release.mock.calls.length

    expect(runtime.processOperations(12)).toEqual({ completed: 12, examined: 12 })
    expect(factory.groups.length - buildsBefore).toBe(6)
    expect(release.mock.calls.length - releasesBefore).toBe(6)
    expect(runtime.snapshot()).toMatchObject({ logical: 12, resident: 6, pending: 6 })
  })

  it('examines bounded queue entries after a canceled backlog and reaches new live work', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build)
    runtime.setMode('raw')
    runtime.setTrees(Array.from({ length: 2_000 }, (_, index) => tree(`canceled-${index}`, index, 0)))
    expect(runtime.snapshot().pending).toBe(2_000)
    runtime.setTrees([])
    expect(runtime.snapshot().pending).toBe(0)
    runtime.setTrees([tree('live', 0, -20)])

    const work = runtime.processOperations(1)

    expect(work).toEqual({ completed: 1, examined: 1 })
    expect(parent.children.map(({ name }) => name)).toEqual(['live'])
    expect(runtime.snapshot()).toMatchObject({ pending: 0, resident: 1 })
  })

  it('hides a game representation immediately when Raw needs the same full LOD rebuilt', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build)
    runtime.setTrees([tree('same-lod', 0, -20)])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)
    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)
    const gameObject = factory.groups[0]!
    expect(gameObject.userData['representation']).toBe('full')

    runtime.setMode('raw')

    expect(gameObject.visible).toBe(false)
    expect(gameObject.parent).toBeNull()
    expect(runtime.snapshot()).toMatchObject({ full: 1, resident: 0, pending: 1 })
    runtime.processOperations(12)
    expect(factory.groups[1]!.userData['representation']).toBe('raw')
  })

  it('suspends and resumes only one generic tree without coupling residency to another tree', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build)
    const first = tree('first', 0, -20, 'a', 0, 0)
    const second = tree('second', 2, -20, 'a', 0, 1)
    runtime.setMode('raw')
    runtime.setTrees([first, second])
    runtime.processOperations(12)

    runtime.suspend('first')

    expect(runtime.residentObjects('first')).toEqual([])
    expect(runtime.residentObjects('second').map(({ name }) => name)).toEqual(['second'])
    expect(runtime.snapshot()).toMatchObject({ logical: 2, resident: 1 })

    runtime.resume(first)

    expect(runtime.residentObjects().map(({ name }) => name).sort()).toEqual(['first', 'second'])
    expect(runtime.snapshot()).toMatchObject({ logical: 2, resident: 2, pending: 0 })
  })

  it('rebuilds from changed diagram bytes before a suspended tree becomes resident again', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(
      resolve({ a: asset(), b: asset({ x: 1, y: 2, z: 0 }, 6) }),
      parent,
      factory.build,
    )
    const original = tree('changing', 0, -20, 'a')
    runtime.setMode('raw')
    runtime.setTrees([original])
    runtime.processOperations(12)
    runtime.suspend(original.id)

    runtime.resume(tree('changing', 0, -20, 'b'))

    expect(runtime.residentObjects('changing')).toEqual([])
    expect(runtime.snapshot()).toMatchObject({ logicalEntities: 6, resident: 0, pending: 1 })
    runtime.processOperations(12)
    expect(factory.groups).toHaveLength(2)
    expect(runtime.residentObjects('changing')).toEqual([factory.groups[1]])
  })

  it('hides and detaches a removed tree immediately, then releases its geometry from the queue', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build)
    runtime.setMode('raw')
    runtime.setTrees([tree('removed', 0, 0)])
    runtime.processOperations(12)
    const group = factory.groups[0]!
    const dispose = vi.spyOn(factory.geometries[0]!, 'dispose')

    runtime.setTrees([])

    expect(group.visible).toBe(false)
    expect(group.parent).toBeNull()
    expect(dispose).not.toHaveBeenCalled()
    expect(runtime.snapshot()).toMatchObject({ logical: 0, resident: 0, pending: 1 })

    expect(runtime.processOperations(12).completed).toBe(1)
    expect(dispose).toHaveBeenCalledTimes(1)
    expect(runtime.snapshot().pending).toBe(0)
  })

  it('visits spatial candidates and prior render states without scanning every logical tree', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), parent, factory.build)
    const farTrees = Array.from({ length: 500 }, (_, index) => tree(`far-${index}`, 10_000 + index * 20, 10_000))
    runtime.setTrees([tree('near', 0, -20), ...farTrees])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)

    const updated = runtime.updateGame(camera, 100, 720)

    expect(updated.visited).toBe(1)
    expect(runtime.snapshot()).toMatchObject({ logical: 501, logicalEntities: 2004, visible: 1 })

    runtime.setTrees([tree('near', 0, -20), ...farTrees.slice(0, 199)])
    expect(runtime.snapshot()).toMatchObject({ logical: 200, logicalEntities: 800 })
    expect(runtime.updateGame(camera, 100, 720).visited).toBe(1)
  })

  it('uses full detail when the camera is inside a derived sphere and looks away from its center', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset({ x: 0, y: 1.7, z: -4 }) }), parent, factory.build)
    runtime.setTrees([tree('surrounding', 0, 0)])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, 1)

    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ visible: 1, full: 1, resident: 1 })
    expect(factory.groups[0]!.userData['representation']).toBe('full')
  })

  it('derives bounded material radiance from the immutable render asset bloom', () => {
    const branch = asset().lods.full.entities[0]!
    if (branch.kind !== 'branch') throw new Error('fixture branch missing')
    const material = makeTreeMaterialSource(
      { ...asset(), palette: { ...asset().palette, branch: '#808080' } },
      new Set(),
      new Set(),
      new Set(),
      () => ({ width: 800, height: 600 }),
    ).line(branch, 0.1)

    expect(material.color.r).toBeCloseTo(new THREE.Color('#808080').r * 1.8)
  })

  it('reindexes a stable-ID game move/yaw and moves its ground glow contribution', () => {
    const movedAsset = asset({ x: 20, y: 1.7, z: 0 })
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: movedAsset }), parent, factory.build)
    runtime.setTrees([tree('moving', 300, 300)])
    expect(runtime.flushGlow().map(({ key, contributors }) => [key, contributors.length])).toEqual([['2:2', 1]])
    runtime.setTrees([tree('moving', 10, -20, 'a', Math.PI)])

    const glow = runtime.flushGlow()
    expect(glow.map(({ key, contributors }) => [key, contributors.length])).toEqual([
      ['-1:-1', 1],
      ['-1:0', 1],
      ['0:-1', 1],
      ['0:0', 1],
      ['2:2', 0],
    ])
    expect(glow[0]!.contributors[0]).toMatchObject({ id: 'moving', x: 10, z: -20 })
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)

    expect(runtime.updateGame(camera, 100, 720).visited).toBe(1)
    expect(runtime.snapshot()).toMatchObject({ logical: 1, visible: 1, full: 1 })
    runtime.processOperations(12)
    expect(parent.children.map(({ name }) => name)).toEqual(['moving'])
    expect(factory.groups).toHaveLength(1)
  })

  it('surfaces a failed representation without fallback or automatic same-target retries', () => {
    let attempts = 0
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), () => {
      attempts++
      throw new Error('tree-a build failed')
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('tree-a', 0, -20)])

    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({
      resident: 0,
      pending: 0,
      failureCount: 1,
      error: "tree 'tree-a' full representation failed: tree-a build failed",
    })
    runtime.processOperations(12)
    expect(attempts).toBe(1)
  })

  it('retries after entity change and clears that state failure after success', () => {
    let fail = true
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (...args) => {
      if (fail) throw new Error('moving tree failed')
      return factory.build(...args)
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('moving', 0, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe("tree 'moving' full representation failed: moving tree failed")

    fail = false
    runtime.setTrees([tree('moving', 1, -20)])
    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ resident: 1, pending: 0, error: null })
  })

  it('retries after desired-LOD change and clears the recovered state failure', () => {
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (...args) => {
      if (args[2] === 'full') throw new Error('full failed')
      return factory.build(...args)
    })
    runtime.setTrees([tree('lod-retry', 0, -20)])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)
    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe("tree 'lod-retry' full representation failed: full failed")

    runtime.setTrees([tree('lod-retry', 0, -80)])
    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ reduced: 1, resident: 1, error: null })
  })

  it('clears only the recovered or inactive state failure while preserving concurrent failures', () => {
    const failing = new Set(['a', 'b'])
    const factory = objectBuilder()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (...args) => {
      if (failing.has(args[1].id)) throw new Error(`${args[1].id} failed`)
      return factory.build(...args)
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('a', 0, -20), tree('b', 1, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe("tree 'a' full representation failed: a failed")

    failing.delete('a')
    runtime.setTrees([tree('a', 0, -21), tree('b', 1, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe("tree 'b' full representation failed: b failed")

    runtime.setTrees([tree('a', 0, -21)])
    expect(runtime.snapshot().error).toBeNull()
  })

  it('releases active and retired runtime objects exactly once across repeated disposal', () => {
    const factory = objectBuilder()
    const release = vi.fn()
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), factory.build, release)
    runtime.setMode('raw')
    runtime.setTrees([tree('active', 0, -20), tree('retired', 1, -20)])
    runtime.processOperations(12)
    runtime.setTrees([tree('active', 0, -20)])

    runtime.dispose()
    runtime.dispose()

    expect(new Set(release.mock.calls.map(([group]) => group.name))).toEqual(new Set(['active', 'retired']))
    expect(release).toHaveBeenCalledTimes(2)
  })

  it('counts analytic lights from visible Three representation objects', () => {
    const runtime = new GameTreeRuntime(resolve({ a: asset() }), new THREE.Group(), (_asset, tree) => {
      const group = new THREE.Group()
      group.name = tree.id
      group.add(new THREE.PointLight('#ffffff'))
      return group
    })
    runtime.setMode('raw')
    runtime.setTrees([tree('lit', 0, -20)])
    runtime.processOperations(12)

    expect(runtime.snapshot().pointLights).toBe(1)
  })

  it('runs the world resource teardown exactly once across repeated disposal', () => {
    const releases = [vi.fn(), vi.fn(), vi.fn()]
    const lifecycle = new GameWorldLifecycle(releases)

    lifecycle.dispose()
    lifecycle.dispose()

    for (const release of releases) expect(release).toHaveBeenCalledTimes(1)
  })
})
