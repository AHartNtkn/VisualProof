import * as THREE from 'three'
import { describe, expect, it, vi } from 'vitest'
import {
  OrchardWorldLifecycle,
  OrchardTreeRuntime,
  treeWorldSphere,
  type TreeObjectBuilder,
} from '../../orchard/render'
import type { SavedTree, SavedTreeLayout } from '../../orchard/world'

function layout(center = { x: 0, y: 2, z: 0 }, entityCount = 4): SavedTreeLayout {
  const entities = Array.from({ length: entityCount }, (_, index) => ({
    kind: 'branch' as const,
    key: `branch-${index}`,
    polarity: 0 as const,
    pts: [{ x: 0, y: index, z: 0 }, { x: 0, y: index + 1, z: 0 }],
  }))
  return {
    label: 'runtime fixture',
    bounds: { center, radius: 5 },
    lods: {
      full: { center, radius: 5, entities },
      reduced: { center, radius: 5, entities: entities.slice(0, 2) },
      marker: { color: '#ffffff', size: 1 },
    },
    hues: [],
    palette: { branch: '#ffffff', cutBranch: '#777777', baseWire: '#eeeeee' },
    widths: { branch: 0.1, curve: 0.05 },
    glow: { color: '#ffffff', radius: 4, opacity: 0.5, bloom: 0.6 },
  }
}

const saved = (id: string, x: number, z: number, layoutId = 'a', yaw = 0): SavedTree => ({
  id, layout: layoutId, x, z, yaw,
})

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
    build(_layout, tree, index, lod, raw) {
      const group = new THREE.Group()
      const geometry = new THREE.BufferGeometry()
      const mesh = new THREE.Mesh(geometry, new THREE.MeshBasicMaterial())
      group.name = tree.id
      group.userData['treeIndex'] = index
      group.userData['representation'] = raw ? 'raw' : lod
      group.position.set(tree.x, 0, tree.z)
      group.rotation.y = tree.yaw
      group.add(mesh)
      groups.push(group)
      geometries.push(geometry)
      return group
    },
  }
}

describe('orchard tree runtime', () => {
  it('rotates an off-center saved bound before translating its world sphere', () => {
    const sphere = treeWorldSphere(saved('off-center', 10, -4, 'a', Math.PI / 2), layout({ x: 3, y: 7, z: 2 }))

    expect(sphere.center.x).toBeCloseTo(12)
    expect(sphere.center.y).toBe(7)
    expect(sphere.center.z).toBeCloseTo(-7)
    expect(sphere.radius).toBe(5)
  })

  it('diffs stable IDs, updates placement in place, and replaces only a changed layout', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const release = vi.fn((group: THREE.Group) => {
      for (const child of group.children) (child as THREE.Mesh).geometry.dispose()
    })
    const runtime = new OrchardTreeRuntime({ a: layout(), b: layout({ x: 1, y: 2, z: 0 }, 6) }, parent, factory.build, release)
    runtime.setMode('raw')
    runtime.setTrees([saved('stable', 1, 2)])
    expect(runtime.processOperations(12).completed).toBe(1)
    const original = factory.groups[0]!

    runtime.setTrees([saved('stable', -9, 12, 'a', 0.75)])

    expect(runtime.snapshot()).toMatchObject({ logical: 1, logicalEntities: 4, pending: 0, resident: 1 })
    expect(original.position.toArray()).toEqual([-9, 0, 12])
    expect(original.rotation.y).toBe(0.75)
    expect(factory.groups).toHaveLength(1)

    runtime.setTrees([saved('stable', -9, 12, 'b', 0.75)])
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
    const runtime = new OrchardTreeRuntime({ a: layout() }, parent, factory.build, release)
    runtime.setMode('raw')
    runtime.setTrees(Array.from({ length: 6 }, (_, index) => saved(`old-${index}`, index, 0)))
    expect(runtime.processOperations(12).completed).toBe(6)

    runtime.setTrees([])
    runtime.setTrees(Array.from({ length: 12 }, (_, index) => saved(`new-${index}`, index, -20)))
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
    const runtime = new OrchardTreeRuntime({ a: layout() }, parent, factory.build)
    runtime.setMode('raw')
    runtime.setTrees(Array.from({ length: 2_000 }, (_, index) => saved(`canceled-${index}`, index, 0)))
    expect(runtime.snapshot().pending).toBe(2_000)
    runtime.setTrees([])
    expect(runtime.snapshot().pending).toBe(0)
    runtime.setTrees([saved('live', 0, -20)])

    const work = runtime.processOperations(1)

    expect(work).toEqual({ completed: 1, examined: 1 })
    expect(parent.children.map(({ name }) => name)).toEqual(['live'])
    expect(runtime.snapshot()).toMatchObject({ pending: 0, resident: 1 })
  })

  it('hides a selected game representation immediately when Raw needs the same full LOD rebuilt', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: layout() }, parent, factory.build)
    runtime.setTrees([saved('same-lod', 0, -20)])
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

  it('hides and detaches a removed tree immediately, then releases its geometry from the queue', () => {
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: layout() }, parent, factory.build)
    runtime.setMode('raw')
    runtime.setTrees([saved('removed', 0, 0)])
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
    const runtime = new OrchardTreeRuntime({ a: layout() }, parent, factory.build)
    const farTrees = Array.from({ length: 500 }, (_, index) => saved(`far-${index}`, 10_000 + index * 20, 10_000))
    runtime.setTrees([saved('near', 0, -20), ...farTrees])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)

    const updated = runtime.updateGame(camera, 100, 720)

    expect(updated.visited).toBe(1)
    expect(runtime.snapshot()).toMatchObject({ logical: 501, logicalEntities: 2004, visible: 1 })

    runtime.setTrees([saved('near', 0, -20), ...farTrees.slice(0, 199)])
    expect(runtime.snapshot()).toMatchObject({ logical: 200, logicalEntities: 800 })
    expect(runtime.updateGame(camera, 100, 720).visited).toBe(1)
  })

  it('reindexes a stable-ID Game move/yaw and moves its saved-ground glow contribution', () => {
    const movedLayout = layout({ x: 20, y: 1.7, z: 0 })
    const parent = new THREE.Group()
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: movedLayout }, parent, factory.build)
    runtime.setTrees([saved('moving', 300, 300)])
    expect(runtime.flushGlow().map(({ key, contributors }) => [key, contributors.length])).toEqual([['2:2', 1]])
    runtime.setTrees([saved('moving', 10, -20, 'a', Math.PI)])

    const glow = runtime.flushGlow()
    expect(glow.map(({ key, contributors }) => [key, contributors.length])).toEqual([
      ['0:-1', 1],
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
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), () => {
      attempts++
      throw new Error('tree-a build failed')
    })
    runtime.setMode('raw')
    runtime.setTrees([saved('tree-a', 0, -20)])

    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ resident: 0, pending: 0, error: 'tree-a build failed' })
    runtime.processOperations(12)
    expect(attempts).toBe(1)
  })

  it('retries after entity change and clears that state failure after success', () => {
    let fail = true
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), (...args) => {
      if (fail) throw new Error('moving tree failed')
      return factory.build(...args)
    })
    runtime.setMode('raw')
    runtime.setTrees([saved('moving', 0, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe('moving tree failed')

    fail = false
    runtime.setTrees([saved('moving', 1, -20)])
    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ resident: 1, pending: 0, error: null })
  })

  it('retries after desired-LOD change and clears the recovered state failure', () => {
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), (...args) => {
      if (args[3] === 'full') throw new Error('full failed')
      return factory.build(...args)
    })
    runtime.setTrees([saved('lod-retry', 0, -20)])
    const camera = new THREE.PerspectiveCamera(67, 16 / 9, 0.08, 1800)
    camera.position.set(0, 1.7, 0)
    camera.lookAt(0, 1.7, -1)
    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe('full failed')

    runtime.setTrees([saved('lod-retry', 0, -80)])
    runtime.updateGame(camera, 100, 720)
    runtime.processOperations(12)

    expect(runtime.snapshot()).toMatchObject({ reduced: 1, resident: 1, error: null })
  })

  it('clears only the recovered or inactive state failure while preserving concurrent failures', () => {
    const failing = new Set(['a', 'b'])
    const factory = objectBuilder()
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), (...args) => {
      if (failing.has(args[1].id)) throw new Error(`${args[1].id} failed`)
      return factory.build(...args)
    })
    runtime.setMode('raw')
    runtime.setTrees([saved('a', 0, -20), saved('b', 1, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe('a failed')

    failing.delete('a')
    runtime.setTrees([saved('a', 0, -21), saved('b', 1, -20)])
    runtime.processOperations(12)
    expect(runtime.snapshot().error).toBe('b failed')

    runtime.setTrees([saved('a', 0, -21)])
    expect(runtime.snapshot().error).toBeNull()
  })

  it('releases active and retired runtime objects exactly once across repeated disposal', () => {
    const factory = objectBuilder()
    const release = vi.fn()
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), factory.build, release)
    runtime.setMode('raw')
    runtime.setTrees([saved('active', 0, -20), saved('retired', 1, -20)])
    runtime.processOperations(12)
    runtime.setTrees([saved('active', 0, -20)])

    runtime.dispose()
    runtime.dispose()

    expect(new Set(release.mock.calls.map(([group]) => group.name))).toEqual(new Set(['active', 'retired']))
    expect(release).toHaveBeenCalledTimes(2)
  })

  it('counts analytic lights from selected Three representation objects', () => {
    const runtime = new OrchardTreeRuntime({ a: layout() }, new THREE.Group(), (_layout, tree) => {
      const group = new THREE.Group()
      group.name = tree.id
      group.add(new THREE.PointLight('#ffffff'))
      return group
    })
    runtime.setMode('raw')
    runtime.setTrees([saved('lit', 0, -20)])
    runtime.processOperations(12)

    expect(runtime.snapshot().pointLights).toBe(1)
  })

  it('runs the world resource teardown exactly once across repeated disposal', () => {
    const releases = [vi.fn(), vi.fn(), vi.fn()]
    const lifecycle = new OrchardWorldLifecycle(releases)

    lifecycle.dispose()
    lifecycle.dispose()

    for (const release of releases) expect(release).toHaveBeenCalledTimes(1)
  })
})
