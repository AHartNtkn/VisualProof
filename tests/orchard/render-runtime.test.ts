import * as THREE from 'three'
import { describe, expect, it, vi } from 'vitest'
import {
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
    expect(runtime.processOperations(12)).toBe(1)
    const original = factory.groups[0]!

    runtime.setTrees([saved('stable', -9, 12, 'a', 0.75)])

    expect(runtime.snapshot()).toMatchObject({ logical: 1, logicalEntities: 4, pending: 0, resident: 1 })
    expect(original.position.toArray()).toEqual([-9, 0, 12])
    expect(original.rotation.y).toBe(0.75)
    expect(factory.groups).toHaveLength(1)

    runtime.setTrees([saved('stable', -9, 12, 'b', 0.75)])
    expect(original.visible).toBe(false)
    expect(original.parent).toBeNull()
    expect(runtime.processOperations(12)).toBe(1)

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
    expect(runtime.processOperations(12)).toBe(6)

    runtime.setTrees([])
    runtime.setTrees(Array.from({ length: 12 }, (_, index) => saved(`new-${index}`, index, -20)))
    const buildsBefore = factory.groups.length
    const releasesBefore = release.mock.calls.length

    expect(runtime.processOperations(12)).toBe(12)
    expect(factory.groups.length - buildsBefore).toBe(6)
    expect(release.mock.calls.length - releasesBefore).toBe(6)
    expect(runtime.snapshot()).toMatchObject({ logical: 12, resident: 6, pending: 6 })
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

    expect(runtime.processOperations(12)).toBe(1)
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
})
