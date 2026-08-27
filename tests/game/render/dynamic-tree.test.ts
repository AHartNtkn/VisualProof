import * as THREE from 'three'
import { LineSegments2 } from 'three/examples/jsm/lines/LineSegments2.js'
import { describe, expect, it, vi } from 'vitest'
import {
  DynamicTreeObjects,
  TREE_TWEEN_MS,
  TreeTweenTracks,
  type TreeRenderSnapshot,
} from '../../../src/game/render/dynamic-tree'
import type { RenderTree } from '../../../src/game/render/runtime'
import { pointAtVisibleParts } from '../../../src/game/render/tree-objects'

const interactionReach = 100

function branchScene(key: string, x: number): TreeRenderSnapshot {
  return {
    center: { x, y: 0, z: 0 },
    radius: 1,
    entities: [{
      kind: 'branch', key, polarity: 0,
      pts: [{ x, y: 0, z: 0 }, { x, y: 1, z: 0 }],
    }],
  }
}

function renderTree(id: string, diagramJson: string): RenderTree {
  return {
    id,
    diagramJson,
    placement: { id, index: id === 'a' ? 0 : 1, x: 0, z: -20, yaw: 0 },
  }
}

function pointedObject(treeId: string, entityKey: string): THREE.Object3D {
  const object = new THREE.Object3D()
  object.userData['treeId'] = treeId
  object.userData['entityKey'] = entityKey
  return object
}

function rootFor(treeId: string, child: THREE.Object3D): THREE.Group {
  const root = new THREE.Group()
  root.userData['treeId'] = treeId
  root.add(child)
  return root
}

describe('ordinary visible tree-part picking', () => {
  it('filters orbit raycasts to the exact orbit target before intersecting background trees', () => {
    const foreground = rootFor('foreground', pointedObject('foreground', 'b:r0'))
    const orbit = rootFor('orbit', pointedObject('orbit', 'b:r0'))
    const intersectObjects = vi.fn((objects: THREE.Object3D[]) => objects.map((root, index) => ({
      distance: index + 1,
      point: new THREE.Vector3(),
      object: root.children[0]!,
    })))

    const pointedPart = pointAtVisibleParts(
      { intersectObjects } as unknown as THREE.Raycaster,
      [foreground, orbit],
      interactionReach,
      'orbit',
    )

    expect(intersectObjects).toHaveBeenCalledWith([orbit], true)
    expect(pointedPart?.treeId).toBe('orbit')
  })

  it('accepts ordinary non-branch parts for orbit entry and enforces the strict reach boundary', () => {
    const ring = pointedObject('tree-a', 'r:n0')
    const root = rootFor('tree-a', ring)
    const rayAt = (distance: number): THREE.Raycaster => ({
      intersectObjects: () => [{ distance, point: new THREE.Vector3(), object: ring }],
    }) as unknown as THREE.Raycaster

    expect(pointAtVisibleParts(rayAt(interactionReach), [root], interactionReach, null))
      .toEqual({ treeId: 'tree-a', entityKey: 'r:n0', distance: interactionReach })
    expect(pointAtVisibleParts(rayAt(interactionReach + 0.001), [root], interactionReach, null))
      .toBeNull()
  })

  it('maps a batched line segment index through its retained entity ranges', () => {
    const line = new LineSegments2()
    line.userData['treeId'] = 'tree-a'
    line.userData['entityRanges'] = [
      { entityKey: 'b:root', startSegment: 0, endSegment: 2 },
      { entityKey: 'b:side', startSegment: 2, endSegment: 3 },
    ]
    const root = rootFor('tree-a', line)
    const ray = {
      intersectObjects: () => [{
        distance: 7,
        point: new THREE.Vector3(),
        object: line,
        faceIndex: 2,
      }],
    } as unknown as THREE.Raycaster

    expect(pointAtVisibleParts(ray, [root], interactionReach, null)).toEqual({
      treeId: 'tree-a', entityKey: 'b:side', distance: 7,
    })
  })
})

describe('per-tree dynamic tween tracks', () => {
  it('animates different trees concurrently and replans one tree from its displayed frame', () => {
    const beforeA = branchScene('b:a', 0)
    const afterA = branchScene('b:a', 10)
    const secondA = branchScene('b:a', 20)
    const beforeB = branchScene('b:b', 30)
    const afterB = branchScene('b:b', 40)
    const tracks = new TreeTweenTracks()
    tracks.begin('a', beforeA, afterA, 0)
    tracks.begin('b', beforeB, afterB, 100)

    expect(new Set(tracks.at(175).keys())).toEqual(new Set(['a', 'b']))
    const displayed = tracks.at(175).get('a')!
    tracks.begin('a', afterA, secondA, 175)

    expect(tracks.at(175).get('a')).toEqual(displayed)
    expect(tracks.at(175).get('b')).toEqual(
      new TreeTweenTracks().begin('b', beforeB, afterB, 100).at(175).get('b'),
    )
  })

  it('completes and resumes only the trees whose independent tracks elapsed', () => {
    const parent = new THREE.Group()
    const runtime = {
      suspend: vi.fn(),
      resume: vi.fn(),
    }
    const released: THREE.Group[] = []
    const dynamic = new DynamicTreeObjects(
      parent,
      runtime,
      (snapshot, tree) => {
        const group = new THREE.Group()
        group.name = tree.id
        group.userData['frameX'] = snapshot.center.x
        return group
      },
      (group) => { released.push(group) },
    )
    const treeA = renderTree('a', 'after-a')
    const treeB = renderTree('b', 'after-b')
    dynamic.begin(treeA, branchScene('b:a', 0), branchScene('b:a', 10), 0)
    dynamic.begin(treeB, branchScene('b:b', 20), branchScene('b:b', 30), 100)

    dynamic.update(TREE_TWEEN_MS)

    expect(runtime.suspend.mock.calls).toEqual([['a'], ['b']])
    expect(runtime.resume.mock.calls).toEqual([[treeA]])
    expect(dynamic.objects().map(({ name }) => name)).toEqual(['b'])
    expect(released.some(({ name }) => name === 'a')).toBe(true)

    dynamic.update(TREE_TWEEN_MS + 100)

    expect(runtime.resume.mock.calls).toEqual([[treeA], [treeB]])
    expect(dynamic.objects()).toEqual([])
  })

  it('cancels and disposes every active dynamic role without resuming stale targets', () => {
    const parent = new THREE.Group()
    const runtime = { suspend: vi.fn(), resume: vi.fn() }
    const released: THREE.Group[] = []
    const dynamic = new DynamicTreeObjects(
      parent,
      runtime,
      (_snapshot, tree) => {
        const group = new THREE.Group()
        group.name = tree.id
        return group
      },
      (group) => { released.push(group) },
    )
    dynamic.begin(renderTree('a', 'after-a'), branchScene('b:a', 0), branchScene('b:a', 10), 0)
    dynamic.begin(renderTree('b', 'after-b'), branchScene('b:b', 20), branchScene('b:b', 30), 100)

    dynamic.clear()
    dynamic.update(TREE_TWEEN_MS + 100)

    expect(released.map(({ name }) => name)).toEqual(['a', 'b'])
    expect(parent.children).toEqual([])
    expect(dynamic.objects()).toEqual([])
    expect(runtime.resume).not.toHaveBeenCalled()
  })
})
