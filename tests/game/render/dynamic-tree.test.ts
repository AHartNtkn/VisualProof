import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it } from 'vitest'
import {
  DynamicTreeObjects,
  type TreeRenderSnapshot,
} from '../../../src/game/render/dynamic-tree'
import { SCENE_TWEEN_MS } from '../../../src/view3d/transition'
import type { RenderTree } from '../../../src/game/render/runtime'
import {
  makeDynamicTreeObject,
  type TreeMaterialSource,
} from '../../../src/game/render/tree-objects'

function materials(): TreeMaterialSource {
  return {
    line: () => {
      const material = new LineMaterial({ color: '#ffffff', linewidth: 0.1, worldUnits: true })
      material.resolution.set(800, 600)
      return material
    },
    sprite: () => new THREE.SpriteMaterial(),
    marker: () => new THREE.SpriteMaterial(),
  }
}

function branchScene(key: string, x: number): TreeRenderSnapshot {
  return {
    center: { x, y: 0, z: 0 },
    radius: 1,
    entities: [{
      kind: 'branch', key, region: key.slice(2), polarity: 0,
      pts: [{ x, y: 0, z: 0 }, { x, y: 1, z: 0 }],
    }],
  }
}

function renderTree(id: string): RenderTree {
  return {
    id,
    diagramJson: id,
    placement: { id, index: id === 'a' ? 0 : 1, x: 0, z: -20, yaw: 0 },
  }
}

function branchX(snapshot: TreeRenderSnapshot): number {
  const branch = snapshot.entities[0]
  if (branch?.kind !== 'branch') throw new Error('expected branch snapshot')
  return branch.pts[0]!.x
}

function publish(
  dynamic: DynamicTreeObjects,
  tree: RenderTree,
  before: TreeRenderSnapshot,
  after: TreeRenderSnapshot,
  now: number,
): void {
  dynamic.commit(dynamic.prepare(tree, before, after, now))
}

describe('dynamic trees', () => {
  it('restarts an interrupted tween from its currently displayed geometry', () => {
    const displayed: TreeRenderSnapshot[] = []
    const dynamic = new DynamicTreeObjects(
      new THREE.Group(),
      { suspend() {}, resume() {} },
      (snapshot) => {
        displayed.push(snapshot)
        return new THREE.Group()
      },
    )
    const tree = renderTree('a')

    publish(dynamic, tree, branchScene('b:a', 0), branchScene('b:a', 10), 0)
    dynamic.update(SCENE_TWEEN_MS / 2)
    const beforeInterrupt = displayed.at(-1)!
    expect(branchX(beforeInterrupt)).toBeCloseTo(5)

    // The caller's `before` is the first target (x=10), not the halfway
    // frame currently on screen. Restarting from it would visibly pop.
    publish(
      dynamic,
      tree,
      branchScene('b:a', 10),
      branchScene('b:a', 20),
      SCENE_TWEEN_MS / 2,
    )
    const afterInterrupt = displayed.at(-1)!

    expect(afterInterrupt).toEqual(beforeInterrupt)
    expect(branchX(afterInterrupt)).toBeCloseTo(5)
  })

  it('keeps concurrent tweens visible at independent progress and completion times', () => {
    const parent = new THREE.Group()
    const dynamic = new DynamicTreeObjects(
      parent,
      { suspend() {}, resume() {} },
      (snapshot, tree) => makeDynamicTreeObject(snapshot, tree.placement, materials()),
    )
    publish(dynamic, renderTree('a'), branchScene('b:a', 0), branchScene('b:a', 10), 0)
    publish(dynamic, renderTree('b'), branchScene('b:b', 30), branchScene('b:b', 40), 0)

    dynamic.update(175)
    expect(dynamic.objects('a')).toHaveLength(1)
    expect(dynamic.objects('b')).toHaveLength(1)

    publish(dynamic, renderTree('a'), branchScene('b:a', 10), branchScene('b:a', 20), 175)
    dynamic.update(175)
    expect(dynamic.objects('a')).toHaveLength(1)

    dynamic.update(SCENE_TWEEN_MS)
    expect(dynamic.objects('b')).toEqual([])
    expect(dynamic.objects('a')).toHaveLength(1)

    dynamic.update(525)
    expect(dynamic.objects()).toEqual([])
  })
})
