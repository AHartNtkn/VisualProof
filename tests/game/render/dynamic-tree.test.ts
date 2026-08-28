import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it } from 'vitest'
import {
  DynamicTreeObjects,
  TREE_TWEEN_MS,
  type TreeRenderSnapshot,
} from '../../../src/game/render/dynamic-tree'
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
      kind: 'branch', key, polarity: 0,
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

describe('dynamic trees', () => {
  it('keeps concurrent tweens visible at independent progress and completion times', () => {
    const parent = new THREE.Group()
    const dynamic = new DynamicTreeObjects(
      parent,
      { suspend() {}, resume() {} },
      (snapshot, tree) => makeDynamicTreeObject(snapshot, tree.placement, materials()),
    )
    dynamic.begin(renderTree('a'), branchScene('b:a', 0), branchScene('b:a', 10), 0)
    dynamic.begin(renderTree('b'), branchScene('b:b', 30), branchScene('b:b', 40), 0)

    dynamic.update(175)
    expect(dynamic.objects('a')).toHaveLength(1)
    expect(dynamic.objects('b')).toHaveLength(1)

    dynamic.begin(renderTree('a'), branchScene('b:a', 10), branchScene('b:a', 20), 175)
    dynamic.update(175)
    expect(dynamic.objects('a')).toHaveLength(1)

    dynamic.update(TREE_TWEEN_MS)
    expect(dynamic.objects('b')).toEqual([])
    expect(dynamic.objects('a')).toHaveLength(1)

    dynamic.update(525)
    expect(dynamic.objects()).toEqual([])
  })
})
