import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson } from '../../../src/kernel/diagram/json'
import { DARK } from '../../../src/view/paint'
import { TreeRenderAssetCache } from '../../../src/game/render/assets'
import {
  DynamicTreeObjects,
  TREE_TWEEN_MS,
  type TreeRenderSnapshot,
} from '../../../src/game/render/dynamic-tree'
import type { RenderTree } from '../../../src/game/render/runtime'
import {
  makeBatchedTreeObject,
  makeDynamicTreeObject,
  pointAtVisibleParts,
  type TreeMaterialSource,
} from '../../../src/game/render/tree-objects'

const interactionReach = 100

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

describe('visible tree-part pointing', () => {
  it('points only the orbit target when full-detail trees overlap', () => {
    const diagram = new DiagramBuilder().build()
    const asset = new TreeRenderAssetCache(DARK).get(JSON.stringify(diagramToJson(diagram)), diagram)
    const background = makeBatchedTreeObject(asset, 'full', {
      id: 'background', index: 0, x: 0, z: -20, yaw: 0,
    }, materials())
    const orbit = makeBatchedTreeObject(asset, 'full', {
      id: 'orbit', index: 1, x: 0, z: -20, yaw: 0,
    }, materials())
    const branch = asset.lods.full.entities[0]!
    if (!('pts' in branch)) throw new Error('expected production branch')
    background.updateMatrixWorld(true)
    orbit.updateMatrixWorld(true)
    const ray = new THREE.Raycaster(
      new THREE.Vector3(branch.pts[0]!.x, branch.pts[0]!.y, 0),
      new THREE.Vector3(0, 0, -1),
      0,
      interactionReach,
    )

    expect(pointAtVisibleParts(ray, [background, orbit], interactionReach, 'orbit')).toMatchObject({
      treeId: 'orbit', entityKey: `b:${diagram.root}`,
    })
  })

  it('identifies a later branch in a batched full-detail tree by pointing at its geometry', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    builder.cut(outer)
    const diagram = builder.build()
    const asset = new TreeRenderAssetCache(DARK).get(JSON.stringify(diagramToJson(diagram)), diagram)
    const tree = makeBatchedTreeObject(asset, 'full', {
      id: 'tree-a', index: 0, x: 0, z: -20, yaw: 0,
    }, materials())
    tree.updateMatrixWorld(true)
    const ray = new THREE.Raycaster(
      new THREE.Vector3(0, 2.2, 0),
      new THREE.Vector3(0, 0, -1),
      0,
      interactionReach,
    )

    expect(pointAtVisibleParts(ray, [tree], interactionReach, null)).toMatchObject({
      treeId: 'tree-a', entityKey: 'b:r2',
    })
  })

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
    parent.updateMatrixWorld(true)
    const pointAtX = (x: number, orbitTarget: string | null = null) => pointAtVisibleParts(
      new THREE.Raycaster(
        new THREE.Vector3(x, 0.5, 0),
        new THREE.Vector3(0, 0, -1),
        0,
        interactionReach,
      ),
      dynamic.objects(),
      interactionReach,
      orbitTarget,
    )

    expect(pointAtX(5, 'a')).toMatchObject({ treeId: 'a', entityKey: 'b:a' })
    expect(pointAtX(35, 'b')).toMatchObject({
      treeId: 'b', entityKey: 'b:b',
    })

    dynamic.begin(renderTree('a'), branchScene('b:a', 10), branchScene('b:a', 20), 175)
    dynamic.update(175)
    parent.updateMatrixWorld(true)
    expect(pointAtX(5, 'a')).toMatchObject({ treeId: 'a', entityKey: 'b:a' })

    dynamic.update(TREE_TWEEN_MS)
    expect(dynamic.objects('b')).toEqual([])
    expect(dynamic.objects('a')).toHaveLength(1)

    dynamic.update(525)
    expect(dynamic.objects()).toEqual([])
  })
})
