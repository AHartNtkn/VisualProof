import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson } from '../../../src/kernel/diagram/json'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { TreeRenderAssetCache } from '../../../src/game/render/assets'
import {
  makeBatchedTreeObject,
  makeDynamicTreeObject,
  makeMarkerObject,
  makeRawTreeObject,
  pointAtTreeAssets,
  type TreeMaterialSource,
} from '../../../src/game/render/tree-objects'
import type { TreePlacement } from '../../../src/game/render/placement'
import type { TreeRenderAsset } from '../../../src/game/render/types'
import { DARK } from '../../../src/view/paint'

const asset: TreeRenderAsset = {
  bounds: { center: { x: 0, y: 2, z: 0 }, radius: 4 },
  lods: {
    full: {
      center: { x: 0, y: 2, z: 0 },
      radius: 4,
      entities: [
        {
          kind: 'branch', key: 'b:root', region: 'root', polarity: 0,
          pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 2, z: 0 }],
        },
        {
          kind: 'ring', key: 'r:n', node: 'n', headWire: null,
          pts: [{ x: 1, y: 2, z: 0 }, { x: 1, y: 2, z: 1 }, { x: 1, y: 2, z: 0 }],
        },
        { kind: 'pip', key: 'p:n', node: 'n', ownerWire: null, pos: { x: 0, y: 1, z: 0 } },
        { kind: 'label', key: 'l:n', node: 'n', text: 'N', pos: { x: 2, y: 3, z: 0 } },
      ],
    },
    reduced: {
      center: { x: 0, y: 2, z: 0 },
      radius: 4,
      entities: [{
        kind: 'branch', key: 'b:reduced', region: 'reduced', polarity: 0,
        pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 3, z: 0 }],
      }],
    },
    marker: { color: '#123456', size: 1.25 },
  },
  hues: [],
  palette: { branch: '#ffffff', cutBranch: '#777777', baseWire: '#eeeeee' },
  widths: { branch: 0.1, curve: 0.05 },
  glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
}

const placement: TreePlacement = { id: 'tree-a', index: 0, x: 10, z: 20, yaw: 0.5 }

function materials(): TreeMaterialSource {
  return {
    line: (_entity, width) => new LineMaterial({
      color: '#ffffff', linewidth: width, worldUnits: true,
    }),
    sprite: () => {
      const material = new THREE.SpriteMaterial({ color: '#ffffff' })
      material.userData['aspect'] = 2
      return material
    },
    marker: (marker) => new THREE.SpriteMaterial({ color: marker.color }),
  }
}

function visualMaterials(group: THREE.Object3D): THREE.Material[] {
  const rendered: THREE.Material[] = []
  group.traverse((object) => {
    if (!('material' in object)) return
    const material = (object as THREE.Mesh).material
    if (Array.isArray(material)) rendered.push(...material)
    else rendered.push(material)
  })
  return rendered
}

function representativeAsset(): TreeRenderAsset {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const outer = builder.atom(builder.root, relSig([IOTA]))
  const inner = builder.atom(cut, relSig([IOTA]))
  const reference = builder.ref(cut, 'Def', relSig([IOTA]))
  builder.wire([
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
    { node: reference, port: { kind: 'arg', index: 0 } },
  ])
  const diagram = builder.build()
  return new TreeRenderAssetCache(DARK).get(JSON.stringify(diagramToJson(diagram)), diagram)
}

function kindColoredMaterials(): TreeMaterialSource {
  const colors = {
    branch: '#ff0000',
    ring: '#00ff00',
    strand: '#0000ff',
    pip: '#ff00ff',
    label: '#00ffff',
  } as const
  return {
    line: (entity, width) => {
      const material = new LineMaterial({ color: colors[entity.kind], linewidth: width, worldUnits: true })
      material.resolution.set(800, 600)
      return material
    },
    sprite: (entity) => new THREE.SpriteMaterial({ color: colors[entity.kind] }),
    marker: (marker) => new THREE.SpriteMaterial({ color: marker.color }),
  }
}

function visibleColors(group: THREE.Object3D): Set<string> {
  return new Set(visualMaterials(group).flatMap((material) => (
    'color' in material && material.color instanceof THREE.Color
      ? [material.color.getHexString()]
      : []
  )))
}

describe('game tree representations', () => {
  it('points a typed branch whose drawing key does not encode its semantic region', () => {
    const semanticBranch = {
      kind: 'branch' as const,
      key: 'drawing-only-key',
      region: 'semantic-region',
      polarity: 0 as const,
      pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 2, z: 0 }],
    }
    const semanticAsset: TreeRenderAsset = {
      ...asset,
      bounds: { center: { x: 0, y: 1, z: 0 }, radius: 2 },
      lods: {
        ...asset.lods,
        full: { center: { x: 0, y: 1, z: 0 }, radius: 2, entities: [semanticBranch] },
      },
    }

    const pointed = pointAtTreeAssets(
      new THREE.Ray(new THREE.Vector3(0, 1, 5), new THREE.Vector3(0, 0, -1)),
      [{
        treeId: 'semantic-tree',
        placement: { id: 'semantic-tree', index: 0, x: 0, z: 0, yaw: 0 },
        asset: semanticAsset,
      }],
      100,
      null,
      (entity) => entity.kind === 'branch',
    )

    expect(pointed).toMatchObject({
      treeId: 'semantic-tree',
      entity: { key: 'drawing-only-key', region: 'semantic-region' },
    })
  })

  it('renders tween entities at their requested visible opacity', () => {
    const group = makeDynamicTreeObject({
      ...asset.lods.full,
      entities: [
        { ...asset.lods.full.entities[0]!, alpha: 0.25 },
        { ...asset.lods.full.entities[3]!, alpha: 0.5 },
      ],
    }, placement, materials())

    expect(visualMaterials(group).map(({ opacity }) => opacity)).toEqual([0.25, 0.5])
  })

  it('produces visible raw, full, reduced, and marker representations without analytic lights', () => {
    const representations = [
      makeRawTreeObject(asset, placement, materials()),
      makeBatchedTreeObject(asset, 'full', placement, materials()),
      makeBatchedTreeObject(asset, 'reduced', placement, materials()),
      makeMarkerObject(asset, placement, materials()),
    ]

    for (const group of representations) {
      expect(visualMaterials(group).length).toBeGreaterThan(0)
      expect(group.getObjectsByProperty('isPointLight', true)).toEqual([])
    }
  })

  it('renders every representative full-detail entity kind from a real kernel diagram', () => {
    const derived = representativeAsset()
    const representativePlacement: TreePlacement = {
      id: 'representative', index: 0, x: 0, z: -20, yaw: 0,
    }
    const raw = makeRawTreeObject(derived, representativePlacement, kindColoredMaterials())
    const full = makeBatchedTreeObject(derived, 'full', representativePlacement, kindColoredMaterials())
    const expected = new Set(['ff0000', '00ff00', '0000ff', 'ff00ff', '00ffff'])

    expect(visibleColors(raw)).toEqual(expected)
    expect(visibleColors(full)).toEqual(expected)
  })

  it('renders meaningful reduced branches from a real kernel diagram', () => {
    const derived = representativeAsset()
    const representativePlacement: TreePlacement = {
      id: 'representative', index: 0, x: 0, z: -20, yaw: 0,
    }
    const reduced = makeBatchedTreeObject(
      derived,
      'reduced',
      representativePlacement,
      kindColoredMaterials(),
    )
    reduced.updateMatrixWorld(true)
    expect(visibleColors(reduced)).toEqual(new Set(['ff0000']))
  })

  it('places every representation at the tree world transform', () => {
    const representations = [
      makeRawTreeObject(asset, placement, materials()),
      makeBatchedTreeObject(asset, 'full', placement, materials()),
      makeBatchedTreeObject(asset, 'reduced', placement, materials()),
      makeMarkerObject(asset, placement, materials()),
    ]

    for (const group of representations) {
      expect(group.position.toArray()).toEqual([10, 0, 20])
      expect(group.rotation.y).toBe(0.5)
    }
  })

  it('renders the marker with its derived color and apparent size', () => {
    const group = makeMarkerObject(asset, placement, materials())
    const marker = group.children[0] as THREE.Sprite

    expect(marker.scale.toArray()).toEqual([1.25, 1.25, 1])
    expect(marker.material.color.getHexString()).toBe('123456')
  })
})
