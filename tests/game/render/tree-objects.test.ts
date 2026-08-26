import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { LineSegments2 } from 'three/examples/jsm/lines/LineSegments2.js'
import { describe, expect, it, vi } from 'vitest'
import {
  disposeTreeObject,
  makeBatchedTreeObject,
  makeMarkerObject,
  makeRawTreeObject,
  type TreeMaterialSource,
} from '../../../src/game/render/tree-objects'
import type { TreePlacement } from '../../../src/game/render/placement'
import type { TreeRenderAsset } from '../../../src/game/render/types'
import type { Entity } from '../../../src/view3d/scene'

const asset: TreeRenderAsset = {
  bounds: { center: { x: 0, y: 2, z: 0 }, radius: 4 },
  lods: {
    full: {
      center: { x: 0, y: 2, z: 0 },
      radius: 4,
      entities: [
        {
          kind: 'branch', key: 'b:root', polarity: 0,
          pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 1, z: 0 }, { x: 1, y: 2, z: 0 }],
        },
        {
          kind: 'branch', key: 'b:side', polarity: 0,
          pts: [{ x: 1, y: 2, z: 0 }, { x: 2, y: 3, z: 0 }],
        },
        {
          kind: 'branch', key: 'b:cut', polarity: 1,
          pts: [{ x: 0, y: 1, z: 0 }, { x: -1, y: 2, z: 0 }],
        },
        {
          kind: 'ring', key: 'r:n', node: 'n', headWire: 'w',
          pts: [{ x: 2, y: 2, z: 0 }, { x: 2, y: 2, z: 1 }, { x: 2, y: 2, z: 0 }],
        },
        {
          kind: 'strand', key: 's:w:0', wire: 'w',
          pts: [{ x: 0, y: 1, z: 0 }, { x: 1, y: 1, z: 1 }, { x: 2, y: 1, z: 1 }],
        },
        {
          kind: 'strand', key: 's:w:1', wire: 'w',
          pts: [{ x: 2, y: 1, z: 1 }, { x: 3, y: 1, z: 0 }],
        },
        { kind: 'pip', key: 'p:n', node: 'n', ownerWire: 'w', pos: { x: 0, y: 1, z: 0 } },
        { kind: 'label', key: 'l:n', node: 'n', text: 'N', pos: { x: 2, y: 3, z: 0 } },
      ],
    },
    reduced: {
      center: { x: 0, y: 2, z: 0 },
      radius: 4,
      entities: [
        {
          kind: 'branch', key: 'b:reduced-even', polarity: 0,
          pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 2, z: 0 }],
        },
        {
          kind: 'branch', key: 'b:reduced-odd', polarity: 1,
          pts: [{ x: 0, y: 2, z: 0 }, { x: 1, y: 3, z: 0 }],
        },
      ],
    },
    marker: { color: '#123456', size: 1.25 },
  },
  hues: [['w', '#00aaff']],
  palette: { branch: '#ffffff', cutBranch: '#777777', baseWire: '#eeeeee' },
  widths: { branch: 0.10, curve: 0.05 },
  glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
}

const placement: TreePlacement = { id: 'tree-a', index: 0, x: 10, z: 20, yaw: 0.5 }

function fixtureMaterials(): {
  source: TreeMaterialSource
  materials: Set<THREE.Material>
  textures: Set<THREE.Texture>
} {
  const materials = new Set<THREE.Material>()
  const textures = new Set<THREE.Texture>()
  const lines = new Map<string, LineMaterial>()
  const sprites = new Map<string, THREE.SpriteMaterial>()
  const lineColor = (entity: Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>): string => {
    if (entity.kind === 'branch') return entity.polarity === 0 ? '#ffffff' : '#777777'
    return entity.kind === 'strand' ? '#00aaff' : '#aa00ff'
  }
  return {
    materials,
    textures,
    source: {
      line(entity, width) {
        const color = lineColor(entity)
        const key = `${entity.kind}:${color}:${width}`
        let material = lines.get(key)
        if (material === undefined) {
          material = new LineMaterial({ color, linewidth: width, worldUnits: true })
          lines.set(key, material)
          materials.add(material)
        }
        return material
      },
      sprite(entity) {
        const key = entity.kind === 'label' ? `label:${entity.text}` : 'pip'
        let material = sprites.get(key)
        if (material === undefined) {
          const texture = new THREE.Texture()
          textures.add(texture)
          material = new THREE.SpriteMaterial({ map: texture, color: '#ffffff' })
          if (entity.kind === 'label') material.userData['aspect'] = 2
          sprites.set(key, material)
          materials.add(material)
        }
        return material
      },
      marker(marker) {
        let material = sprites.get(`marker:${marker.color}`)
        if (material === undefined) {
          const texture = new THREE.Texture()
          textures.add(texture)
          material = new THREE.SpriteMaterial({
            map: texture,
            color: marker.color,
            transparent: true,
            blending: THREE.AdditiveBlending,
            depthWrite: false,
          })
          sprites.set(`marker:${marker.color}`, material)
          materials.add(material)
        }
        return material
      },
    },
  }
}

function segmentsOf(line: LineSegments2): number[][] {
  const starts = line.geometry.getAttribute('instanceStart')
  const ends = line.geometry.getAttribute('instanceEnd')
  return Array.from({ length: starts.count }, (_, index) => [
    starts.getX(index), starts.getY(index), starts.getZ(index),
    ends.getX(index), ends.getY(index), ends.getZ(index),
  ])
}

describe('game tree representations', () => {
  it('uses exact derived world-unit widths for raw full-detail entities', () => {
    const group = makeRawTreeObject(asset, placement, fixtureMaterials().source)
    const lines = group.children.filter((child): child is Line2 => child instanceof Line2)

    expect(lines).toHaveLength(6)
    expect(lines.every((line) => line.material.worldUnits)).toBe(true)
    expect(lines.find((line) => line.userData['entityKind'] === 'branch')!.material.linewidth).toBe(0.10)
    expect(lines.find((line) => line.userData['entityKind'] === 'ring')!.material.linewidth).toBe(0.05)
    expect(lines.find((line) => line.userData['entityKind'] === 'strand')!.material.linewidth).toBe(0.05)
    expect(group.children.some((child) => child instanceof THREE.PointLight)).toBe(false)
  })

  it('keeps raw full geometry and sprites unique for every derived entity and tree', () => {
    const source = fixtureMaterials().source
    const a = makeRawTreeObject(asset, placement, source)
    const b = makeRawTreeObject(
      asset,
      { id: 'tree-b', index: 1, x: -10, z: -20, yaw: 1 },
      source,
    )

    expect(a.children).toHaveLength(8)
    expect(b.children).toHaveLength(8)
    expect(a.position.toArray()).toEqual([10, 0, 20])
    expect(a.rotation.y).toBe(0.5)
    expect(a.children.map((child) => child.userData['entityKey'])).toEqual([
      'b:root', 'b:side', 'b:cut', 'r:n', 's:w:0', 's:w:1', 'p:n', 'l:n',
    ])

    for (let index = 0; index < a.children.length; index++) {
      const first = a.children[index]!, second = b.children[index]!
      expect(first).not.toBe(second)
      expect((first as THREE.InstancedMesh).isInstancedMesh).not.toBe(true)
      expect(first.userData['treeId']).toBe('tree-a')
      expect(second.userData['treeId']).toBe('tree-b')
      if (first instanceof Line2 && second instanceof Line2) {
        expect(first.geometry).not.toBe(second.geometry)
      }
    }
  })

  it('preserves every full polyline segment exactly once with hand-derived entity ranges', () => {
    const group = makeBatchedTreeObject(asset, 'full', placement, fixtureMaterials().source)
    const lines = group.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)
    const actualSegments = lines.flatMap(segmentsOf).map((segment) => segment.join(','))

    expect(actualSegments.sort()).toEqual([
      '0,0,0,0,1,0',
      '0,1,0,1,2,0',
      '1,2,0,2,3,0',
      '0,1,0,-1,2,0',
      '2,2,0,2,2,1',
      '2,2,1,2,2,0',
      '0,1,0,1,1,1',
      '1,1,1,2,1,1',
      '2,1,1,3,1,0',
    ].sort())
    expect(lines).toHaveLength(4)
    expect(lines.every((line) => line.userData['treeId'] === 'tree-a')).toBe(true)
    expect(lines.every((line) => line.material.worldUnits)).toBe(true)
    expect(group.children
      .filter((child): child is THREE.Sprite => child instanceof THREE.Sprite)
      .map((sprite) => sprite.userData['entityKey']))
      .toEqual(['p:n', 'l:n'])
    expect(lines.find((line) => line.userData['entityKeys'].includes('b:root'))!.userData['entityRanges']).toEqual([
      { entityKey: 'b:root', startSegment: 0, endSegment: 2 },
      { entityKey: 'b:side', startSegment: 2, endSegment: 3 },
    ])
    expect(lines.find((line) => line.userData['entityKeys'].includes('b:cut'))!.userData['entityRanges']).toEqual([
      { entityKey: 'b:cut', startSegment: 0, endSegment: 1 },
    ])
    expect(lines.find((line) => line.userData['entityKeys'].includes('r:n'))!.userData['entityRanges']).toEqual([
      { entityKey: 'r:n', startSegment: 0, endSegment: 2 },
    ])
    expect(lines.find((line) => line.userData['entityKeys'].includes('s:w:0'))!.userData['entityRanges']).toEqual([
      { entityKey: 's:w:0', startSegment: 0, endSegment: 2 },
      { entityKey: 's:w:1', startSegment: 2, endSegment: 3 },
    ])
  })

  it('allocates different batched geometry buffers for different tree IDs', () => {
    const source = fixtureMaterials().source
    const a = makeBatchedTreeObject(asset, 'full', placement, source)
    const b = makeBatchedTreeObject(
      asset,
      'full',
      { id: 'tree-b', index: 1, x: -10, z: -20, yaw: 1 },
      source,
    )
    const aLines = a.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)
    const bLines = b.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)

    expect(aLines).toHaveLength(bLines.length)
    for (let index = 0; index < aLines.length; index++) {
      expect(aLines[index]).not.toBe(bLines[index])
      expect(aLines[index]!.geometry).not.toBe(bLines[index]!.geometry)
      const aStarts = aLines[index]!.geometry.getAttribute('instanceStart') as THREE.InterleavedBufferAttribute
      const bStarts = bLines[index]!.geometry.getAttribute('instanceStart') as THREE.InterleavedBufferAttribute
      expect(aStarts.data).not.toBe(bStarts.data)
      expect(aLines[index]!.userData['treeId']).toBe('tree-a')
      expect(bLines[index]!.userData['treeId']).toBe('tree-b')
    }
  })

  it('uses only derived reduced branches and batches them into polarity draws', () => {
    const group = makeBatchedTreeObject(asset, 'reduced', placement, fixtureMaterials().source)
    const lines = group.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)

    expect(group.children).toHaveLength(2)
    expect(lines).toHaveLength(2)
    expect(lines.flatMap((line) => line.userData['entityKeys']).sort()).toEqual([
      'b:reduced-even', 'b:reduced-odd',
    ])
    expect(lines.flatMap(segmentsOf).map((segment) => segment.join(',')).sort()).toEqual([
      '0,0,0,0,2,0', '0,2,0,1,3,0',
    ])
  })

  it('creates one additive derived-color and derived-size marker sprite', () => {
    const group = makeMarkerObject(asset, placement, fixtureMaterials().source)

    expect(group.children).toHaveLength(1)
    const marker = group.children[0]!
    expect(marker).toBeInstanceOf(THREE.Sprite)
    expect((marker as THREE.Sprite).material.color.getHexString()).toBe('123456')
    expect((marker as THREE.Sprite).material.blending).toBe(THREE.AdditiveBlending)
    expect(marker.scale.toArray()).toEqual([1.25, 1.25, 1])
    expect(marker.userData['treeId']).toBe('tree-a')
    expect(marker.userData['entityKind']).toBe('marker')
  })

  it('disposes each owned geometry once without disposing shared materials or textures', () => {
    const resources = fixtureMaterials()
    const group = makeBatchedTreeObject(asset, 'full', placement, resources.source)
    const lines = group.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)
    const sharedGeometry = lines[0]!.geometry
    group.add(new LineSegments2(sharedGeometry, lines[0]!.material))
    const geometrySpies = new Map(
      lines.map((line) => [line.geometry, vi.spyOn(line.geometry, 'dispose')] as const),
    )
    const materialSpies = [...resources.materials].map((material) => vi.spyOn(material, 'dispose'))
    const textureSpies = [...resources.textures].map((texture) => vi.spyOn(texture, 'dispose'))

    disposeTreeObject(group)

    for (const spy of geometrySpies.values()) expect(spy).toHaveBeenCalledTimes(1)
    for (const spy of materialSpies) expect(spy).not.toHaveBeenCalled()
    for (const spy of textureSpies) expect(spy).not.toHaveBeenCalled()
  })
})
