import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { LineSegments2 } from 'three/examples/jsm/lines/LineSegments2.js'
import { LineSegmentsGeometry } from 'three/examples/jsm/lines/LineSegmentsGeometry.js'
import type { Entity } from '../src/view3d/scene'
import type { LodLevel } from './lod-policy'
import type { TreePlacement } from './placement'
import type { SavedTreeLayout, SavedTreeLods } from './world'

type LineEntity = Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>
type SpriteEntity = Extract<Entity, { kind: 'pip' | 'label' }>
type GeometryLod = Extract<LodLevel, 'full' | 'reduced'>

export type OrchardMaterialSource = {
  line(entity: LineEntity, width: number): LineMaterial
  sprite(entity: SpriteEntity): THREE.SpriteMaterial
  marker(marker: SavedTreeLods['marker']): THREE.SpriteMaterial
}

type EntitySegmentRange = {
  readonly entityKey: string
  readonly startSegment: number
  readonly endSegment: number
}

type LineBatch = {
  readonly kind: LineEntity['kind']
  readonly width: number
  readonly color: string
  readonly material: LineMaterial
  readonly positions: number[]
  readonly entityKeys: string[]
  readonly entityRanges: EntitySegmentRange[]
}

function treeGroup(placement: TreePlacement, representation: 'raw' | GeometryLod | 'marker'): THREE.Group {
  const group = new THREE.Group()
  group.name = placement.id
  group.position.set(placement.x, 0, placement.z)
  group.rotation.y = placement.yaw
  group.userData['treeId'] = placement.id
  group.userData['treeIndex'] = placement.index
  group.userData['representation'] = representation
  return group
}

function lineWidth(layout: SavedTreeLayout, entity: LineEntity): number {
  return entity.kind === 'branch' ? layout.widths.branch : layout.widths.curve
}

function spriteObject(entity: SpriteEntity, placement: TreePlacement, materials: OrchardMaterialSource): THREE.Sprite {
  const sprite = new THREE.Sprite(materials.sprite(entity))
  sprite.position.set(entity.pos.x, entity.pos.y, entity.pos.z)
  const height = entity.kind === 'pip' ? 0.18 : 0.7
  const aspect = entity.kind === 'label'
    ? Number(sprite.material.userData['aspect'] ?? 2)
    : 1
  sprite.scale.set(height * aspect, height, 1)
  sprite.userData['entityKey'] = entity.key
  sprite.userData['entityKind'] = entity.kind
  sprite.userData['treeId'] = placement.id
  sprite.userData['treeIndex'] = placement.index
  return sprite
}

export function makeRawTreeObject(
  layout: SavedTreeLayout,
  placement: TreePlacement,
  materials: OrchardMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, 'raw')
  for (const entity of layout.lods.full.entities) {
    let object: THREE.Object3D
    if (entity.kind === 'pip' || entity.kind === 'label') {
      object = spriteObject(entity, placement, materials)
    } else {
      const geometry = new LineGeometry()
      geometry.setPositions(entity.pts.flatMap(({ x, y, z }) => [x, y, z]))
      const line = new Line2(geometry, materials.line(entity, lineWidth(layout, entity)))
      line.computeLineDistances()
      object = line
      object.userData['entityKey'] = entity.key
      object.userData['entityKind'] = entity.kind
      object.userData['treeId'] = placement.id
      object.userData['treeIndex'] = placement.index
    }
    group.add(object)
  }
  return group
}

export function makeBatchedTreeObject(
  layout: SavedTreeLayout,
  lod: GeometryLod,
  placement: TreePlacement,
  materials: OrchardMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, lod)
  const batches = new Map<string, LineBatch>()
  const scene = layout.lods[lod]

  for (const entity of scene.entities) {
    if (entity.kind === 'pip' || entity.kind === 'label') {
      if (lod === 'full') group.add(spriteObject(entity, placement, materials))
      continue
    }
    if (lod === 'reduced' && entity.kind !== 'branch') continue

    const width = lineWidth(layout, entity)
    const material = materials.line(entity, width)
    const color = material.color.getHexString()
    const key = `${entity.kind}:${width}:${color}`
    let batch = batches.get(key)
    if (batch === undefined) {
      batch = {
        kind: entity.kind,
        width,
        color,
        material,
        positions: [],
        entityKeys: [],
        entityRanges: [],
      }
      batches.set(key, batch)
    }

    const startSegment = batch.positions.length / 6
    for (let index = 1; index < entity.pts.length; index++) {
      const start = entity.pts[index - 1]!, end = entity.pts[index]!
      batch.positions.push(start.x, start.y, start.z, end.x, end.y, end.z)
    }
    batch.entityKeys.push(entity.key)
    batch.entityRanges.push({
      entityKey: entity.key,
      startSegment,
      endSegment: batch.positions.length / 6,
    })
  }

  for (const batch of batches.values()) {
    const geometry = new LineSegmentsGeometry()
    geometry.setPositions(batch.positions)
    const line = new LineSegments2(geometry, batch.material)
    line.userData['entityKind'] = batch.kind
    line.userData['entityKeys'] = batch.entityKeys
    line.userData['entityRanges'] = batch.entityRanges
    line.userData['treeId'] = placement.id
    line.userData['treeIndex'] = placement.index
    line.userData['width'] = batch.width
    line.userData['color'] = batch.color
    group.add(line)
  }

  return group
}

export function makeMarkerObject(
  layout: SavedTreeLayout,
  placement: TreePlacement,
  materials: OrchardMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, 'marker')
  const marker = new THREE.Sprite(materials.marker(layout.lods.marker))
  marker.position.set(layout.bounds.center.x, layout.bounds.center.y, layout.bounds.center.z)
  marker.scale.set(layout.lods.marker.size, layout.lods.marker.size, 1)
  marker.userData['entityKind'] = 'marker'
  marker.userData['treeId'] = placement.id
  marker.userData['treeIndex'] = placement.index
  group.add(marker)
  return group
}

export function disposeTreeObject(group: THREE.Object3D): void {
  const geometries = new Set<THREE.BufferGeometry>()
  group.traverse((object) => {
    if (!('geometry' in object)) return
    const geometry = (object as THREE.Mesh).geometry
    if (geometry instanceof THREE.BufferGeometry) geometries.add(geometry)
  })
  for (const geometry of geometries) geometry.dispose()
}
