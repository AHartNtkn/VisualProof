import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { LineSegments2 } from 'three/examples/jsm/lines/LineSegments2.js'
import { LineSegmentsGeometry } from 'three/examples/jsm/lines/LineSegmentsGeometry.js'
import type { Entity } from '../../view3d/scene'
import type { FadedEntity } from '../../view3d/transition'
import type { LodLevel } from './lod-policy'
import type { TreePlacement } from './placement'
import type { TreeLodAssets, TreeRenderAsset } from './types'
import type { PointedTreePart } from '../session'

type LineEntity = Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>
type SpriteEntity = Extract<Entity, { kind: 'pip' | 'label' }>
type GeometryLod = Extract<LodLevel, 'full' | 'reduced'>

export type TreeMaterialSource = {
  line(entity: LineEntity, width: number): LineMaterial
  sprite(entity: SpriteEntity): THREE.SpriteMaterial
  marker(marker: TreeLodAssets['marker']): THREE.SpriteMaterial
}

export type EntitySegmentRange = {
  readonly entityKey: string
  readonly startSegment: number
  readonly endSegment: number
}

function entityKeyAt(intersection: THREE.Intersection): string | null {
  const direct = intersection.object.userData['entityKey']
  if (typeof direct === 'string') return direct
  if (!(intersection.object instanceof LineSegments2)) return null
  const segment = intersection.faceIndex
  const ranges = intersection.object.userData['entityRanges'] as readonly EntitySegmentRange[] | undefined
  if (segment === undefined || segment === null || ranges === undefined) return null
  return ranges.find(({ startSegment, endSegment }) =>
    segment >= startSegment && segment < endSegment,
  )?.entityKey ?? null
}

export function pointAtVisibleParts(
  raycaster: THREE.Raycaster,
  objects: readonly THREE.Object3D[],
  reach: number,
  orbitTarget: string | null,
): PointedTreePart | null {
  const candidates = orbitTarget === null
    ? objects
    : objects.filter((object) => object.userData['treeId'] === orbitTarget)
  const intersections = raycaster.intersectObjects([...candidates], true)
  for (const intersection of intersections) {
    if (!Number.isFinite(intersection.distance) || intersection.distance > reach) continue
    const treeId = intersection.object.userData['treeId']
    const entityKey = entityKeyAt(intersection)
    if (typeof treeId === 'string' && entityKey !== null) {
      return { treeId, entityKey, distance: intersection.distance }
    }
  }
  return null
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

function treeGroup(
  placement: TreePlacement,
  representation: 'raw' | GeometryLod | 'marker' | 'dynamic',
): THREE.Group {
  const group = new THREE.Group()
  group.name = placement.id
  group.position.set(placement.x, 0, placement.z)
  group.rotation.y = placement.yaw
  group.userData['treeId'] = placement.id
  group.userData['treeIndex'] = placement.index
  group.userData['representation'] = representation
  return group
}

function fadedMaterial<T extends THREE.Material>(material: T, alpha: number | undefined): T {
  const copy = material.clone() as T
  copy.opacity = alpha ?? 1
  copy.transparent = copy.opacity < 1
  if (copy.transparent) copy.depthWrite = false
  return copy
}

export function makeDynamicTreeObject(
  snapshot: { readonly entities: readonly FadedEntity[] },
  placement: TreePlacement,
  materials: TreeMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, 'dynamic')
  for (const entity of snapshot.entities) {
    let object: THREE.Object3D
    if (entity.kind === 'pip' || entity.kind === 'label') {
      const sprite = spriteObject(entity, placement, materials)
      sprite.material = fadedMaterial(sprite.material, entity.alpha)
      object = sprite
    } else {
      const geometry = new LineGeometry()
      geometry.setPositions(entity.pts.flatMap(({ x, y, z }) => [x, y, z]))
      const material = fadedMaterial(
        materials.line(entity, lineWidth({ branch: 0.10, curve: 0.05 }, entity)),
        entity.alpha,
      )
      const line = new Line2(geometry, material)
      line.computeLineDistances()
      line.userData['entityKey'] = entity.key
      line.userData['entityKind'] = entity.kind
      line.userData['treeId'] = placement.id
      line.userData['treeIndex'] = placement.index
      object = line
    }
    object.userData['ownsMaterial'] = true
    group.add(object)
  }
  return group
}

function lineWidth(widths: TreeRenderAsset['widths'], entity: LineEntity): number {
  return entity.kind === 'branch' ? widths.branch : widths.curve
}

function spriteObject(entity: SpriteEntity, placement: TreePlacement, materials: TreeMaterialSource): THREE.Sprite {
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
  asset: TreeRenderAsset,
  placement: TreePlacement,
  materials: TreeMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, 'raw')
  for (const entity of asset.lods.full.entities) {
    let object: THREE.Object3D
    if (entity.kind === 'pip' || entity.kind === 'label') {
      object = spriteObject(entity, placement, materials)
    } else {
      const geometry = new LineGeometry()
      geometry.setPositions(entity.pts.flatMap(({ x, y, z }) => [x, y, z]))
      const line = new Line2(geometry, materials.line(entity, lineWidth(asset.widths, entity)))
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
  asset: TreeRenderAsset,
  lod: GeometryLod,
  placement: TreePlacement,
  materials: TreeMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, lod)
  const batches = new Map<string, LineBatch>()
  const scene = asset.lods[lod]

  for (const entity of scene.entities) {
    if (entity.kind === 'pip' || entity.kind === 'label') {
      if (lod === 'full') group.add(spriteObject(entity, placement, materials))
      continue
    }
    if (lod === 'reduced' && entity.kind !== 'branch') continue

    const width = lineWidth(asset.widths, entity)
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
  asset: TreeRenderAsset,
  placement: TreePlacement,
  materials: TreeMaterialSource,
): THREE.Group {
  const group = treeGroup(placement, 'marker')
  const marker = new THREE.Sprite(materials.marker(asset.lods.marker))
  marker.position.set(asset.bounds.center.x, asset.bounds.center.y, asset.bounds.center.z)
  marker.scale.set(asset.lods.marker.size, asset.lods.marker.size, 1)
  marker.userData['entityKind'] = 'marker'
  marker.userData['treeId'] = placement.id
  marker.userData['treeIndex'] = placement.index
  group.add(marker)
  return group
}

export function disposeTreeObject(group: THREE.Object3D): void {
  const geometries = new Set<THREE.BufferGeometry>()
  const materials = new Set<THREE.Material>()
  group.traverse((object) => {
    if ('geometry' in object) {
      const geometry = (object as THREE.Mesh).geometry
      if (geometry instanceof THREE.BufferGeometry) geometries.add(geometry)
    }
    if (object.userData['ownsMaterial'] === true && 'material' in object) {
      const material = (object as THREE.Mesh).material
      if (Array.isArray(material)) material.forEach((entry) => materials.add(entry))
      else if (material instanceof THREE.Material) materials.add(material)
    }
  })
  for (const geometry of geometries) geometry.dispose()
  for (const material of materials) material.dispose()
}
