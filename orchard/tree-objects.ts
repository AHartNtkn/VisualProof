import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import type { Entity, Scene3 } from '../src/view3d/scene'
import type { TreePlacement } from './placement'

type LineEntity = Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>
type SpriteEntity = Extract<Entity, { kind: 'pip' | 'label' }>

export type OrchardMaterialSource = {
  line(entity: LineEntity): LineMaterial
  sprite(entity: SpriteEntity): THREE.SpriteMaterial
}

export function makeTreeObject(
  tree: Scene3,
  placement: TreePlacement,
  materials: OrchardMaterialSource,
): THREE.Group {
  const group = new THREE.Group()
  group.name = placement.id
  group.position.set(placement.x, 0, placement.z)
  group.rotation.y = placement.yaw

  for (const entity of tree.entities) {
    let object: THREE.Object3D
    if (entity.kind === 'pip' || entity.kind === 'label') {
      const sprite = new THREE.Sprite(materials.sprite(entity))
      sprite.position.set(entity.pos.x, entity.pos.y, entity.pos.z)
      const height = entity.kind === 'pip' ? 0.18 : 0.7
      const aspect = entity.kind === 'label'
        ? Number(sprite.material.userData['aspect'] ?? 2)
        : 1
      sprite.scale.set(height * aspect, height, 1)
      object = sprite
    } else {
      const geometry = new LineGeometry()
      geometry.setPositions(entity.pts.flatMap(({ x, y, z }) => [x, y, z]))
      const line = new Line2(geometry, materials.line(entity))
      line.computeLineDistances()
      object = line
    }
    object.userData['entityKey'] = entity.key
    object.userData['treeIndex'] = placement.index
    group.add(object)
  }

  return group
}
