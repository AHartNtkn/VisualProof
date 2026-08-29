import * as THREE from 'three'
import type { DiagramSnapshot } from '../diagram-snapshot'
import type { PotPlacement } from '../orders/catalog'
import { disposeTreeObject, makeRawTreeObject, type TreeMaterialSource } from './tree-objects'
import type { TreeRenderAsset } from './types'

export type PotRender = {
  readonly orderId: string
  readonly placement: PotPlacement
  readonly goal: DiagramSnapshot
}

export type PotObject = {
  readonly render: PotRender
  readonly group: THREE.Group
  readonly target: THREE.Sphere
  dispose(): void
}

const POT_TARGET_HEIGHT = 0.55
const POT_TARGET_RADIUS = 1.2

function ownedMaterial<T extends THREE.Material>(material: T): T {
  return material.clone() as T
}

function hologramMaterials(materials: TreeMaterialSource): TreeMaterialSource {
  return {
    line(entity, width) { return ownedMaterial(materials.line(entity, width)) },
    sprite(entity) { return ownedMaterial(materials.sprite(entity)) },
    marker(marker) { return ownedMaterial(materials.marker(marker)) },
  }
}

function releasePotObject(group: THREE.Group): void {
  disposeTreeObject(group)
}

export function makePotObject(
  render: PotRender,
  asset: TreeRenderAsset,
  materials: TreeMaterialSource,
): PotObject {
  const group = new THREE.Group()
  group.name = `order-pot:${render.orderId}`
  group.userData['orderId'] = render.orderId
  group.position.set(render.placement.x, 0, render.placement.z)
  group.rotation.y = render.placement.yaw

  const potMaterial = new THREE.MeshBasicMaterial({ color: '#38261d' })
  const pot = new THREE.Mesh(new THREE.CylinderGeometry(0.58, 0.72, 0.34, 16), potMaterial)
  pot.name = 'pot-body'
  pot.position.y = 0.17
  pot.userData['ownsMaterial'] = true
  group.add(pot)

  const rimMaterial = new THREE.MeshBasicMaterial({ color: '#b9f6ff' })
  const rim = new THREE.Mesh(new THREE.TorusGeometry(0.57, 0.055, 8, 20), rimMaterial)
  rim.name = 'pot-rim'
  rim.rotation.x = Math.PI / 2
  rim.position.y = 0.34
  rim.userData['ownsMaterial'] = true
  group.add(rim)

  const hologram = makeRawTreeObject(asset, {
    id: `goal:${render.orderId}`,
    index: 0,
    x: 0,
    z: 0,
    yaw: 0,
  }, hologramMaterials(materials))
  hologram.name = 'goal-hologram'
  hologram.position.y = 0.42
  hologram.scale.setScalar(0.18)
  hologram.traverse((object) => { object.userData['ownsMaterial'] = true })
  group.add(hologram)

  const target = new THREE.Sphere(
    new THREE.Vector3(render.placement.x, POT_TARGET_HEIGHT, render.placement.z),
    POT_TARGET_RADIUS,
  )
  let disposed = false
  return {
    render,
    group,
    target,
    dispose() {
      if (disposed) return
      disposed = true
      group.removeFromParent()
      releasePotObject(group)
    },
  }
}
