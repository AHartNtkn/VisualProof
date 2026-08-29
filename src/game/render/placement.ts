import * as THREE from 'three'
import type { Vec3 } from '../../view3d/vec3'

export type TreePlacement = {
  readonly id: string
  readonly index: number
  readonly x: number
  readonly z: number
  readonly yaw: number
}

export function localPointToWorld(point: Vec3, placement: TreePlacement): Vec3 {
  const cosine = Math.cos(placement.yaw)
  const sine = Math.sin(placement.yaw)
  return {
    x: placement.x + point.x * cosine + point.z * sine,
    y: point.y,
    z: placement.z - point.x * sine + point.z * cosine,
  }
}

export function worldPointToLocal(point: Vec3, placement: TreePlacement): Vec3 {
  const cosine = Math.cos(placement.yaw)
  const sine = Math.sin(placement.yaw)
  const x = point.x - placement.x
  const z = point.z - placement.z
  return {
    x: x * cosine - z * sine,
    y: point.y,
    z: x * sine + z * cosine,
  }
}

export function worldDirectionToLocal(direction: Vec3, placement: TreePlacement): Vec3 {
  const cosine = Math.cos(placement.yaw)
  const sine = Math.sin(placement.yaw)
  return {
    x: direction.x * cosine - direction.z * sine,
    y: direction.y,
    z: direction.x * sine + direction.z * cosine,
  }
}

export function worldSphere(
  bounds: { readonly center: Vec3; readonly radius: number },
  placement: TreePlacement,
): THREE.Sphere {
  const center = localPointToWorld(bounds.center, placement)
  return new THREE.Sphere(
    new THREE.Vector3(center.x, center.y, center.z),
    bounds.radius,
  )
}

export function applyPlacement(object: THREE.Object3D, placement: TreePlacement): void {
  object.position.set(placement.x, 0, placement.z)
  object.rotation.set(0, placement.yaw, 0)
}

export function orchardPlacements(count: number, spacing: number): TreePlacement[] {
  if (!Number.isInteger(count) || count < 0) {
    throw new Error('tree count must be a non-negative integer')
  }
  if (!(spacing > 0) || !Number.isFinite(spacing)) {
    throw new Error('tree spacing must be finite and positive')
  }
  if (count === 0) return []

  const placements: TreePlacement[] = []
  let cellX = 0, cellZ = 0
  let directionX = 1, directionZ = 0
  let legLength = 1, legProgress = 0, legsAtLength = 0
  for (let index = 0; index < count; index++) {
    placements.push({
      id: `tree-${String(index).padStart(4, '0')}`,
      index,
      x: cellX * spacing,
      z: cellZ * spacing,
      yaw: (index * 2.399963229728653) % (Math.PI * 2),
    })
    cellX += directionX
    cellZ += directionZ
    legProgress++
    if (legProgress === legLength) {
      ;[directionX, directionZ] = [-directionZ, directionX]
      legProgress = 0
      legsAtLength++
      if (legsAtLength === 2) {
        legsAtLength = 0
        legLength++
      }
    }
  }
  return placements
}
