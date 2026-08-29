import * as THREE from 'three'
import { describe, expect, it } from 'vitest'
import {
  applyPlacement,
  localPointToWorld,
  orchardPlacements,
  worldDirectionToLocal,
  worldPointToLocal,
  worldSphere,
  type TreePlacement,
} from '../../../src/game/render/placement'

const placement: TreePlacement = {
  id: 'tree-transform',
  index: 7,
  x: 17,
  z: -11,
  yaw: Math.PI / 3,
}

describe('orchardPlacements', () => {
  it('lays out stable tree records progressively from the world center', () => {
    const placements = orchardPlacements(5, 10)

    expect(placements.map(({ id, index, x, z }) => ({ id, index, x, z }))).toEqual([
      { id: 'tree-0000', index: 0, x: 0, z: 0 },
      { id: 'tree-0001', index: 1, x: 10, z: 0 },
      { id: 'tree-0002', index: 2, x: 10, z: 10 },
      { id: 'tree-0003', index: 3, x: 0, z: 10 },
      { id: 'tree-0004', index: 4, x: -10, z: 10 },
    ])
  })

  it('keeps every pair of trees at least one spacing apart', () => {
    const placements = orchardPlacements(37, 18)

    for (let i = 0; i < placements.length; i++) {
      for (let j = i + 1; j < placements.length; j++) {
        const a = placements[i]!, b = placements[j]!
        expect(Math.hypot(a.x - b.x, a.z - b.z)).toBeGreaterThanOrEqual(18)
      }
    }
  })

  it('gives trees varied but repeatable rotations', () => {
    const first = orchardPlacements(12, 18)
    const second = orchardPlacements(12, 18)

    expect(first).toEqual(second)
    expect(new Set(first.map(({ yaw }) => yaw)).size).toBeGreaterThan(8)
    for (const { yaw } of first) {
      expect(yaw).toBeGreaterThanOrEqual(0)
      expect(yaw).toBeLessThan(Math.PI * 2)
    }
  })

  it('rejects counts that cannot describe a finite collection of trees', () => {
    expect(() => orchardPlacements(-1, 10)).toThrow('non-negative integer')
    expect(() => orchardPlacements(1.5, 10)).toThrow('non-negative integer')
    expect(() => orchardPlacements(Number.POSITIVE_INFINITY, 10)).toThrow('non-negative integer')
  })
})

describe('tree placement transform', () => {
  it('round-trips points through the same positive-Y rotation used by rendered objects', () => {
    const local = { x: 2, y: 4, z: -3 }
    const world = localPointToWorld(local, placement)

    const roundTripped = worldPointToLocal(world, placement)
    expect(roundTripped.x).toBeCloseTo(local.x)
    expect(roundTripped.y).toBeCloseTo(local.y)
    expect(roundTripped.z).toBeCloseTo(local.z)

    const object = new THREE.Object3D()
    applyPlacement(object, placement)
    object.updateMatrixWorld(true)
    const rendered = new THREE.Vector3(local.x, local.y, local.z).applyMatrix4(object.matrixWorld)
    expect(world.x).toBeCloseTo(rendered.x)
    expect(world.y).toBeCloseTo(rendered.y)
    expect(world.z).toBeCloseTo(rendered.z)
  })

  it('transforms directions and spheres without translating direction or changing radius', () => {
    const localDirection = { x: 2, y: -1, z: -3 }
    const localBounds = { center: { x: 2, y: 4, z: -3 }, radius: 6 }
    const sphere = worldSphere(localBounds, placement)
    const expectedCenter = localPointToWorld(localBounds.center, placement)
    const worldDirection = new THREE.Vector3(
      localDirection.x,
      localDirection.y,
      localDirection.z,
    ).applyAxisAngle(new THREE.Vector3(0, 1, 0), placement.yaw)

    const roundTripped = worldDirectionToLocal({
      x: worldDirection.x,
      y: worldDirection.y,
      z: worldDirection.z,
    }, placement)
    expect(roundTripped.x).toBeCloseTo(localDirection.x)
    expect(roundTripped.y).toBeCloseTo(localDirection.y)
    expect(roundTripped.z).toBeCloseTo(localDirection.z)
    expect(sphere.center.x).toBeCloseTo(expectedCenter.x)
    expect(sphere.center.y).toBeCloseTo(expectedCenter.y)
    expect(sphere.center.z).toBeCloseTo(expectedCenter.z)
    expect(sphere.radius).toBe(6)
  })
})
