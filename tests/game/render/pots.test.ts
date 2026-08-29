import * as THREE from 'three'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it, vi } from 'vitest'
import { snapshotFromDiagram } from '../../../src/game/diagram-snapshot'
import { TreeRenderAssetCache } from '../../../src/game/render/assets'
import { makePotObject, type PotRender } from '../../../src/game/render/pots'
import type { TreeMaterialSource } from '../../../src/game/render/tree-objects'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DARK } from '../../../src/view/paint'

function materials(): TreeMaterialSource {
  return {
    line: (_entity, width) => new LineMaterial({ color: '#7fffd4', linewidth: width, worldUnits: true }),
    sprite: () => new THREE.SpriteMaterial({ color: '#7fffd4' }),
    marker: (marker) => new THREE.SpriteMaterial({ color: marker.color }),
  }
}

function pot(): PotRender {
  return {
    orderId: 'starter-double-cut',
    placement: { x: 3, z: -8, yaw: 0.25 },
    goal: snapshotFromDiagram(new DiagramBuilder().build()),
  }
}

describe('order pot rendering', () => {
  it('creates a tagged physical pot with a target sphere and scaled goal hologram', () => {
    const render = pot()
    const asset = new TreeRenderAssetCache(DARK).get(render.goal)
    const object = makePotObject(render, asset, materials())

    expect(object.group.userData['orderId']).toBe(render.orderId)
    expect(object.group.position.toArray()).toEqual([3, 0, -8])
    expect(object.group.rotation.y).toBe(0.25)
    expect(object.target.center.toArray()).toEqual([3, 0.55, -8])
    expect(object.target.radius).toBeGreaterThan(0)
    expect(object.group.getObjectByName('goal-hologram')!.scale.x).toBeLessThan(1)
  })

  it('disposes every pot and hologram geometry and material on removal', () => {
    const geometryDispose = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose')
    const materialDispose = vi.spyOn(THREE.Material.prototype, 'dispose')
    const render = pot()
    const asset = new TreeRenderAssetCache(DARK).get(render.goal)
    const object = makePotObject(render, asset, materials())
    const before = { geometry: geometryDispose.mock.calls.length, material: materialDispose.mock.calls.length }

    object.dispose()

    expect(geometryDispose.mock.calls.length).toBeGreaterThan(before.geometry)
    expect(materialDispose.mock.calls.length).toBeGreaterThan(before.material)
  })
})
