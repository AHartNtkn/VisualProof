import * as THREE from 'three'
import { Line2 } from 'three/examples/jsm/lines/Line2.js'
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js'
import { describe, expect, it } from 'vitest'
import { makeTreeObject, type OrchardMaterialSource } from '../../orchard/tree-objects'
import type { Entity, Scene3 } from '../../src/view3d/scene'

const scene: Scene3 = {
  center: { x: 0, y: 1, z: 0 },
  radius: 2,
  entities: [
    { kind: 'branch', key: 'b:root', polarity: 0, pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 2, z: 0 }] },
    { kind: 'strand', key: 's:w:0', wire: 'w', pts: [{ x: 0, y: 1, z: 0 }, { x: 1, y: 2, z: 0 }] },
    { kind: 'pip', key: 'p:n', node: 'n', ownerWire: 'w', pos: { x: 0, y: 1, z: 0 } },
  ],
}

const lineMaterial = new LineMaterial({ color: '#ffffff', linewidth: 2 })
const spriteMaterial = new THREE.SpriteMaterial({ color: '#ffffff' })
const materials: OrchardMaterialSource = {
  line: (_entity: Extract<Entity, { kind: 'branch' | 'ring' | 'strand' }>) => lineMaterial,
  sprite: (_entity: Extract<Entity, { kind: 'pip' | 'label' }>) => spriteMaterial,
}
const glow = { color: '#ffffff', intensity: 1800, distance: 32, decay: 2, height: 13 }

describe('makeTreeObject', () => {
  it('creates separate objects and geometry for every tree without instancing', () => {
    const a = makeTreeObject(scene, { id: 'tree-a', index: 0, x: 10, z: 20, yaw: 0.5 }, materials, glow)
    const b = makeTreeObject(scene, { id: 'tree-b', index: 1, x: -10, z: -20, yaw: 1 }, materials, glow)

    expect(a).not.toBe(b)
    expect(a.children).toHaveLength(scene.entities.length + 1)
    expect(b.children).toHaveLength(scene.entities.length + 1)
    expect(a.position.toArray()).toEqual([10, 0, 20])
    expect(a.rotation.y).toBe(0.5)

    const firstLight = a.children.find((child): child is THREE.PointLight => child instanceof THREE.PointLight)
    const secondLight = b.children.find((child): child is THREE.PointLight => child instanceof THREE.PointLight)
    expect(firstLight).toBeDefined()
    expect(secondLight).toBeDefined()
    expect(firstLight).not.toBe(secondLight)
    expect(firstLight!.color.getHexString()).toBe('ffffff')
    expect(firstLight!.intensity).toBe(1800)
    expect(firstLight!.distance).toBe(32)
    expect(firstLight!.decay).toBe(2)
    expect(firstLight!.position.toArray()).toEqual([0, 13, 0])

    const firstEntities = a.children.filter((child) => !(child instanceof THREE.PointLight))
    const secondEntities = b.children.filter((child) => !(child instanceof THREE.PointLight))
    for (let index = 0; index < scene.entities.length; index++) {
      const first = firstEntities[index]!, second = secondEntities[index]!
      expect(first).not.toBe(second)
      expect((first as THREE.InstancedMesh).isInstancedMesh).not.toBe(true)
      if (first instanceof Line2 && second instanceof Line2) {
        expect(first.geometry).not.toBe(second.geometry)
      }
    }
  })
})
