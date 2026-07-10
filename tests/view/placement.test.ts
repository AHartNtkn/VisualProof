import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import {
  beginBodyPlacement,
  cancelBodyPlacement,
  previewBodyPlacement,
  seedBodyPlacement,
} from '../../src/view/placement'
import { advanceInteractivePhysics } from '../../src/view/physics-drag'

describe('semantic placement preview', () => {
  it('moves and cancels a body without changing the fixed destination geometry', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const node = b.ref(cut, 'R', 0)
    const engine = mkEngine(b.build(), [])
    const beforeCircle = engine.regions.get(cut)
    const placement = beginBodyPlacement(engine, node)

    previewBodyPlacement(engine, placement, { x: 40, y: 35 })
    expect(engine.bodies.get(node)!.pos).toEqual({ x: 40, y: 35 })
    expect(engine.regions.get(cut)).toBe(beforeCircle)

    cancelBodyPlacement(engine, placement)
    expect(engine.bodies.get(node)!.pos).toEqual(placement.origin)
  })

  it('seeds a fresh body at an invocation point', () => {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, 'R', 0)
    const engine = mkEngine(b.build(), [])
    seedBodyPlacement(engine, node, { x: -7, y: 11 })
    expect(engine.bodies.get(node)!.pos).toEqual({ x: -7, y: 11 })
  })

  it('holds the placed body while connected passive physics stays live', () => {
    const b = new DiagramBuilder()
    const held = b.ref(b.root, 'held', 1)
    const neighbour = b.ref(b.root, 'neighbour', 1)
    b.wire(b.root, [
      { node: held, port: { kind: 'arg', index: 0 } },
      { node: neighbour, port: { kind: 'arg', index: 0 } },
    ])
    const engine = mkEngine(b.build(), [])
    engine.bodies.get(held)!.pos = { x: -55, y: 32 }
    engine.bodies.get(neighbour)!.pos = { x: 30, y: 0 }
    const placement = beginBodyPlacement(engine, held)
    previewBodyPlacement(engine, placement, { x: -70, y: 45 })
    const beforeNeighbour = { ...engine.bodies.get(neighbour)!.pos }

    for (let frame = 0; frame < 20; frame++) {
      advanceInteractivePhysics(engine, new Set([held]), null, true)
      expect(engine.bodies.get(held)!.pos).toEqual({ x: -70, y: 45 })
    }
    const afterNeighbour = engine.bodies.get(neighbour)!.pos
    expect(Math.hypot(afterNeighbour.x - beforeNeighbour.x, afterNeighbour.y - beforeNeighbour.y)).toBeGreaterThan(0.01)
  })
})
