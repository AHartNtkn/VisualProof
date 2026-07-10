import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import {
  advanceInteractivePhysics,
  cancelPhysicsDrag,
  commitPhysicsDragSample,
  type ActivePhysicsDrag,
} from '../../src/view/physics-drag'
import { recomputeRegions } from '../../src/view/relax'
import { semanticConflicts } from '../../src/view/constraints'

function connectedPair(): { engine: ReturnType<typeof mkEngine>; moving: string; neighbour: string } {
  const b = new DiagramBuilder()
  const moving = b.ref(b.root, 'moving', 1)
  const neighbour = b.ref(b.root, 'neighbour', 1)
  b.wire(b.root, [
    { node: moving, port: { kind: 'arg', index: 0 } },
    { node: neighbour, port: { kind: 'arg', index: 0 } },
  ])
  const engine = mkEngine(b.build(), [])
  engine.bodies.get(moving)!.pos = { x: -30, y: 0 }
  engine.bodies.get(neighbour)!.pos = { x: 30, y: 0 }
  engine.frame = { center: { x: 0, y: 0 }, half: 160 }
  recomputeRegions(engine)
  return { engine, moving, neighbour }
}

describe('interactive physics drag', () => {
  it('keeps ungrabbed physics live while passive connection relaxation is paused', () => {
    const { engine, moving, neighbour } = connectedPair()
    const before = { ...engine.bodies.get(neighbour)!.pos }
    const active: ActivePhysicsDrag = {
      drag: {
        bodies: new Map([[moving, { x: 0, y: 0 }]]),
        origins: new Map([[moving, { x: -30, y: 0 }]]),
      },
      cursor: { x: -65, y: 35 },
    }
    commitPhysicsDragSample(engine, active)

    for (let frame = 0; frame < 20; frame++) {
      advanceInteractivePhysics(engine, new Set(), active, false)
      expect(engine.bodies.get(moving)!.pos).toEqual(active.cursor)
    }

    const after = engine.bodies.get(neighbour)!.pos
    expect(Math.hypot(after.x - before.x, after.y - before.y)).toBeGreaterThan(0.01)
    expect(semanticConflicts(engine)).toEqual([])
  })

  it('commits the final pointer sample without waiting for an animation frame', () => {
    const { engine, moving } = connectedPair()
    const active: ActivePhysicsDrag = {
      drag: {
        bodies: new Map([[moving, { x: 3, y: -4 }]]),
        origins: new Map([[moving, { x: -30, y: 0 }]]),
      },
      cursor: { x: 12, y: 18 },
    }

    const projection = commitPhysicsDragSample(engine, active)

    expect(projection.blocked).toBe(false)
    expect(engine.bodies.get(moving)!.pos).toEqual({ x: 15, y: 14 })
    expect(semanticConflicts(engine)).toEqual([])
  })

  it('restores the legal pointer-down sample when a drag is cancelled', () => {
    const { engine, moving } = connectedPair()
    const active: ActivePhysicsDrag = {
      drag: {
        bodies: new Map([[moving, { x: 0, y: 0 }]]),
        origins: new Map([[moving, { x: -30, y: 0 }]]),
      },
      cursor: { x: -10, y: 45 },
    }

    commitPhysicsDragSample(engine, active)
    expect(engine.bodies.get(moving)!.pos).not.toEqual({ x: -30, y: 0 })

    cancelPhysicsDrag(engine, active.drag)

    expect(engine.bodies.get(moving)!.pos).toEqual({ x: -30, y: 0 })
    expect(semanticConflicts(engine)).toEqual([])
  })
})
