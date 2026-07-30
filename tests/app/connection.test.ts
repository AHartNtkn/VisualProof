import { describe, expect, it } from 'vitest'
import type { Hit } from '../../src/app/hittest'
import {
  ConnectionDragController,
  type ConnectionGesture,
} from '../../src/app/interact/connection'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { WireId } from '../../src/kernel/diagram/diagram'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'

function sample(point: Vec2, hit: Hit | null = null): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: point,
    screen: point,
    world: point,
    hit,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

function wireHit(id: WireId): Hit {
  return { kind: 'wire', id }
}

describe('wire-to-wire connection drag', () => {
  it('commits a source/target pair on a landed drag', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [])
    const right = builder.wire(negative, [])
    const engine = mkEngine(builder.build(), [])
    const leftPoint = engine.bodies.get(`j:${left}`)!.pos
    const rightPoint = engine.bodies.get(`j:${right}`)!.pos
    const gestures: ConnectionGesture[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (gesture) => { gestures.push(gesture); return true },
      refuse: () => undefined,
    })

    const claim = drag.claim(sample(leftPoint, wireHit(left)))!
    claim.move(sample(rightPoint, wireHit(right)))
    claim.release(sample(rightPoint, wireHit(right)), true)

    expect(gestures).toEqual([{
      source: { wire: left, endpoint: null },
      target: { wire: right, endpoint: null },
    }])
  })

  it('refuses a release in the open with the diagram unchanged', () => {
    const builder = new DiagramBuilder()
    const wire = builder.wire(builder.root, [])
    const engine = mkEngine(builder.build(), [])
    const start = engine.bodies.get(`j:${wire}`)!.pos
    const gestures: ConnectionGesture[] = []
    const refusals: string[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (gesture) => { gestures.push(gesture); return true },
      refuse: (text) => { refusals.push(text) },
    })

    const claim = drag.claim(sample(start, wireHit(wire)))!
    const away = vec(start.x + 300, start.y + 300)
    claim.move(sample(away))
    claim.release(sample(away), true)

    expect(gestures).toEqual([])
    expect(refusals).toEqual(['release on a line endpoint or another line'])
  })
})
