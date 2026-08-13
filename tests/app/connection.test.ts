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
import { segment, spread } from './helpers/build'

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
    const left = segment(builder, negative)
    const right = segment(builder, negative)
    const engine = mkEngine(builder.build(), [])
    const leftPoint = spread(engine, left, vec(100, 100))
    const rightPoint = spread(engine, right, vec(500, 100))
    const gestures: ConnectionGesture[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (gesture) => { gestures.push(gesture); return true },
      refuse: () => undefined,
    })

    const claim = drag.claim(sample(leftPoint, wireHit(left.wire)))!
    claim.move(sample(rightPoint, wireHit(right.wire)))
    claim.release(sample(rightPoint, wireHit(right.wire)), true)

    expect(gestures).toEqual([{
      source: { wire: left.wire, endpoint: null },
      target: { wire: right.wire, endpoint: null },
    }])
  })

  it('refuses a release in the open with the diagram unchanged', () => {
    const builder = new DiagramBuilder()
    const wire = segment(builder, builder.root)
    const engine = mkEngine(builder.build(), [])
    const start = spread(engine, wire, vec(100, 100))
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

    const claim = drag.claim(sample(start, wireHit(wire.wire)))!
    const away = vec(start.x + 300, start.y + 300)
    claim.move(sample(away))
    claim.release(sample(away), true)

    expect(gestures).toEqual([])
    expect(refusals).toEqual(['release on a line endpoint or another line'])
  })
})
