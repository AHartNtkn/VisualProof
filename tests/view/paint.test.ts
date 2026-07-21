import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, DISC_R, frameBounds, frameSlots } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, nextTheme, LIGHT, DARK, THEMES } from '../../src/view/paint'
import { drawShapes } from '../../src/view/canvas'
import { computeLegs } from '../../src/view/wires'

describe('authoritative content scale', () => {
  it('paint derives node size directly from Engine.scale', () => {
    const h = new DiagramBuilder()
    const ref = h.ref(h.root, 'R', 0)
    const e = mkEngine(h.build(), [])
    settle(e, 1)
    e.scale = 2

    const body = e.bodies.get(ref)!
    const disc = paint(e, LIGHT).find((shape) =>
      shape.kind === 'circle'
      && shape.center.x === body.pos.x
      && shape.center.y === body.pos.y
      && shape.r === 2 * DISC_R)
    expect(disc, 'rendering must read the engine-owned scale without body state').toBeDefined()
  })
})

describe('theme constants', () => {
  it('ships the two first-class themes', () => {
    expect(THEMES).toHaveLength(2)
    expect(THEMES.map((t) => t.name)).toEqual([LIGHT.name, DARK.name])
    expect(LIGHT.wireGlow).toBe(false)
    expect(DARK.wireGlow).toBe(true)
  })

  it('nextTheme flips between the two first-class themes', () => {
    expect(nextTheme(LIGHT)).toBe(DARK)
    expect(nextTheme(DARK)).toBe(LIGHT)
  })
})

describe('canvas labels', () => {
  it('fits the complete label at the canvas boundary without substring truncation', () => {
    const drawn: { text: string; maxWidth: number; font: string }[] = []
    let currentFont = ''
    const context = {
      lineJoin: '',
      lineCap: '',
      get font() { return currentFont },
      set font(value: string) { currentFont = value },
      textAlign: '',
      textBaseline: '',
      fillStyle: '',
      measureText(text: string) {
        const size = Number(/ ([0-9.]+)px /.exec(currentFont)?.[1] ?? 10)
        return { width: text.length * size * 0.7 } as TextMetrics
      },
      fillText(text: string, _x: number, _y: number, maxWidth: number) {
        drawn.push({ text, maxWidth, font: currentFont })
      },
    } as unknown as CanvasRenderingContext2D
    const label = 'VeryLongUnqualifiedRelation'

    drawShapes(context, [{ kind: 'label', center: { x: 0, y: 0 }, text: label, color: '#000', r: 9, font: 'serif' }], {
      scale: 2,
      offsetX: 0,
      offsetY: 0,
    })

    expect(drawn).toHaveLength(1)
    expect(drawn[0]!.text).toBe(label)
    expect(drawn[0]!.maxWidth).toBeLessThan(2 * 9 * 2)
    expect(Number(/ ([0-9.]+)px /.exec(drawn[0]!.font)?.[1])).toBeLessThan(14)
  })
})

describe('endpointless frame ports', () => {
  const dotsAt = (shapes: ReturnType<typeof paint>, point: { x: number; y: number }) =>
    shapes.filter((shape) => shape.kind === 'dot' && Math.hypot(shape.center.x - point.x, shape.center.y - point.y) < 1e-6)

  it('renders endpointless boundary wires at ordered slots with only port 0 prominent', () => {
    const h = new DiagramBuilder()
    const wires = [h.wire(h.root, []), h.wire(h.root, []), h.wire(h.root, [])]
    const engine = mkEngine(h.build(), wires)
    settle(engine, 20)
    engine.slotShift = 1
    const shapes = paint(engine, LIGHT)
    const slots = frameSlots(frameBounds(engine)!, 3)
    const dots = slots.map((slot) => dotsAt(shapes, slot.point))

    expect(dots[0]).toHaveLength(1)
    expect(dots[1]).toHaveLength(1)
    expect(dots[2]).toHaveLength(1)
    const at0 = dots[0]![0]!
    const at1 = dots[1]![0]!
    const at2 = dots[2]![0]!
    if (at0.kind !== 'dot' || at1.kind !== 'dot' || at2.kind !== 'dot') throw new Error('frame ports must paint as dots')
    expect(at1.rPx).toBeGreaterThan(at0.rPx)
    expect(at0.rPx).toBe(at2.rPx)
    expect(wires.some((wire) => engine.bodies.has(`j:${wire}`))).toBe(false)
  })

  it('paints both frame ports and the connecting line for a repeated boundary wire', () => {
    const h = new DiagramBuilder()
    const shared = h.wire(h.root, [])
    const engine = mkEngine(h.build(), [shared, shared])
    settle(engine, 20)
    engine.slotShift = 1
    const shapes = paint(engine, LIGHT)
    const slots = frameSlots(frameBounds(engine)!, 2)
    const logical0 = dotsAt(shapes, slots[1]!.point)
    const logical1 = dotsAt(shapes, slots[0]!.point)

    expect(logical0).toHaveLength(1)
    expect(logical1).toHaveLength(1)
    if (logical0[0]!.kind !== 'dot' || logical1[0]!.kind !== 'dot') throw new Error('frame ports must paint as dots')
    expect(logical0[0]!.rPx).toBeGreaterThan(logical1[0]!.rPx)
    expect(computeLegs(engine).filter((leg) => leg.leg.wid === shared)).toHaveLength(1)
    expect(shapes.some((shape) => shape.kind === 'polyline')).toBe(true)
  })
})
