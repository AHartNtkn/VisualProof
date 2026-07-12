import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, DISC_R } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, nextTheme, LIGHT, DARK, THEMES } from '../../src/view/paint'
import { drawShapes } from '../../src/view/canvas'

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
