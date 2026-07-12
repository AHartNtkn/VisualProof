import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, DISC_R } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, nextTheme, LIGHT, DARK, THEMES } from '../../src/view/paint'

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
