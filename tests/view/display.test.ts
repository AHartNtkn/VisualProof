import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { renderScene, binderHue } from '../../src/view/display'
import { initialState, settle, DEFAULT_PARAMS } from '../../src/view/physics'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function scene() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('\\x. \\y. x'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('y'))
  void n
  void m
  const d = h.build()
  const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
  return buildScene(d, s.positions)
}

describe('renderScene', () => {
  it('paints regions first, then wires, then node structure', () => {
    const shapes = renderScene(scene())
    const firstNodeArc = shapes.findIndex((s) => s.kind === 'arc')
    const lastRegion = shapes.map((s) => s.kind).lastIndexOf('circle')
    const firstWire = shapes.findIndex((s) => s.kind === 'polyline')
    expect(lastRegion).toBeLessThan(firstWire)
    expect(firstWire).toBeLessThan(firstNodeArc)
  })

  it('paints polarity: negative cuts shade, positive cuts un-shade, bubbles stay open', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const bub = h.bubble(c1, 0)
    h.termNode(c2, p('\\x. x'))
    const d = h.build()
    void bub
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const shapes = renderScene(buildScene(d, s.positions))
    const circles = shapes.filter((x) => x.kind === 'circle')
    expect(circles).toHaveLength(3)
    const fills = circles.map((c) => (c.kind === 'circle' ? c.fill : undefined))
    // one shade fill (the negative depth-1 cut), one background fill (the
    // positive depth-2 cut), one open circle (the bubble)
    expect(fills.filter((f) => f !== undefined && f.startsWith('rgba'))).toHaveLength(1)
    expect(fills.filter((f) => f === '#fafaf7')).toHaveLength(1)
    expect(fills.filter((f) => f === undefined)).toHaveLength(1)
  })

  it('binder hues are distinct per binder row and stable', () => {
    expect(binderHue(0)).not.toBe(binderHue(1))
    expect(binderHue(3)).toBe(binderHue(3))
  })

  it('every shape carries finite coordinates', () => {
    for (const s of renderScene(scene())) {
      const nums: number[] = []
      if (s.kind === 'circle') nums.push(s.center.x, s.center.y, s.r)
      if (s.kind === 'arc') nums.push(s.center.x, s.center.y, s.r, s.a0, s.a1)
      if (s.kind === 'segment') nums.push(s.from.x, s.from.y, s.to.x, s.to.y)
      if (s.kind === 'polyline') for (const pt of s.points) nums.push(pt.x, pt.y)
      if (s.kind === 'label') nums.push(s.pos.x, s.pos.y)
      for (const x of nums) expect(Number.isFinite(x)).toBe(true)
    }
  })
})

describe('hover tethers', () => {
  it('emits one tether per var radial of the hovered node, in the binder hue', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. \\y. x y'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const sceneV = buildScene(d, s.positions)
    const plain = renderScene(sceneV)
    const hovered = renderScene(sceneV, { hoverNode: n })
    expect(hovered.length).toBeGreaterThan(plain.length)
    const tethers = hovered.filter((x) => x.kind === 'segment' && x.width === 2.5)
    expect(tethers).toHaveLength(2) // one per variable occurrence: x and y
  })

  it('no hover, no tethers (output unchanged)', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const sceneV = buildScene(d, s.positions)
    expect(renderScene(sceneV)).toEqual(renderScene(sceneV, {}))
  })
})
