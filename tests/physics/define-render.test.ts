import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine, settle, paint, LIGHT, DISC_R } from '../../src/view/index'

/** An n-ary relation signature over individuals (ref/atom arity, new sig API). */
const rel = (n: number) => relSig(Array.from({ length: n }, () => IOTA))

describe('reference argument-order rendering', () => {
  it('an arity-2 ref draws exactly one pip on its rim', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'R', rel(2))
    const diagram = builder.build()
    const e = mkEngine(diagram, [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    const label = shapes.find((s) => s.kind === 'label' && s.text === 'R')!
    expect(label.kind === 'label').toBe(true)
    const c = label.kind === 'label' ? label.center : { x: 0, y: 0 }
    const inkDots = shapes.filter((s) => s.kind === 'dot' && s.fill === LIGHT.ink)
    expect(inkDots).toHaveLength(1)
    const pip = inkDots[0]!
    const dist = pip.kind === 'dot' ? Math.hypot(pip.center.x - c.x, pip.center.y - c.y) : 0
    expect(dist).toBeCloseTo(DISC_R, 5)
    expect(diagram.nodes[ref]).toMatchObject({ kind: 'ref', defId: 'R', sig: rel(2) })
  })

  it('a ref to an ARITY-1 relation draws no pip (a single leg needs no order mark)', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'S', rel(1))
    const e = mkEngine(b.build(), [])
    settle(e, 400)
    const inkDots = paint(e, LIGHT).filter((s) => s.kind === 'dot' && s.fill === LIGHT.ink)
    expect(inkDots).toHaveLength(0)
  })
})
