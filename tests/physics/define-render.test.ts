import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyRelFold } from '../../src/kernel/rules/reldef'
import { defineRelation } from '../../src/app/define'
import { mkEngine, settle, paint, LIGHT, DISC_R } from '../../src/view/index'
import { sheetBody, emptyCtx } from '../app/relationFixture'

const refNodeOf = (d: { nodes: Record<string, { kind: string }> }): string => {
  const found = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref')
  if (found === undefined) throw new Error('no ref node in the folded diagram')
  return found[0]
}

describe('defineRelation — the defined relation renders its argument-order pip', () => {
  it('a ref to the defined ARITY-2 relation draws exactly one pip on its rim', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    const relations = new Map([['R', relation]])
    const folded = applyRelFold(d, sel, 'R', [wY, wZ], relations)
    const ref = refNodeOf(folded)
    const e = mkEngine(folded, [])
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
    expect(folded.nodes[ref]).toMatchObject({ kind: 'ref', defId: 'R', arity: 2 })
  })

  it('a ref to an ARITY-1 relation draws no pip (a single leg needs no order mark)', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'S', 1)
    const e = mkEngine(b.build(), [])
    settle(e, 400)
    const inkDots = paint(e, LIGHT).filter((s) => s.kind === 'dot' && s.fill === LIGHT.ink)
    expect(inkDots).toHaveLength(0)
  })
})
