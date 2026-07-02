import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { mkEngine, settle, paint, LIGHT } from '../../src/view/index'

const p = (s: string) => parseTerm(s)

/** Every numeric field of a shape must be finite (NaN would blow up the canvas). */
function assertFinite(value: unknown): void {
  if (typeof value === 'number') { expect(Number.isFinite(value)).toBe(true); return }
  if (value === null || typeof value !== 'object') return
  for (const v of Object.values(value as Record<string, unknown>)) assertFinite(v)
}

describe('the full pipeline tracks kernel edits', () => {
  it('paints before and after a rule application without carrying any layout across', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d1 = h.build()
    const e1 = mkEngine(d1, [])
    settle(e1, 800)
    expect(paint(e1, LIGHT).length).toBeGreaterThan(0)

    const sel = mkSelection(d1, { region: d1.root, regions: [], nodes: [n], wires: [] })
    const d2 = applyDoubleCutIntro(d1, sel)
    // fresh engine for the edited diagram — layout is never persisted
    const e2 = mkEngine(d2, [])
    settle(e2, 800)
    const cutCircles = paint(e2, LIGHT).filter((s) => s.kind === 'circle' && s.stroke === LIGHT.ink)
    expect(cutCircles).toHaveLength(2) // the two new cuts
    const fills = cutCircles.map((c) => (c.kind === 'circle' ? c.fill : null))
    // outer cut is negative (shade fill), inner cut is positive (paper fill)
    expect(fills.filter((f) => f === LIGHT.negFill)).toHaveLength(1)
    expect(fills.filter((f) => f === LIGHT.paper)).toHaveLength(1)
  })

  it('shapes contain no NaN under extreme aspect terms', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\a. \\b. \\c. \\d. \\e. a (b (c (d e)))'))
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 800)
    for (const shape of paint(e, LIGHT)) assertFinite(shape)
  })
})
