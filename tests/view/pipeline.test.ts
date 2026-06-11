import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildScene, initialState, settle, renderScene, DEFAULT_PARAMS } from '../../src/view/index'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('the full pipeline tracks kernel edits', () => {
  it('renders before and after a rule application without carrying any state across', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d1 = h.build()
    const s1 = settle(d1, initialState(d1), DEFAULT_PARAMS, 20000)
    const shapes1 = renderScene(buildScene(d1, s1.positions))
    expect(shapes1.length).toBeGreaterThan(0)

    const sel = mkSelection(d1, { region: d1.root, regions: [], nodes: [n], wires: [] })
    const d2 = applyDoubleCutIntro(d1, sel)
    // fresh physics for the edited diagram — layout is never persisted
    const s2 = settle(d2, initialState(d2), DEFAULT_PARAMS, 20000)
    const shapes2 = renderScene(buildScene(d2, s2.positions))
    const circles2 = shapes2.filter((s) => s.kind === 'circle')
    expect(circles2).toHaveLength(2) // the two new cuts
    // outer cut is negative (shade fill), inner cut is positive (background fill)
    const fills = circles2.map((c) => (c.kind === 'circle' ? c.fill : undefined))
    expect(fills.filter((f) => f !== undefined && f.startsWith('rgba'))).toHaveLength(1)
    expect(fills.filter((f) => f === '#fafaf7')).toHaveLength(1)
  })

  it('scenes contain no NaN under extreme aspect terms', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\a. \\b. \\c. \\d. \\e. a (b (c (d e)))'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    for (const shape of renderScene(buildScene(d, s.positions))) {
      expect(JSON.stringify(shape)).not.toContain('null') // NaN serializes to null
    }
  })
})
