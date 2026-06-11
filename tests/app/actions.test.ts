import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { applicableActions } from '../../src/app/actions'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applicableActions', () => {
  it('offers erasure at positive selections and insertion at negative regions', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())

    const pos = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const atPos = applicableActions(d, pos, ctx).map((a) => a.kind)
    expect(atPos).toContain('erase')
    expect(atPos).not.toContain('insert')
    expect(atPos).toContain('doubleCutWrap')
    expect(atPos).toContain('iterate')
    expect(atPos).toContain('vacuousWrap')

    const neg = mkSelection(d, { region: cut, regions: [], nodes: [], wires: [] })
    const atNeg = applicableActions(d, neg, ctx).map((a) => a.kind)
    expect(atNeg).toContain('insert')
    expect(atNeg).not.toContain('erase')
  })

  it('offers double-cut elimination only on empty-annulus cuts', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    h.cut(c1)
    const c3 = h.cut(h.root)
    h.termNode(c3, p('y'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const onClean = applicableActions(d, mkSelection(d, { region: d.root, regions: [c1], nodes: [], wires: [] }), ctx)
    expect(onClean.map((a) => a.kind)).toContain('doubleCutElim')
    const onDirty = applicableActions(d, mkSelection(d, { region: d.root, regions: [c3], nodes: [], wires: [] }), ctx)
    expect(onDirty.map((a) => a.kind)).not.toContain('doubleCutElim')
  })

  it('offers vacuous elimination only on atom-free bubbles, and instantiation only on negative ones', () => {
    const h = new DiagramBuilder()
    const empty = h.bubble(h.root, 1)
    const cut = h.cut(h.root)
    const negBub = h.bubble(cut, 1)
    h.atom(negBub, negBub)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const onEmpty = applicableActions(d, mkSelection(d, { region: d.root, regions: [empty], nodes: [], wires: [] }), ctx).map((a) => a.kind)
    expect(onEmpty).toContain('vacuousElim')
    expect(onEmpty).not.toContain('instantiate')
    const onNeg = applicableActions(d, mkSelection(d, { region: cut, regions: [negBub], nodes: [], wires: [] }), ctx).map((a) => a.kind)
    expect(onNeg).toContain('instantiate')
    expect(onNeg).not.toContain('vacuousElim')
  })

  it('offers theorem citations whose direction matches the selection polarity', () => {
    const consts = new Set(['ZERO'])
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, parseTerm('ZERO', consts))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [nz], wires: [] })
    const cites = applicableActions(d, sel, ctx).filter((a) => a.kind === 'citeTheorem')
    expect(cites.length).toBeGreaterThan(0)
    expect(cites.every((c) => c.kind === 'citeTheorem' && c.direction === 'forward')).toBe(true)
  })

  it('every descriptor carries a human label', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    for (const a of applicableActions(d, sel, ctx)) {
      expect(a.label.length).toBeGreaterThan(0)
    }
  })
})

describe('erase polarity with content', () => {
  it('does not offer erase for content selected at a negative region', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).not.toContain('erase')
  })
})
