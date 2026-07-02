import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { applicableActions } from '../../src/app/actions'
import { applyConversion } from '../../src/kernel/rules/conversion'
import { applyStep } from '../../src/kernel/proof/step'

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

describe('double-cut elimination annulus content', () => {
  it('is not offered when the annulus holds a node beside the inner cut... or anything at all', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    h.cut(outer)
    h.termNode(outer, p('y')) // annulus polluted but children.length is still 1
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [outer], nodes: [], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).not.toContain('doubleCutElim')
  })
})

describe('reference-node gates', () => {
  const refHost = (defId: string) => {
    const b = new DiagramBuilder()
    const ref = b.ref(b.root, defId, 1)
    const carrier = b.termNode(b.root, p('y'))
    b.wire(b.root, [
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'y' } },
    ])
    return { d: b.build(), ref }
  }

  it('a ref node is not convertible, unfolds when its relation is in scope, and joins selection-based actions', () => {
    const { d, ref } = refHost('nat') // buildFregeTheory carries the 'nat' relation
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [ref], wires: [] })
    const kinds = applicableActions(d, sel, ctx).map((a) => a.kind)
    expect(kinds).not.toContain('convert') // refs are not term nodes
    expect(kinds).toContain('relUnfold')
    expect(kinds).toContain('doubleCutWrap') // selection-based actions still flow through
    expect(kinds).toContain('iterate')
  })

  it('does not offer relUnfold when the referenced relation is not in scope', () => {
    const { d, ref } = refHost('ghost')
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [ref], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).not.toContain('relUnfold')
  })

  it('offers relFold on a content selection when a relation exists, and not otherwise', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const withRel = verifyTheory(buildFregeTheory())
    expect(applicableActions(d, sel, withRel).map((a) => a.kind)).toContain('relFold')
    const noRel = verifyTheory({ definitions: {}, relations: {}, theorems: [] })
    expect(applicableActions(d, sel, noRel).map((a) => a.kind)).not.toContain('relFold')
  })
})

describe('descriptor → step construction (the shell contract)', () => {
  it('insert: an enumerated insert commits as the shell builds it', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).toContain('insert')
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. \\y. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const out = applyStep(d, { rule: 'insertion', region: cut, pattern, attachments: [], binders: {} }, ctx)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })

  it('convert: an enumerated convert commits via the certificate path', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\a. a) y'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).toContain('convert')
    // the node's source free 'y' is canonical s0 after construction
    const target = p('s0')
    const pre = applyConversion(d, n, target, 32)
    const out = applyStep(d, { rule: 'conversion', node: n, term: target, certificate: pre.certificate, attachments: {} }, ctx)
    expect(JSON.stringify(out.nodes[n])).toContain('"port"')
  })

  it('relUnfold: an enumerated unfold commits via applyStep against ctx.relations', () => {
    const b = new DiagramBuilder()
    const ref = b.ref(b.root, 'nat', 1)
    const carrier = b.termNode(b.root, p('y'))
    b.wire(b.root, [
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = b.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [ref], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).toContain('relUnfold')
    const out = applyStep(d, { rule: 'relUnfold', node: ref }, ctx)
    // the reference is gone and the nat body has been inlined
    expect(Object.values(out.nodes).some((n) => n.kind === 'ref')).toBe(false)
    expect(Object.keys(out.nodes).length).toBeGreaterThan(Object.keys(d.nodes).length)
  })
})
