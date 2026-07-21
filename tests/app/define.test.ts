import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyRelFold, applyRelUnfold } from '../../src/kernel/rules/reldef'
import { verifyTheory } from '../../src/kernel/proof/context'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { emptyDiagram } from '../../src/interaction/edit'
import { defineRelation, canonicalArgOrder, inferFoldArgs } from '../../src/interaction/define'
import { sheetBody, emptyCtx } from './relationFixture'

const refNodeOf = (d: { nodes: Record<string, { kind: string }> }): string => {
  const found = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref')
  if (found === undefined) throw new Error('no ref node in the folded diagram')
  return found[0]
}

describe('defineRelation — the extracted copy round-trips through fold/unfold', () => {
  it('defines a relation whose fold-then-unfold reproduces the original sheet', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    expect(relation.boundary).toHaveLength(2)

    const relations = new Map([['R', relation]])
    const folded = applyRelFold(d, sel, 'R', [wY, wZ], relations)
    const ref = refNodeOf(folded)
    expect(folded.nodes[ref]).toMatchObject({ kind: 'ref', defId: 'R', arity: 2 })

    const unfolded = applyRelUnfold(folded, ref, relations)
    expect(exploreForm(unfolded)).toBe(exploreForm(d))
  })

  it('honors the pick order as the argument order (reversed picks give the reversed boundary)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    // Define with REVERSED picks: arg 0 is the z-line, arg 1 is the y-line.
    const { relation } = defineRelation(d, sel, [wZ, wY], 'R', emptyCtx)
    const relations = new Map([['R', relation]])
    // Folding the same body with the same (reversed) arg order matches.
    expect(() => applyRelFold(d, sel, 'R', [wZ, wY], relations)).not.toThrow()
    // Folding with the sorted order does NOT — proving the boundary honors picks,
    // not the extraction's host-wire-id order.
    expect(() => applyRelFold(d, sel, 'R', [wY, wZ], relations)).toThrow(/does not match relation 'R'/)
  })

  it('does not mutate the input diagram', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const before = JSON.stringify(d)
    defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    expect(JSON.stringify(d)).toBe(before)
  })

  it('leaves the sheet diagram structurally identical — defining is a conservative extension', () => {
    // Byte-identity (above) is the strongest non-mutation pin; this adds the
    // SEMANTIC statement the spec makes ("no diagram changes when a relation is
    // defined"): the canonical form of the sheet is untouched by defining.
    const { d, sel, wY, wZ } = sheetBody()
    const before = exploreForm(d)
    defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    expect(exploreForm(d)).toBe(before)
  })
})

describe('defineRelation — refusals (each message observed)', () => {
  it('refuses an empty name', () => {
    const { d, sel, wY, wZ } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wZ], '', emptyCtx)).toThrow(/name is empty/)
    expect(() => defineRelation(d, sel, [wY, wZ], '   ', emptyCtx)).toThrow(/name is empty/)
  })

  it('refuses a name that collides with an existing relation (ctx.relations)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    const ctx = verifyTheory({ relations: [['R', relation]], theorems: [] })
    expect(() => defineRelation(d, sel, [wY, wZ], 'R', ctx)).toThrow(/relation 'R' already exists/)
  })

  it('refuses a name that collides with a theorem (one namespace)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const empty = mkDiagramWithBoundary(emptyDiagram(), [])
    const thm: Theorem = { name: 'T', lhs: empty, rhs: empty, actions: [] }
    const ctx = verifyTheory({ relations: [], theorems: [thm] })
    expect(() => defineRelation(d, sel, [wY, wZ], 'T', ctx)).toThrow(/already a theorem/)
  })

  it('refuses when a crossing wire is left unpicked', () => {
    const { d, sel, wY } = sheetBody()
    expect(() => defineRelation(d, sel, [wY], 'R', emptyCtx)).toThrow(/was not picked/)
  })

  it('refuses a duplicated pick', () => {
    const { d, sel, wY } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wY], 'R', emptyCtx)).toThrow(/picked more than once/)
  })

  it('refuses a non-crossing (internal) wire picked as an argument', () => {
    const { d, sel, wY, wZ, wOut } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wZ, wOut], 'R', emptyCtx)).toThrow(/is not a crossing wire/)
  })

  it('refuses an open subgraph — a selection that binds atoms outside itself', () => {
    // An atom inside a bubble, bound by that (enclosing) bubble, but the bubble
    // is NOT in the selection: the extracted body would reference a variable it
    // does not bind, so it could never be folded — the same gate abstraction and
    // relFold apply.
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const at = b.atom(bub, bub)
    const d = b.build()
    const sel = mkSelection(d, { region: bub, regions: [], nodes: [at], wires: [] as WireId[] })
    const wArg = Object.keys(d.wires).find((wid) =>
      d.wires[wid]!.endpoints.some((ep) => ep.node === at),
    )!
    expect(() => defineRelation(d, sel, [wArg], 'R', emptyCtx)).toThrow(
      /binds atoms outside itself/,
    )
  })
})

describe('canonicalArgOrder — a deterministic default argument order', () => {
  it('orders the crossing wires by the canonical explorer, stably across identical builds', () => {
    const a = sheetBody()
    const b2 = sheetBody()
    const ordA = canonicalArgOrder(a.d, a.sel)
    const ordB = canonicalArgOrder(b2.d, b2.sel)
    expect(ordA).toHaveLength(2)
    expect(new Set(ordA)).toEqual(new Set([a.wY, a.wZ]))
    // identical constructions get the identical order — the default is a
    // property of the shape, not of iteration accidents
    expect(ordA).toEqual(ordB)
    // and defining with it round-trips like any explicit pick
    const { relation } = defineRelation(a.d, a.sel, ordA, 'C', emptyCtx)
    expect(relation.boundary).toHaveLength(2)
  })

  it('refuses open subgraphs with the self-containment message', () => {
    // an atom whose binder bubble is NOT part of the selection: open subgraph
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const atom = b.atom(bub, bub)
    const d = b.build()
    const sel = mkSelection(d, { region: bub, regions: [], nodes: [atom], wires: [] })
    expect(() => canonicalArgOrder(d, sel)).toThrowError(/binds atoms outside itself/)
  })
})

describe('inferFoldArgs — the fold arguments come from occurrence matching', () => {
  it('infers the attachment order that folds, without any user pick', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    const ctx = verifyTheory({ relations: [['R', relation]], theorems: [] })
    const args = inferFoldArgs(d, sel, 'R', ctx)
    // the body is asymmetric, so exactly one assignment is valid — the pick order
    expect(args).toEqual([wY, wZ])
    // and applying the fold with the inferred args succeeds
    const folded = applyRelFold(d, sel, 'R', args, ctx.relations)
    expect(Object.values(folded.nodes).some((n) => n.kind === 'ref')).toBe(true)
  })

  it('refuses when the selection is not an occurrence of the body', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    // a different, non-matching sheet: a single closed term node
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, parseTerm('\\x. x'))
    const d2 = b.build()
    const sel2 = mkSelection(d2, { region: b.root, regions: [], nodes: [t], wires: [] })
    const ctx = verifyTheory({ relations: [['R', relation]], theorems: [] })
    expect(() => inferFoldArgs(d2, sel2, 'R', ctx)).toThrowError(/not an occurrence of 'R'/)
  })

  it('refuses unknown relations, listing the known ones', () => {
    const { d, sel } = sheetBody()
    expect(() => inferFoldArgs(d, sel, 'nope', emptyCtx)).toThrowError(/unknown relation 'nope'/)
  })
})
