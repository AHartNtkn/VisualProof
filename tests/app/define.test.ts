import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyFold, applyUnfold } from '../../src/kernel/rules/fold'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { relationSig } from '../../src/theories/macros'
import { spawnBoundRelationNode } from '../../src/kernel/diagram/spawn'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { verifyTheory } from '../../src/kernel/proof/context'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { emptyDiagram } from '../../src/app/edit'
import { defineRelation, canonicalArgOrder, inferFoldArgs } from '../../src/app/define'
import { sheetBody, emptyCtx } from './relationFixture'

const refNodeOf = (d: { nodes: Record<string, { kind: string }> }): string => {
  const found = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref')
  if (found === undefined) throw new Error('no ref node in the folded diagram')
  return found[0]
}

const R = (n: number) => relSig(Array.from({ length: n }, () => TERM))
type Rels = ReadonlyMap<string, DiagramWithBoundary>
const foldR = (d: Parameters<typeof applyFold>[0], sel: Parameters<typeof applyFold>[1], name: string, args: readonly string[], relations: Rels) =>
  applyFold(d, sel, args, { defId: name, sig: relationSig(relations.get(name)!), resolve: (id) => relations.get(id) })
const unfoldR = (d: Parameters<typeof applyUnfold>[0], node: string, relations: Rels) =>
  applyUnfold(d, node, (id) => relations.get(id))

describe('defineRelation — the extracted copy round-trips through fold/unfold', () => {
  it('defines a relation whose fold-then-unfold reproduces the original sheet', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx)
    expect(relation.boundary).toHaveLength(2)

    const relations = new Map([['R', relation]])
    const folded = foldR(d, sel, 'R', [wY, wZ], relations)
    const ref = refNodeOf(folded)
    expect(folded.nodes[ref]).toMatchObject({ kind: 'ref', defId: 'R', sig: R(2) })

    const unfolded = unfoldR(folded, ref, relations)
    expect(exploreForm(unfolded)).toBe(exploreForm(d))
  })

  it('honors the pick order as the argument order (reversed picks give the reversed boundary)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    // Define with REVERSED picks: arg 0 is the z-line, arg 1 is the y-line.
    const { relation } = defineRelation(d, sel, [wZ, wY], 'R', emptyCtx)
    const relations = new Map([['R', relation]])
    // Folding the same body with the same (reversed) arg order matches.
    expect(() => foldR(d, sel, 'R', [wZ, wY], relations)).not.toThrow()
    // Folding with the sorted order does NOT — proving the boundary honors picks,
    // not the extraction's host-wire-id order.
    expect(() => foldR(d, sel, 'R', [wY, wZ], relations)).toThrow(/does not match the body/)
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

  it('defines a HIGHER-ORDER relation from a selection whose atom rides an unselected relational wire', () => {
    // The old "open subgraph" refusal has no wire-model successor: an atom whose
    // head wire crosses the selection is a legitimate higher-order boundary
    // argument (the relation takes a relation), not a dangling binder. Every
    // crossing wire — the term arg AND the relational head line — must be picked.
    const b = new DiagramBuilder()
    const W = b.relWire(b.root, R(1))
    const built = b.build()
    const { diagram, node: at } = spawnBoundRelationNode(built, built.root, W)
    const wArg = Object.keys(diagram.wires).find((wid) =>
      diagram.wires[wid]!.endpoints.some((ep) => ep.node === at && ep.port.kind === 'arg'),
    )!
    const sel = mkSelection(diagram, { region: diagram.root, regions: [], nodes: [at], wires: [] as WireId[] })
    const { relation } = defineRelation(diagram, sel, [wArg, W], 'R', emptyCtx)
    expect(relation.boundary).toHaveLength(2)
    // one boundary wire is the higher-order (relational) argument, one is term
    expect(relation.boundary.map((wid) => relation.diagram.wires[wid]!.sig.kind).sort())
      .toEqual(['rel', 'term'])
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

  it('orders the crossing wires of a higher-order selection (relational arg included)', () => {
    // No open-subgraph refusal: a selection whose atom rides an unselected
    // relational wire has that wire as a higher-order crossing argument, so the
    // canonical order simply covers both crossing wires.
    const b = new DiagramBuilder()
    const W = b.relWire(b.root, R(1))
    const built = b.build()
    const { diagram, node: atom } = spawnBoundRelationNode(built, built.root, W)
    const sel = mkSelection(diagram, { region: diagram.root, regions: [], nodes: [atom], wires: [] })
    const ord = canonicalArgOrder(diagram, sel)
    expect(ord).toHaveLength(2)
    expect(new Set(ord)).toEqual(new Set([W, ...ord.filter((w) => w !== W)]))
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
    const folded = foldR(d, sel, 'R', args, ctx.relations)
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
