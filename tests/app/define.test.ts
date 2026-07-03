import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyRelFold, applyRelUnfold } from '../../src/kernel/rules/reldef'
import { mkEngine, settle, paint, LIGHT, DISC_R } from '../../src/view/index'
import type { ProofContext } from '../../src/kernel/proof/step'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { emptyDiagram } from '../../src/app/edit'
import { defineRelation } from '../../src/app/define'
import { sheetBody, emptyCtx } from './relationFixture'

const refNodeOf = (d: { nodes: Record<string, { kind: string }> }): string => {
  const found = Object.entries(d.nodes).find(([, n]) => n.kind === 'ref')
  if (found === undefined) throw new Error('no ref node in the folded diagram')
  return found[0]
}

describe('defineRelation — the extracted copy round-trips through fold/unfold', () => {
  it('defines a relation whose fold-then-unfold reproduces the original sheet', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
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
    const { relation } = defineRelation(d, sel, [wZ, wY], 'R', emptyCtx, {})
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
    defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    expect(JSON.stringify(d)).toBe(before)
  })

  it('leaves the sheet diagram structurally identical — defining is a conservative extension', () => {
    // Byte-identity (above) is the strongest non-mutation pin; this adds the
    // SEMANTIC statement the spec makes ("no diagram changes when a relation is
    // defined"): the canonical form of the sheet is untouched by defining.
    const { d, sel, wY, wZ } = sheetBody()
    const before = exploreForm(d)
    defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    expect(exploreForm(d)).toBe(before)
  })
})

describe('defineRelation — the defined relation renders its argument-order pip', () => {
  // The port-order pip on a disc marks port a0's angle so the argument order of a
  // named relation is READABLE on the sheet. A ref to the defined arity-2 relation
  // must therefore carry exactly one pip; an arity-1 relation's ref carries none
  // (a single leg needs no ordering mark). The pip is the only ink-filled dot in
  // the scene (junction dots are paper/wire), sitting DISC_R from the disc centre.
  it('a ref to the defined ARITY-2 relation draws exactly one pip on its rim', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    const relations = new Map([['R', relation]])
    const folded = applyRelFold(d, sel, 'R', [wY, wZ], relations)
    const ref = refNodeOf(folded)
    const e = mkEngine(folded, [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    // The disc centre is the ref's rendered label centre.
    const label = shapes.find((s) => s.kind === 'label' && s.text === 'R')!
    expect(label.kind === 'label').toBe(true)
    const c = label.kind === 'label' ? label.center : { x: 0, y: 0 }
    const inkDots = shapes.filter((s) => s.kind === 'dot' && s.fill === LIGHT.ink)
    expect(inkDots).toHaveLength(1) // the port-order pip, nothing else
    const pip = inkDots[0]!
    const dist = pip.kind === 'dot' ? Math.hypot(pip.center.x - c.x, pip.center.y - c.y) : 0
    expect(dist).toBeCloseTo(DISC_R, 5) // on the disc rim
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

describe('defineRelation — refusals (each message observed)', () => {
  it('refuses an empty name', () => {
    const { d, sel, wY, wZ } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wZ], '', emptyCtx, {})).toThrow(/name is empty/)
    expect(() => defineRelation(d, sel, [wY, wZ], '   ', emptyCtx, {})).toThrow(/name is empty/)
  })

  it('refuses a name that collides with an existing relation (ctx.relations)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    const ctx: ProofContext = { theorems: new Map(), relations: new Map([['R', relation]]) }
    expect(() => defineRelation(d, sel, [wY, wZ], 'R', ctx, {})).toThrow(/relation 'R' already exists/)
  })

  it('refuses a name that collides with a session relation (the relations record)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const { relation } = defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {})
    expect(() => defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, { R: relation })).toThrow(
      /relation 'R' already exists/,
    )
  })

  it('refuses a name that collides with a theorem (one namespace)', () => {
    const { d, sel, wY, wZ } = sheetBody()
    const empty = mkDiagramWithBoundary(emptyDiagram(), [])
    const thm: Theorem = { name: 'T', lhs: empty, rhs: empty, steps: [] }
    const ctx: ProofContext = { theorems: new Map([['T', thm]]), relations: new Map() }
    expect(() => defineRelation(d, sel, [wY, wZ], 'T', ctx, {})).toThrow(/already a theorem/)
  })

  it('refuses when a crossing wire is left unpicked', () => {
    const { d, sel, wY } = sheetBody()
    expect(() => defineRelation(d, sel, [wY], 'R', emptyCtx, {})).toThrow(/was not picked/)
  })

  it('refuses a duplicated pick', () => {
    const { d, sel, wY } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wY], 'R', emptyCtx, {})).toThrow(/picked more than once/)
  })

  it('refuses a non-crossing (internal) wire picked as an argument', () => {
    const { d, sel, wY, wZ, wOut } = sheetBody()
    expect(() => defineRelation(d, sel, [wY, wZ, wOut], 'R', emptyCtx, {})).toThrow(/is not a crossing wire/)
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
    expect(() => defineRelation(d, sel, [wArg], 'R', emptyCtx, {})).toThrow(
      /binds atoms outside itself/,
    )
  })
})
