import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyRelFold, applyRelUnfold } from '../../src/kernel/rules/reldef'
import type { ProofContext } from '../../src/kernel/proof/step'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { emptyDiagram } from '../../src/app/edit'
import { defineRelation } from '../../src/app/define'

const pc = (s: string) => parseTerm(s)

const emptyCtx: ProofContext = { theorems: new Map(), relations: new Map() }

/**
 * An asymmetric arity-2 body on the sheet: term node `y` in root and term node
 * `z` inside a cut, their outputs joined by one internal wire (kept in the
 * selection). The two crossing wires are `y`'s input (into a positive region)
 * and `z`'s input (into the cut) — structurally distinct, so the boundary ORDER
 * is observable in the canonical fingerprint. Selecting {tA} plus the whole cut
 * subtree gives exactly those two crossing wires.
 */
function sheetBody() {
  const b = new DiagramBuilder()
  const tA = b.termNode(b.root, pc('y'))
  const c1 = b.cut(b.root)
  const tB = b.termNode(c1, pc('z'))
  const wOut = b.wire(b.root, [
    { node: tA, port: { kind: 'output' } },
    { node: tB, port: { kind: 'output' } },
  ])
  const wY = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
  const wZ = b.wire(b.root, [{ node: tB, port: { kind: 'freeVar', name: 'z' } }])
  const d = b.build()
  const sel = mkSelection(d, { region: b.root, regions: [c1], nodes: [tA], wires: [wOut] })
  return { d, sel, wOut, wY, wZ }
}

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
