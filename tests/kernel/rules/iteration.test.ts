import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'
import { applyAction, type ProofAction } from '../../../src/kernel/proof/action'
import type { ProofContext } from '../../../src/kernel/proof/step'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

/** Host: node `y` at root wired to a hub, plus an empty cut to iterate into. */
function host() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('y'))
  const hub = h.termNode(h.root, p('\\x. x'))
  const w = h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: hub, port: { kind: 'output' } },
  ])
  const cut = h.cut(h.root)
  return { d: h.build(), n, hub, w, cut }
}

describe('applyIteration', () => {
  it('copies a subgraph into a descendant region, sharing attachments', () => {
    const { d, n, w, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, cut)
    // the attachment wire gained the copy's endpoint
    expect(out.wires[w]?.endpoints).toHaveLength(3)
    const copies = Object.values(out.nodes).filter((x) => x.region === cut)
    expect(copies).toHaveLength(1)
  })

  it('permits iteration into the same region', () => {
    const { d, n, w } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, d.root)
    expect(out.wires[w]?.endpoints).toHaveLength(3)
  })

  it('threads action reservations into the nested splice allocator', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    builder.termNode(cut, p('\\x. x'))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [cut], nodes: [], wires: [],
    })
    const action = {
      label: 'reserved iteration',
      steps: [{ rule: 'iteration' as const, sel: selection, target: diagram.root }],
      placements: [],
      allocation: { regions: [`${cut}_0`], nodes: ['n0_0'], wires: ['w0_0'] },
    } as ProofAction & { readonly allocation: {
      readonly regions: readonly string[]
      readonly nodes: readonly string[]
      readonly wires: readonly string[]
    } }

    const out = applyAction(diagram, action, ctx)

    expect(out.regions[`${cut}_1`]).toBeDefined()
    expect(out.nodes['n0_1']).toBeDefined()
    expect(out.wires['w0_1']).toBeDefined()
  })

  it('rejects targets outside the source region and targets inside the copy', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const inner = h.cut(cutA)
    const cutB = h.cut(h.root)
    const n = h.termNode(cutA, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cutA, regions: [inner], nodes: [n], wires: [] })
    expect(() => applyIteration(d, sel, cutB))
      .toThrowError(/iteration target 'r3' must lie within the source region 'r1'/)
    expect(() => applyIteration(d, sel, inner))
      .toThrowError(/iteration target 'r2' lies inside the iterated subgraph/)
  })
})

describe('applyDeiteration', () => {
  it('iterate then deiterate is the identity (fingerprint)', () => {
    const { d, n, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    // the copy is the unique node in the cut
    const copyId = Object.entries(iterated.nodes).find(([, x]) => x.region === cut)![0]
    const copySel = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    const back = applyDeiteration(iterated, copySel, 100)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('rejects removal of an unjustified subgraph, by name', () => {
    const { d, n } = host()
    // the original has no second copy anywhere: deiterating it is unjustified
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence found for deiteration at 'r0'/)
  })

  it('rejects justification from a strict descendant: iteration only copies inward', () => {
    // a (root) and b (inside a cut) share BOTH wires — b would justify a if
    // the ancestor direction were ignored, which is the unsound direction
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y'))
    const cut = h.cut(h.root)
    const b = h.termNode(cut, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence/)
  })

  it('a copy cannot justify itself, and separate wires are not shared attachments', () => {
    // ONE closed node: the matcher finds the node itself, but a copy cannot
    // justify its own removal
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence/)
    // TWO separately built identical nodes have DISTINCT output wires:
    // ∃x.P(x) ∧ ∃y.P(y) → ∃x.P(x) is erasure, not deiteration — refuse
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    h2.termNode(h2.root, p('\\x. x'))
    const d2 = h2.build()
    const sel2 = mkSelection(d2, { region: d2.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d2, sel2, 100))
      .toThrowError(/no justifying occurrence/)
  })

  it('attachment-SHARING duplicates deiterate: ∃x.(P(x)∧P(x)) → ∃x.P(x)', () => {
    // two `y` nodes sharing BOTH their y-wire and their output wire
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y'))
    const b = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [b], wires: [] })
    const out = applyDeiteration(d, sel, 100)
    expect(Object.keys(out.nodes)).toHaveLength(1)
    expect(out.nodes[a]).toBeDefined()
  })

  it('refuses removal justified only by an ISOMORPHIC occurrence under a DIFFERENT binder', () => {
    // Host: ∃x. [∃S. S(x)] ∧ [∃R. ¬R(x)]. The selection is the R-application
    // under the cut (an OPEN selection: R = rB binds it from outside). The
    // only structural match of its stub pattern ∃?.?(x) is the rD bubble —
    // a DIFFERENT relation variable. Binder identity matching makes the decoy
    // a non-match (open binders map stubs to specific host bubbles), so the
    // removal fails as unjustified.
    const h = new DiagramBuilder()
    const rD = h.bubble(h.root, 1)
    const aJ = h.atom(rD, rD)
    const rB = h.bubble(h.root, 1)
    const c1 = h.cut(rB)
    const aT = h.atom(c1, rB)
    h.wire(h.root, [
      { node: aJ, port: { kind: 'arg', index: 0 } },
      { node: aT, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: c1, regions: [], nodes: [aT], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence/)
  })

  it('mentions undecided pairs in the failure when fuel ran out', () => {
    // copy and candidate original are both non-normalizing and structurally
    // different — comparison exhausts fuel, so the failure must say so
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    h.termNode(h.root, p('(\\x. x x x) (\\x. x x x)'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d, sel, 25))
      .toThrowError(/undecided under fuel 25/)
  })
})
