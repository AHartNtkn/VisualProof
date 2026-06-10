import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('double cut', () => {
  it('intro wraps a selection in two fresh cuts; elim undoes it (fingerprint identity)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const wrapped = applyDoubleCutIntro(d, sel)
    // find the new outer cut: a cut in root whose only child is a cut
    const outer = Object.entries(wrapped.regions).find(([, r]) => r.kind === 'cut' && r.parent === d.root)![0]
    const inner = Object.entries(wrapped.regions).find(([, r]) => r.kind === 'cut' && r.parent === outer)![0]
    const movedNode = Object.values(wrapped.nodes).find((x) => x.region === inner)
    expect(movedNode).toBeDefined()
    // the crossing wire passes through: still scoped at root
    const crossing = Object.values(wrapped.wires).find((w) => w.endpoints.length === 2)
    expect(crossing?.scope).toBe(d.root)
    const unwrapped = applyDoubleCutElim(wrapped, outer)
    expect(diagramFingerprint(unwrapped)).toBe(diagramFingerprint(d))
  })

  it('intro on an empty selection produces a bare double cut', () => {
    const h = new DiagramBuilder()
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [], wires: [] })
    const wrapped = applyDoubleCutIntro(d, sel)
    expect(Object.keys(wrapped.regions)).toHaveLength(3) // root + two cuts
  })

  it('elim rejects non-cuts, annulus content, and multiple children, by name', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const cutA = h.cut(h.root)
    h.cut(cutA) // cutA has a child cut...
    h.termNode(cutA, p('\\x. x')) // ...but also a node in the annulus
    const cutB = h.cut(h.root)
    h.cut(cutB)
    h.cut(cutB) // second child: not a lone double cut
    const cutC = h.cut(h.root)
    h.cut(cutC)
    h.wire(cutC, []) // wire scoped in the annulus
    const cutD = h.cut(h.root)
    h.cut(cutD) // clean double cut for contrast
    const d = h.build()
    expect(() => applyDoubleCutElim(d, bub))
      .toThrowError(new RegExp(`double-cut elimination requires a cut; '${bub}' is a bubble`))
    expect(() => applyDoubleCutElim(d, cutA))
      .toThrowError(new RegExp(`annulus '${cutA}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutB))
      .toThrowError(new RegExp(`annulus '${cutB}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutC))
      .toThrowError(new RegExp(`annulus '${cutC}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutD)).not.toThrow()
  })

  it('elim promotes inner-scoped wires to the outer parent', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const n = h.termNode(inner, p('\\x. x'))
    const w = h.wire(inner, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyDoubleCutElim(d, outer)
    expect(out.wires[w]?.scope).toBe(d.root)
    expect(out.nodes[n]?.region).toBe(d.root)
    expect(out.regions[outer]).toBeUndefined()
    expect(out.regions[inner]).toBeUndefined()
  })

  it('intro_at_nested_region: outer cut is parented to sel.region not root (kills M1)', () => {
    // sel.region is a cut, not the sheet root
    const h = new DiagramBuilder()
    const enclosing = h.cut(h.root)
    const n = h.termNode(enclosing, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: enclosing, regions: [], nodes: [n], wires: [] })
    const wrapped = applyDoubleCutIntro(d, sel)
    // a new cut must be parented directly to enclosing, not to root
    const outer = Object.entries(wrapped.regions).find(([, r]) => r.kind === 'cut' && r.parent === enclosing)
    expect(outer).toBeDefined()
    const newCutsAtRoot = Object.entries(wrapped.regions).filter(
      ([id, r]) => r.kind === 'cut' && r.parent === h.root && id !== enclosing,
    )
    expect(newCutsAtRoot).toHaveLength(0)
  })

  it('elim_nested_in_cut: promotes to enclosing cut not root (kills M2)', () => {
    // double-cut sits inside another cut; contents must go there, not to sheet root
    const h = new DiagramBuilder()
    const enclosing = h.cut(h.root)
    const outer = h.cut(enclosing)
    const inner = h.cut(outer)
    const n = h.termNode(inner, p('\\x. x'))
    const d = h.build()
    const out = applyDoubleCutElim(d, outer)
    expect(out.nodes[n]?.region).toBe(enclosing)
    expect(out.nodes[n]?.region).not.toBe(h.root)
  })

  it('elim_rejects_node_only_in_annulus: arity-0 atom with no wire triggers gate (kills M5)', () => {
    // A bubble encloses the outer cut; an arity-0 atom in the annulus produces no
    // auto-wire, so wiresInOuter=false but nodesInOuter=true — the gate must fire.
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const outer = h.cut(bub)
    h.cut(outer)      // lone child cut — otherwise the test would reject for wrong reason
    h.atom(outer, bub) // arity-0 atom in annulus; no auto-wires created
    const d = h.build()
    expect(() => applyDoubleCutElim(d, outer))
      .toThrowError(new RegExp(`annulus '${outer}' must contain exactly one child cut and nothing else`))
  })

  it('elim_rejects_lone_bubble_child: bubble child is not a cut (kills M6)', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    h.bubble(outer, 0)  // lone child is a bubble, not a cut
    const d = h.build()
    expect(() => applyDoubleCutElim(d, outer))
      .toThrowError(new RegExp(`annulus '${outer}' must contain exactly one child cut and nothing else`))
  })
})
