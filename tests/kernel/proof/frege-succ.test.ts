import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { Definitions } from '../../../src/kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import type { Diagram, NodeId, RegionId, WireId } from '../../../src/kernel/diagram/diagram'

const consts = new Set(['ZERO', 'SUCC'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
}
const ctx: ProofContext = { definitions: defs, theorems: new Map() }

/** The base+closure open pattern shared with zeroIsNat (atoms bound to the stub). */
function baseClPattern() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const bz = b.termNode(stub, p('ZERO'))
  const a0 = b.atom(stub, stub)
  // the zero-line is a BOUNDARY: insertion attaches it to the host's base
  // line, so deiterations of base copies find this base as their justifier
  // with matching attachments
  const w0stub = b.wire(b.root, [
    { node: bz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = b.cut(stub)
  const a1 = b.atom(cut2, stub)
  const ns = b.termNode(cut2, p('SUCC y'))
  b.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ns, port: { kind: 'freeVar', name: 'y' } },
  ])
  const cut3 = b.cut(cut2)
  const a2 = b.atom(cut3, stub)
  b.wire(cut2, [
    { node: ns, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  return { pattern: mkDiagramWithBoundary(b.build(), [w0stub]), stub }
}

/** The open comp "x : R′(x)". */
function rPrimeComp() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const atom = b.atom(stub, stub)
  const bx = b.wire(b.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { comp: mkDiagramWithBoundary(b.build(), [bx]), stub }
}

describe('Frege arithmetic: the successor theorem', () => {
  it('ℕ(n) ∧ m = SUCC n ⟹ m = SUCC n ∧ ℕ(m) replays and checks', () => {
    // ---- lhs: SUCC evidence at root + the general ℕ(n) (separate zero-line)
    const l = new DiagramBuilder()
    const nS = l.termNode(l.root, p('SUCC y'))
    const cut1 = l.cut(l.root)
    const rB = l.bubble(cut1, 1)
    const nz = l.termNode(rB, p('ZERO'))
    const a0 = l.atom(rB, rB)
    // the canonical general ℕ: the base zero-line is ROOT-scoped — the form
    // zeroIsNat derives and theorem composition (oneIsNat) matches against
    const w0 = l.wire(l.root, [
      { node: nz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ])
    const cut2 = l.cut(rB)
    const a1 = l.atom(cut2, rB)
    const ny = l.termNode(cut2, p('SUCC y'))
    l.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ny, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut3 = l.cut(cut2)
    const a2 = l.atom(cut3, rB)
    l.wire(cut2, [
      { node: ny, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const cut4 = l.cut(rB)
    const a3 = l.atom(cut4, rB)
    const wn = l.wire(l.root, [
      { node: nS, port: { kind: 'freeVar', name: 'y' } },
      { node: a3, port: { kind: 'arg', index: 0 } },
    ])
    const wm = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
    const lhsDiagram = l.build()
    const lhs = mkDiagramWithBoundary(lhsDiagram, [wn, wm])

    let cur: Diagram = lhsDiagram
    const steps: ProofStep[] = []
    const push = (s: ProofStep): void => {
      steps.push(s)
      cur = replayProof(cur, [s], ctx)
    }
    const newCutIn = (parent: RegionId, before: Diagram): RegionId =>
      Object.entries(cur.regions).find(
        ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
      )![0]
    const atomsIn = (region: RegionId): [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }][] =>
      Object.entries(cur.nodes).filter(
        (e): e is [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }] =>
          e[1].kind === 'atom' && e[1].region === region,
      )
    const wireOf = (node: NodeId, key: 'arg' | 'output' | 'freeVar'): WireId =>
      Object.entries(cur.wires).find(([, w]) =>
        w.endpoints.some((ep) => ep.node === node && ep.port.kind === key))![0]

    // ---- ℕ-intro skeleton (steps 1–3)
    let snapshot = cur
    push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
    const cO = newCutIn(cur.root, snapshot)
    const cI = newCutIn(cO, snapshot)

    push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
    const rBp = Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'bubble' && lhsDiagram.regions[id] === undefined,
    )![0]

    const { pattern: baseCl, stub: bcStub } = baseClPattern()
    // the inserted base shares the lhs ℕ's base line w0, so base-copy
    // deiterations later find it with matching attachments
    push({ rule: 'insertion', region: rBp, pattern: baseCl, attachments: [w0], binders: { [bcStub]: rBp } })
    // the ambient closure cut inside rB′: its child cut OTHER than cI
    // (vacuousIntro reparented cI into the bubble)
    const cut2p = Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === rBp && id !== cI,
    )![0]

    // ---- induction application (steps 4–8): R′(n) materializes in cI
    snapshot = cur
    push({ rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }), target: cI })
    const cut1c = newCutIn(cI, snapshot)
    const rBc = Object.entries(cur.regions).find(
      ([, r]) => r.kind === 'bubble' && r.parent === cut1c,
    )![0]

    const { comp: xRp, stub: xStub } = rPrimeComp()
    push({ rule: 'comprehensionInstantiate', bubble: rBc, comp: xRp, binders: { [xStub]: rBp } })
    // after dissolution, cut1c holds: ZEROc + its R′-atom (the base copy),
    // the closure copy cut2c, and the conclusion copy cut4c
    const zeroC = Object.entries(cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === cut1c,
    )![0]
    // the copy's base sits ON the shared root-scoped w0 (an attachment, not
    // an internal wire) — its deiteration is justified by the inserted base′
    const baseAtomC = atomsIn(cut1c).find(([id]) => wireOf(id, 'arg') === w0)![0]
    push({
      rule: 'deiteration',
      sel: mkSelection(cur, { region: cut1c, regions: [], nodes: [zeroC, baseAtomC], wires: [] }),
      fuel: 64,
    })

    // the closure copy: the child of cut1c that itself has a child cut
    const cut2c = Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
        Object.values(cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
    )![0]
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })

    push({ rule: 'doubleCutElim', region: cut1c })
    // R′(n): the atom now in cI on the wn line
    const rPrimeN = atomsIn(cI).find(([id]) => wireOf(id, 'arg') === wn)![0]

    // ---- guarded modus ponens (steps 9–14): R′(m) materializes in cI
    snapshot = cur
    push({ rule: 'iteration', sel: mkSelection(cur, { region: rBp, regions: [cut2p], nodes: [], wires: [] }), target: cI })
    const cut2c2 = newCutIn(cI, snapshot)
    const hypAtom = atomsIn(cut2c2)[0]![0]
    const wyC2 = wireOf(hypAtom, 'arg')
    push({ rule: 'wireJoin', a: wn, b: wyC2 })
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [hypAtom], wires: [] }), fuel: 64 })
    const succC2 = Object.entries(cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === cut2c2,
    )![0]
    const wsC2 = wireOf(succC2, 'output')
    push({ rule: 'wireJoin', a: wm, b: wsC2 })
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [succC2], wires: [] }), fuel: 64 })
    push({ rule: 'doubleCutElim', region: cut2c2 })

    // ---- cleanup (steps 15–16)
    push({ rule: 'erasure', sel: mkSelection(cur, { region: cI, regions: [], nodes: [rPrimeN], wires: [] }) })
    push({ rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }) })

    // ---- capture and check
    const rhs = mkDiagramWithBoundary(cur, [wn, wm])
    const thm: Theorem = { name: 'succNat', lhs, rhs, steps }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
    expect(steps).toHaveLength(16)
    // shape sanity: four atoms, all bound to the fresh bubble; the conclusion
    // atom sits on wm together with the SUCC output; wn carries only SUCC's y
    const atoms = Object.entries(rhs.diagram.nodes).filter(([, n]) => n.kind === 'atom')
    expect(atoms).toHaveLength(4)
    for (const [, n] of atoms) {
      expect(n.kind === 'atom' && n.binder).toBe(rBp)
    }
    expect(rhs.diagram.wires[wm]!.endpoints).toHaveLength(2)
    expect(rhs.diagram.wires[wn]!.endpoints).toHaveLength(1)
  })
})
