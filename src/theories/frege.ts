import { app, lam, bvar, port, type Term } from '../kernel/term/term'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/context'
import { registerTheorem, verifyTheory } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import { DerivationCursor } from './macros'

// ─── pure Church programs (no term constants: named things are relation nodes) ───
const ZEROp = lam(lam(bvar(0)))                                                // λf x. x
const SUCCp = lam(lam(lam(app(bvar(1), app(app(bvar(2), bvar(1)), bvar(0)))))) // λn f x. f (n f x)
const PLUSp = lam(lam(lam(lam(app(app(bvar(3), bvar(1)), app(app(bvar(2), bvar(1)), bvar(0))))))) // λm n f x. m f (n f x)
const SC = (t: Term): Term => app(SUCCp, t)
const PL = (a: Term, b: Term): Term => app(app(PLUSp, a), b)

// ─── relations: every named arithmetic notion is its own node (ref), whose body
// wires a closed pure-λ program to a use-site by a line of identity ───

/** Zero(x) := x = ⟦λf x. x⟧. */
function zeroRelation(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const z = b.termNode(b.root, ZEROp)
  const wx = b.wire(b.root, [{ node: z, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [wx])
}

/** Succ(n,s) := ∃p. p = ⟦λn f x. f (n f x)⟧ ∧ s = p n. */
function succRelation(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const prog = b.termNode(b.root, SUCCp)
  const use = b.termNode(b.root, app(port('p'), port('n')))
  b.wire(b.root, [{ node: prog, port: { kind: 'output' } }, { node: use, port: { kind: 'freeVar', name: 'p' } }])
  const wn = b.wire(b.root, [{ node: use, port: { kind: 'freeVar', name: 'n' } }])
  const ws = b.wire(b.root, [{ node: use, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [wn, ws])
}

/** Plus(a,b,c) := ∃p. p = ⟦λm n f x. m f (n f x)⟧ ∧ c = p a b. */
function plusRelation(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const prog = b.termNode(b.root, PLUSp)
  const use = b.termNode(b.root, app(app(port('p'), port('a')), port('b')))
  b.wire(b.root, [{ node: prog, port: { kind: 'output' } }, { node: use, port: { kind: 'freeVar', name: 'p' } }])
  const wa = b.wire(b.root, [{ node: use, port: { kind: 'freeVar', name: 'a' } }])
  const wb = b.wire(b.root, [{ node: use, port: { kind: 'freeVar', name: 'b' } }])
  const wc = b.wire(b.root, [{ node: use, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [wa, wb, wc])
}

/**
 * The general ℕ(x) — inCutNat, restated with Zero/Succ REF nodes (no bare λ in
 * the definition). The base line is scoped at the guard bubble rB (NOT the
 * root): the zero-witness lives strictly inside the cut, so ℕ is non-vacuous.
 * The boundary is the x-line, the only wire that leaves the cut.
 */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const zref = l.ref(rB, 'zero', 1)
  const a0 = l.atom(rB, rB)
  // the base zero-line is scoped INSIDE the guard bubble (the non-vacuity fix)
  l.wire(rB, [
    { node: zref, port: { kind: 'arg', index: 0 } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const sref = l.ref(cut2, 'succ', 2)
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: sref, port: { kind: 'arg', index: 0 } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: sref, port: { kind: 'arg', index: 1 } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wx = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(l.build(), [wx])
}

function buildRelations(): Record<string, DiagramWithBoundary> {
  return { zero: zeroRelation(), succ: succRelation(), plus: plusRelation(), nat: natRelation() }
}

const idCert = { leftSteps: [], rightSteps: [] }
const J = (t: Term): string => JSON.stringify(t)

// ─── structural finders and definitional-computation helpers ───

/** The sole term node directly in the root region. */
function soleRootTerm(e: DerivationCursor): NodeId {
  const found = Object.entries(e.cur.nodes).filter(([, n]) => n.kind === 'term' && n.region === e.cur.root)
  if (found.length !== 1) throw new Error(`expected exactly one root term node, found ${found.length}`)
  return found[0]![0]
}

/** The reference node in `region` naming relation `defId`. */
function refBy(e: DerivationCursor, region: RegionId, defId: string): NodeId {
  const found = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'ref' && n.region === region && n.defId === defId)
  if (found === undefined) throw new Error(`no '${defId}' reference node in region '${region}'`)
  return found[0]
}

/** The term node in `region` carrying `t` whose freeVar `name` rides `wire`. */
function nodeOnWire(e: DerivationCursor, region: RegionId, t: Term, name: string, wire: WireId): NodeId {
  const found = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === region && J(n.term) === J(t) &&
      e.cur.wires[wire]!.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === name))
  if (found === undefined) throw new Error(`no '${name}'-on-'${wire}' node carrying the given term in '${region}'`)
  return found[0]
}

/** The wire holding `node`'s arg-`i` endpoint. */
function argWire(e: DerivationCursor, node: NodeId, i: number): WireId {
  const found = Object.entries(e.cur.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'arg' && ep.port.index === i))
  if (found === undefined) throw new Error(`node '${node}' has no arg-${i} endpoint on any wire`)
  return found[0]
}

/**
 * K-trick: mint a node carrying the OPEN term `s` (its frees wired per `attach`)
 * in `region`, off the closed `seed`, restoring the seed after. This remains
 * useful in positive regions where polarity-gated atomic open spawning cannot fire.
 */
function kOpen(e: DerivationCursor, tag: string, seed: NodeId, region: RegionId, s: Term, attach: Record<string, WireId>): NodeId {
  const seedTerm = e.termOf(seed)
  e.pushConv(`${tag} K-expand`, seed, app(lam(seedTerm), s), attach)
  const before = e.cur
  e.push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
  const made = e.newNodeIn(region, before)
  e.pushConv(`${tag} K-restore`, seed, seedTerm)
  return made
}

// The closed induction pair G(x) := `λn. x + (Sn)` —o— `λn. S(x + n)`; U1/U2 are
// the left-shifted β-expanded forms eExtract fissions the IH component out of.
const F1term = lam(PL(port('s0'), SC(bvar(0))))   // λn. x + (S n)
const F2term = lam(SC(PL(port('s0'), bvar(0))))   // λn. S (x + n)
const U1 = lam(SC(app(F1term, bvar(0))))          // λn. S (F1 n)
const U2 = lam(SC(app(F2term, bvar(0))))          // λn. S (F2 n)

/** Left-shift the applied F-form and fission the IH-shaped subterm out, returning it. */
function eExtract(e: DerivationCursor, tag: string, D: NodeId, region: RegionId, isF1: boolean): NodeId {
  e.pushConv(`${tag} left-shift`, D, isF1 ? U1 : U2)
  const before = e.cur
  e.push(`${tag} fission`, { rule: 'fission', node: D, path: ['body', 'arg', 'fn'] })
  return e.newNodeIn(region, before)
}

/** Fold a fused `PLUS x y` node into a plus reference (head-fission then relFold). */
function refoldPlus(e: DerivationCursor, node: NodeId, args: readonly WireId[]): void {
  const region = e.regionOf(node)
  const snap = e.cur
  e.push('refold plus: fission head', { rule: 'fission', node, path: ['fn', 'fn'] })
  const prog = e.newNodeIn(region, snap, PLUSp)
  const internal = e.wireOf(prog, 'output')
  e.push('refold plus: relFold', {
    rule: 'relFold',
    sel: mkSelection(e.cur, { region, regions: [], nodes: [prog, node], wires: [internal] }),
    defId: 'plus', args: [...args],
  })
}

/** Fold a fused `SUCC t` node into a succ reference (head-fission then relFold). */
function refoldSucc(e: DerivationCursor, node: NodeId, args: readonly WireId[]): void {
  const region = e.regionOf(node)
  const snap = e.cur
  e.push('refold succ: fission head', { rule: 'fission', node, path: ['fn'] })
  const prog = e.newNodeIn(region, snap, SUCCp)
  const internal = e.wireOf(prog, 'output')
  e.push('refold succ: relFold', {
    rule: 'relFold',
    sel: mkSelection(e.cur, { region, regions: [], nodes: [prog, node], wires: [internal] }),
    defId: 'succ', args: [...args],
  })
}

/** Build Zero(x) ∧ R(x) ∧ ¬(R(y) ∧ Succ(y,z) ∧ ¬R(z)) using only atomic moves. */
function spawnNatGuard(e: DerivationCursor, region: RegionId): { readonly zero: NodeId; readonly base: NodeId } {
  const zero = e.spawnRelation('guard: spawn zero', region, 'zero')
  const base = e.spawnBoundRelation('guard: spawn base atom', region, region)
  const w0 = argWire(e, zero, 0)
  e.push('guard: join base line', { rule: 'wireJoin', a: w0, b: argWire(e, base, 0) })

  let snap = e.cur
  e.push('guard: introduce closure cuts', {
    rule: 'doubleCutIntro',
    sel: mkSelection(e.cur, { region, regions: [], nodes: [], wires: [] }),
  })
  const outer = e.newCutIn(region, snap)
  const inner = e.newCutIn(outer, snap)

  snap = e.cur
  e.push('guard: iterate antecedent atom', {
    rule: 'iteration',
    sel: mkSelection(e.cur, { region, regions: [], nodes: [base], wires: [] }),
    target: outer,
  })
  const antecedent = Object.entries(e.cur.nodes).find(([id, node]) =>
    node.kind === 'atom' && node.region === outer && snap.nodes[id] === undefined)![0]

  e.push('guard: unfold zero anchor', { rule: 'relUnfold', node: zero })
  const zeroTerm = e.nodeBy(region, ZEROp)
  snap = e.cur
  e.push('guard: split closure variable', {
    rule: 'anchoredWireSplit',
    wire: w0,
    witness: zeroTerm,
    endpoints: [{ node: antecedent, port: { kind: 'arg', index: 0 } }],
    target: outer,
  })
  const localZero = e.newNodeIn(outer, snap, ZEROp)
  const x = e.wireOf(localZero, 'output')
  const succTerm = kOpen(e, 'guard: mint successor', localZero, outer, SC(port('x')), { x })
  const y = e.wireOf(succTerm, 'output')
  refoldSucc(e, succTerm, [x, y])
  e.push('guard: erase local zero anchor', {
    rule: 'erasure',
    sel: mkSelection(e.cur, { region: outer, regions: [], nodes: [localZero], wires: [] }),
  })
  const consequent = e.spawnBoundRelation('guard: spawn consequent atom', inner, region)
  e.push('guard: join consequent line', { rule: 'wireJoin', a: y, b: argWire(e, consequent, 0) })
  e.push('guard: refold zero', {
    rule: 'relFold',
    sel: mkSelection(e.cur, { region, regions: [], nodes: [zeroTerm], wires: [] }),
    defId: 'zero',
    args: [w0],
  })
  return { zero: refBy(e, region, 'zero'), base }
}

// ─── conversion theorems (βη-only: Church PLUS bakes these into normalization) ───

/** plusLeftUnit: Zero(z) ∧ Plus(z,a,o) ⟹ o = a. */
function derivePlusLeftUnit(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const zref = l.ref(l.root, 'zero', 1)
  const pref = l.ref(l.root, 'plus', 3)
  l.wire(l.root, [{ node: zref, port: { kind: 'arg', index: 0 } }, { node: pref, port: { kind: 'arg', index: 0 } }])
  const wa = l.wire(l.root, [{ node: pref, port: { kind: 'arg', index: 1 } }])
  const wo = l.wire(l.root, [{ node: pref, port: { kind: 'arg', index: 2 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wo])
  const e = new DerivationCursor(lhsD, ctx)
  e.push('unfold zero', { rule: 'relUnfold', node: zref })
  e.push('unfold plus', { rule: 'relUnfold', node: pref })
  e.push('fuse plus program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, PLUSp), 'output') })
  e.push('fuse zero', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, ZEROp), 'output') })
  e.pushConv('reduce 0 + a to a', soleRootTerm(e), port('s0'))
  return { name: 'plusLeftUnit', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wo]), actions: [...e.actions] }
}

/** plusRightUnit: Zero(z) ∧ Plus(a,z,o) ⟹ o = a. */
function derivePlusRightUnit(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const zref = l.ref(l.root, 'zero', 1)
  const pref = l.ref(l.root, 'plus', 3)
  const wa = l.wire(l.root, [{ node: pref, port: { kind: 'arg', index: 0 } }])
  l.wire(l.root, [{ node: zref, port: { kind: 'arg', index: 0 } }, { node: pref, port: { kind: 'arg', index: 1 } }])
  const wo = l.wire(l.root, [{ node: pref, port: { kind: 'arg', index: 2 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wo])
  const e = new DerivationCursor(lhsD, ctx)
  e.push('unfold zero', { rule: 'relUnfold', node: zref })
  e.push('unfold plus', { rule: 'relUnfold', node: pref })
  e.push('fuse plus program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, PLUSp), 'output') })
  e.push('fuse zero', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, ZEROp), 'output') })
  e.pushConv('reduce a + 0 to a', soleRootTerm(e), port('s0'))
  return { name: 'plusRightUnit', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wo]), actions: [...e.actions] }
}

/** plusAssoc: Plus(a,b,t) ∧ Plus(t,c,o) ⟹ Plus(b,c,u) ∧ Plus(a,u,o). */
function derivePlusAssoc(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const p1 = l.ref(l.root, 'plus', 3)
  const p2 = l.ref(l.root, 'plus', 3)
  const wa = l.wire(l.root, [{ node: p1, port: { kind: 'arg', index: 0 } }])
  const wb = l.wire(l.root, [{ node: p1, port: { kind: 'arg', index: 1 } }])
  const wt = l.wire(l.root, [{ node: p1, port: { kind: 'arg', index: 2 } }, { node: p2, port: { kind: 'arg', index: 0 } }])
  const wc = l.wire(l.root, [{ node: p2, port: { kind: 'arg', index: 1 } }])
  const wo = l.wire(l.root, [{ node: p2, port: { kind: 'arg', index: 2 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wb, wc, wo])
  const e = new DerivationCursor(lhsD, ctx)
  e.push('unfold p1', { rule: 'relUnfold', node: p1 })
  e.push('unfold p2', { rule: 'relUnfold', node: p2 })
  e.push('fuse t', { rule: 'fusion', wire: wt })
  for (const [id] of Object.entries(e.cur.nodes).filter(([, n]) => n.kind === 'term' && J(n.term) === J(PLUSp))) {
    e.push('fuse plus program', { rule: 'fusion', wire: e.wireOf(id, 'output') })
  }
  const merged = soleRootTerm(e)
  e.pushConv('reassociate', merged, PL(port('s0'), PL(port('s1'), port('s2'))))
  const snap = e.cur
  e.push('fission inner sum', { rule: 'fission', node: merged, path: ['arg'] })
  const inner = e.newNodeIn(e.cur.root, snap, PL(port('s0'), port('s1')))
  const wu = e.wireOf(inner, 'output')
  refoldPlus(e, inner, [wb, wc, wu])
  refoldPlus(e, merged, [wa, wu, wo])
  return { name: 'plusAssoc', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wb, wc, wo]), actions: [...e.actions] }
}

// ─── succShiftS (genuine ℕ-induction on the FIRST addend) ───
//
// The provable shift is `a + (Sn) ~ S(a + n)` guarded by ℕ(a): the successor
// leaves the SECOND addend and the induction runs on the FIRST (Church PLUS
// recurses on its first argument). The closed comprehension pair
// G(x) := `λn. x + (Sn)` —o— `λn. S(x + n)` carries the induction; base and
// closure facts are manufactured at the root (closedTermIntro + congruenceJoin)
// and discharged by deiteration; the G(a) function pair is then applied to the
// boundary and folded back into the relational conclusion.

/**
 * Run the induction on `ref` (a folded ℕ reference) and apply the resulting
 * function pair to the `wn` line, leaving the applied pair A1=`a + (Sn)` —o—
 * A2=`S(a + n)` on a shared output. Returns those node ids and the
 * manufactured-fact ids the caller cleans up.
 */
function runShiftInduction(e: DerivationCursor, ref: NodeId, wn: WireId): {
  A1: NodeId; A2: NodeId; M: NodeId; Mp: NodeId; Z1: NodeId; wM: WireId; wZ: WireId; cutA: RegionId
} {
  let snap = e.cur
  e.push('D0a iterate ref', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [ref], wires: [] }), target: e.cur.root })
  const copyRef = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'ref' && n.defId === 'nat' && id !== ref && snap.nodes[id] === undefined)![0]
  snap = e.cur
  e.push('D0b relUnfold copy', { rule: 'relUnfold', node: copyRef })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  const cb = new DiagramBuilder()
  const g1 = cb.termNode(cb.root, F1term)
  const g2 = cb.termNode(cb.root, F2term)
  const gbx = cb.wire(cb.root, [{ node: g1, port: { kind: 'freeVar', name: 's0' } }, { node: g2, port: { kind: 'freeVar', name: 's0' } }])
  cb.wire(cb.root, [{ node: g1, port: { kind: 'output' } }, { node: g2, port: { kind: 'output' } }])
  e.push('D2 instantiate G', { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [gbx]), attachments: [], binders: [] })

  const zref = refBy(e, cut1c, 'zero')
  e.push('unfold copy zero', { rule: 'relUnfold', node: zref })
  const nzC = e.nodeBy(cut1c, ZEROp)
  const w0C = e.wireOf(nzC, 'output')
  const cut2c = Object.entries(e.cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c && Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id))![0]
  const cut3c = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]
  const sref = refBy(e, cut2c, 'succ')
  e.push('unfold copy succ', { rule: 'relUnfold', node: sref })
  e.push('fuse copy succ program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(cut2c, SUCCp), 'output') })
  const F1_0 = e.nodeBy(cut1c, F1term)
  const F2_0 = e.nodeBy(cut1c, F2term)
  const o0 = e.wireOf(F1_0, 'output')

  // t: transform the closure conjunct into the achievable IH-carrying shape
  const nSc = e.nodeBy(cut2c, SC(port('s0')))
  const F1sc = e.nodeBy(cut3c, F1term)
  const F2sc = e.nodeBy(cut3c, F2term)
  const wsC = e.wireOf(nSc, 'output')
  snap = e.cur
  e.push('t1 iterate nSc', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS2 = e.newNodeIn(cut2c, snap)
  snap = e.cur
  e.push('t1b iterate nSc', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS3 = e.newNodeIn(cut2c, snap)
  e.push('t2 sever wsC', { rule: 'wireSever', wire: wsC, keep: [{ node: nSc, port: { kind: 'output' } }] })
  const ws2 = e.wireOf(nS2, 'output')
  e.push('t3 sever ws2', { rule: 'wireSever', wire: ws2, keep: [{ node: nS2, port: { kind: 'output' } }, { node: F1sc, port: { kind: 'freeVar', name: 's0' } }] })
  const ws3 = e.wireOf(nS3, 'output')
  e.push('t4 fuse nS2->F1sc', { rule: 'fusion', wire: ws2 })
  e.push('t5 fuse nS3->F2sc', { rule: 'fusion', wire: ws3 })
  const E1c = eExtract(e, 't6', F1sc, cut3c, true)
  const E2c = eExtract(e, 't7', F2sc, cut3c, false)
  const F1yc = e.nodeBy(cut2c, F1term)
  const F2yc = e.nodeBy(cut2c, F2term)
  const oyc = e.wireOf(F1yc, 'output')
  snap = e.cur
  e.push('t8 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [F1yc, F2yc], wires: [oyc] }), target: cut3c })
  const H1pc = e.newNodeIn(cut3c, snap, F1term)
  const H2pc = e.newNodeIn(cut3c, snap, F2term)
  e.pushCongruence('t9 cJ E1c=H1pc', E1c, H1pc, idCert)
  e.pushCongruence('t9b cJ E2c=H2pc', E2c, H2pc, idCert)
  e.pushDeiteration('t11 deiterate E1c', mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), 64)
  e.pushDeiteration('t11b deiterate E2c', mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E2c], wires: [] }), 64)

  // b: manufactured root base fact {Z1, M=G(0).F1, Mp=G(0).F2}; deiterate the copy's base
  const M = e.intro('b1 intro G(0).F1', e.cur.root, lam(PL(ZEROp, SC(bvar(0)))))
  snap = e.cur
  e.push('b2 iterate M', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M], wires: [] }), target: e.cur.root })
  const Mp = e.newNodeIn(e.cur.root, snap)
  e.pushConv('b3 convert to G(0).F2', Mp, lam(SC(PL(ZEROp, bvar(0)))))
  snap = e.cur
  e.push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['body', 'fn', 'arg'] })
  const Z1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('b4b fission ZERO out of Mp', { rule: 'fission', node: Mp, path: ['body', 'arg', 'fn', 'arg'] })
  const Z2 = e.newNodeIn(e.cur.root, snap)
  e.pushCongruence('b5 cJ Z1=Z2', Z1, Z2, idCert)
  e.push('b6 erase Z2 dup', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z2], wires: [] }) })
  const wZ = e.wireOf(Z1, 'output')
  e.pushDeiteration('A7 deiterate base conjunct',
    mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC, F1_0, F2_0], wires: [w0C, o0] }), 64)

  // c: manufactured root closure fact; discharge the copy's closure, unwrap
  snap = e.cur
  e.push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = e.newCutIn(e.cur.root, snap)
  const cutB = e.newCutIn(cutA, snap)
  const H1 = e.spawnOpenTerm('c2 spawn IH1', cutA, F1term)
  const H2 = e.spawnOpenTerm('c2b spawn IH2', cutA, F2term)
  const nSucc = e.spawnOpenTerm('c2c spawn SUCC', cutA, SC(port('s0')))
  e.push('c2d join IH arguments', { rule: 'wireJoin', a: e.wireOf(H1, 'freeVar'), b: e.wireOf(H2, 'freeVar') })
  e.push('c2e join SUCC argument', { rule: 'wireJoin', a: e.wireOf(H1, 'freeVar'), b: e.wireOf(nSucc, 'freeVar') })
  e.push('c2f join IH outputs', { rule: 'wireJoin', a: e.wireOf(H1, 'output'), b: e.wireOf(H2, 'output') })
  const wyF = e.wireOf(H1, 'freeVar')
  const ohF = e.wireOf(H1, 'output')
  const seedB = e.intro('c3 intro seedB', cutB, ZEROp)
  const D1 = kOpen(e, 'c4', seedB, cutB, lam(PL(SC(port('a')), SC(bvar(0)))), { a: wyF })
  const D2 = kOpen(e, 'c4b', seedB, cutB, lam(SC(PL(SC(port('a')), bvar(0)))), { a: wyF })
  const E1 = eExtract(e, 'c5', D1, cutB, true)
  const E2 = eExtract(e, 'c5b', D2, cutB, false)
  snap = e.cur
  e.push('c6 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutA, regions: [], nodes: [H1, H2], wires: [ohF] }), target: cutB })
  const H1p = e.newNodeIn(cutB, snap, F1term)
  const H2p = e.newNodeIn(cutB, snap, F2term)
  e.pushCongruence('c7 cJ E1=H1p', E1, H1p, idCert)
  e.pushCongruence('c7b cJ E2=H2p', E2, H2p, idCert)
  e.pushCongruence('c7c cJ D1=D2', D1, D2, idCert)
  e.pushDeiteration('c8 deiterate E1', mkSelection(e.cur, { region: cutB, regions: [], nodes: [E1], wires: [] }), 64)
  e.pushDeiteration('c8b deiterate E2', mkSelection(e.cur, { region: cutB, regions: [], nodes: [E2], wires: [] }), 64)
  e.push('c8c erase seedB', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [seedB], wires: [e.wireOf(seedB, 'output')] }) })
  e.pushDeiteration('A8 deiterate Cl conjunct', mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), 64)
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })

  // e: apply the G(a) function pair to the wn line
  const F1m = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'term' && n.region === e.cur.root && J((n as Extract<typeof n, { kind: 'term' }>).term) === J(F1term) && id !== M)![0]
  const F2m = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'term' && n.region === e.cur.root && J((n as Extract<typeof n, { kind: 'term' }>).term) === J(F2term) && id !== Mp)![0]
  const oG = e.wireOf(F1m, 'output')
  const A1 = kOpen(e, 'e2 A1', Z1, e.cur.root, app(port('f'), port('a')), { f: oG, a: wn })
  const A2 = kOpen(e, 'e2 A2', Z1, e.cur.root, app(port('f'), port('a')), { f: oG, a: wn })
  e.pushCongruence('e2 cJ A1=A2', A1, A2, idCert)
  e.push('e2 sever oG', { rule: 'wireSever', wire: oG, keep: [{ node: F1m, port: { kind: 'output' } }, { node: A1, port: { kind: 'freeVar', name: 's0' } }] })
  e.push('e2 fuse F1m->A1', { rule: 'fusion', wire: oG })
  e.push('e2 fuse F2m->A2', { rule: 'fusion', wire: e.wireOf(F2m, 'output') })
  e.pushConv('e2 convert A1', A1, PL(port('s0'), SC(port('s1'))))
  e.pushConv('e2 convert A2', A2, SC(PL(port('s0'), port('s1'))))
  const wM = e.wireOf(M, 'output')
  return { A1, A2, M, Mp, Z1, wM, wZ, cutA }
}

/**
 * succShiftS: `ℕ(a) ∧ Succ(b,sb) ∧ Plus(a,sb,o) ⟹ ℕ(a) ∧ Plus(a,b,t) ∧ Succ(t,o)`.
 * ℕ(a) is a folded guard on both sides; boundary = [wa, wb, wo], with sb and t
 * internal existentials.
 */
function deriveSuccShiftS(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const rN = l.ref(l.root, 'nat', 1)
  const rS = l.ref(l.root, 'succ', 2)
  const rP = l.ref(l.root, 'plus', 3)
  const wa = l.wire(l.root, [{ node: rN, port: { kind: 'arg', index: 0 } }, { node: rP, port: { kind: 'arg', index: 0 } }])
  const wb = l.wire(l.root, [{ node: rS, port: { kind: 'arg', index: 0 } }])
  const wsb = l.wire(l.root, [{ node: rS, port: { kind: 'arg', index: 1 } }, { node: rP, port: { kind: 'arg', index: 1 } }])
  const wo = l.wire(l.root, [{ node: rP, port: { kind: 'arg', index: 2 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wb, wo])
  const e = new DerivationCursor(lhsD, ctx)

  // bridge: unfold Succ and Plus, fuse to the working o-node `a + (S b)` on wo
  e.push('br unfold succ', { rule: 'relUnfold', node: rS })
  e.push('br fuse succ program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, SUCCp), 'output') })
  e.push('br unfold plus', { rule: 'relUnfold', node: rP })
  e.push('br fuse plus program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, PLUSp), 'output') })
  e.push('br fuse sb', { rule: 'fusion', wire: wsb })
  const oNode = e.nodeBy(e.cur.root, PL(port('s0'), SC(port('s1'))))

  const r = runShiftInduction(e, rN, wb)

  // reconcile: the applied A1 = `a + (S b)` equals the o-node; keep A2 = `S(a + b)`
  e.pushCongruence('rc cJ oNode=A1', oNode, r.A1, idCert)
  e.push('rc erase oNode+A1', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [oNode, r.A1], wires: [] }) })
  // fold A2 = S(a + b) into Plus(a,b,t) ∧ Succ(t,o)
  const snap = e.cur
  e.push('fd fission inner sum', { rule: 'fission', node: r.A2, path: ['arg'] })
  const inner = e.newNodeIn(e.cur.root, snap, PL(port('s0'), port('s1')))
  const wt = e.wireOf(inner, 'output')
  refoldPlus(e, inner, [wa, wb, wt])
  refoldSucc(e, r.A2, [wt, wo])
  e.push('cl erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [r.M, r.Mp, r.Z1], wires: [r.wM, r.wZ] }) })
  e.push('cl erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [r.cutA], nodes: [], wires: [] }) })
  return { name: 'succShiftS', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wb, wo]), actions: [...e.actions] }
}

// ─── plusComm (ℕ-induction on a, citing succShiftS) ───

const PT = PL(port('s0'), port('s1'))

/** Flat parameterized comprehension R(x) := `x + b̂` —o— `b̂ + x`; boundary [x-line, b-param]. */
function buildComp4(): DiagramWithBoundary {
  const cb = new DiagramBuilder()
  const P1 = cb.termNode(cb.root, PT)
  const P2 = cb.termNode(cb.root, PT)
  const wq = cb.wire(cb.root, [{ node: P1, port: { kind: 'freeVar', name: 's0' } }, { node: P2, port: { kind: 'freeVar', name: 's1' } }])
  const wr = cb.wire(cb.root, [{ node: P1, port: { kind: 'freeVar', name: 's1' } }, { node: P2, port: { kind: 'freeVar', name: 's0' } }])
  cb.wire(cb.root, [{ node: P1, port: { kind: 'output' } }, { node: P2, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(cb.build(), [wq, wr])
}

/**
 * plusComm: `ℕ(a) ∧ ℕ(b) ∧ Plus(a,b,o) ⟹ ℕ(a) ∧ ℕ(b) ∧ Plus(b,a,o)`. Both guards
 * stay folded; the induction runs on a with the flat parameterized R(x) above
 * (parameter = the b-line), so R(a) IS the bare commutation pair. The inductive
 * step cites succShiftS forward (for `b + (Sy) ~ S(b + y)` under ℕ(b)), assembled
 * by folding the manufactured `b + (Sy)` node to relational form and unfolding
 * the produced shift back. Boundary = [wa, wb, wo].
 */
function derivePlusComm(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const refA = l.ref(l.root, 'nat', 1)
  const refB = l.ref(l.root, 'nat', 1)
  const refP = l.ref(l.root, 'plus', 3)
  const wa = l.wire(l.root, [{ node: refA, port: { kind: 'arg', index: 0 } }, { node: refP, port: { kind: 'arg', index: 0 } }])
  const wb = l.wire(l.root, [{ node: refB, port: { kind: 'arg', index: 0 } }, { node: refP, port: { kind: 'arg', index: 1 } }])
  const wo = l.wire(l.root, [{ node: refP, port: { kind: 'arg', index: 2 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wb, wo])
  const e = new DerivationCursor(lhsD, ctx)

  // bridge: Plus(a,b,o) → o-node `a + b` on wo
  e.push('br unfold plus', { rule: 'relUnfold', node: refP })
  e.push('br fuse plus program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(e.cur.root, PLUSp), 'output') })

  let snap = e.cur
  e.push('D0a iterate refA', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [refA], wires: [] }), target: e.cur.root })
  const copyRefA = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'ref' && id !== refA && id !== refB && snap.nodes[id] === undefined)![0]
  snap = e.cur
  e.push('D0b relUnfold copyA', { rule: 'relUnfold', node: copyRefA })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  e.push('D2 instantiate R(x):=x+b -o- b+x', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp4(), attachments: [wb], binders: [] })

  const zref = refBy(e, cut1c, 'zero')
  e.push('unfold copy zero', { rule: 'relUnfold', node: zref })
  const nzC = e.nodeBy(cut1c, ZEROp)
  const w0C = e.wireOf(nzC, 'output')
  const cut2c = Object.entries(e.cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c && Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id))![0]
  const cut3c = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]
  const sref = refBy(e, cut2c, 'succ')
  e.push('unfold copy succ', { rule: 'relUnfold', node: sref })
  e.push('fuse copy succ program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(cut2c, SUCCp), 'output') })
  const P1_0 = nodeOnWire(e, cut1c, PT, 's0', w0C)
  const P2_0 = nodeOnWire(e, cut1c, PT, 's1', w0C)
  const o0 = e.wireOf(P1_0, 'output')

  // t: transform the closure conjunct (fuse SUCCs in; left-shift the a-side)
  const nSc = e.nodeBy(cut2c, SC(port('s0')))
  const wyC = e.wireOf(nSc, 'freeVar')
  const wsC = e.wireOf(nSc, 'output')
  const P1y = nodeOnWire(e, cut2c, PT, 's0', wyC)
  const P2y = nodeOnWire(e, cut2c, PT, 's1', wyC)
  const oyC = e.wireOf(P1y, 'output')
  const P1s = nodeOnWire(e, cut3c, PT, 's0', wsC)
  snap = e.cur
  e.push('t1 iterate nSc', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS2 = e.newNodeIn(cut2c, snap)
  snap = e.cur
  e.push('t1b iterate nSc', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS3 = e.newNodeIn(cut2c, snap)
  e.push('t2 sever wsC', { rule: 'wireSever', wire: wsC, keep: [{ node: nSc, port: { kind: 'output' } }] })
  const ws2 = e.wireOf(nS2, 'output')
  e.push('t3 sever ws2', { rule: 'wireSever', wire: ws2, keep: [{ node: nS2, port: { kind: 'output' } }, { node: P1s, port: { kind: 'freeVar', name: 's0' } }] })
  const ws3 = e.wireOf(nS3, 'output')
  e.push('t4 fuse nS2->P1s', { rule: 'fusion', wire: ws2 })
  e.push('t5 fuse nS3->P2s', { rule: 'fusion', wire: ws3 })
  e.pushConv('t6 left-shift P1s', P1s, SC(PT))
  snap = e.cur
  e.push('t6 fission', { rule: 'fission', node: P1s, path: ['arg'] })
  const E1c = e.newNodeIn(cut3c, snap)
  snap = e.cur
  e.push('t8 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [P1y, P2y], wires: [oyC] }), target: cut3c })
  const H1pc = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined)
    .find((id) => e.cur.wires[wyC]!.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === 's0'))!
  e.pushCongruence('t9 cJ E1c=H1pc', E1c, H1pc, idCert)
  e.pushDeiteration('t11 deiterate E1c', mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), 64)

  // b: root base fact `0 + b` —o— `b + 0` (units are pure conversion)
  const Zs = e.intro('b0 intro K-seed', e.cur.root, ZEROp)
  const M = kOpen(e, 'b1 M=0+b', Zs, e.cur.root, PL(ZEROp, port('r')), { r: wb })
  e.push('b1b erase spent seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Zs], wires: [e.wireOf(Zs, 'output')] }) })
  snap = e.cur
  e.push('b2 iterate M', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M], wires: [] }), target: e.cur.root })
  const Mp = e.newNodeIn(e.cur.root, snap)
  e.pushConv('b3 convert to b+0', Mp, PL(port('s0'), ZEROp))
  snap = e.cur
  e.push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['fn', 'arg'] })
  const Z1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('b4b fission ZERO out of Mp', { rule: 'fission', node: Mp, path: ['arg'] })
  const Z2 = e.newNodeIn(e.cur.root, snap)
  e.pushCongruence('b5 cJ Z1=Z2', Z1, Z2, idCert)
  e.push('b6 erase Z2 dup', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z2], wires: [] }) })
  const wZ = e.wireOf(Z1, 'output')
  const wM = e.wireOf(M, 'output')
  e.pushDeiteration('A7 deiterate base conjunct',
    mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC, P1_0, P2_0], wires: [w0C, o0] }), 64)

  // c: root Cl fact; the inductive step cites succShiftS inside cutB
  snap = e.cur
  e.push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = e.newCutIn(e.cur.root, snap)
  const cutB = e.newCutIn(cutA, snap)
  const H1spawn = e.spawnOpenTerm('c2 spawn hyp1', cutA, PT)
  const H2spawn = e.spawnOpenTerm('c2b spawn hyp2', cutA, PT)
  const nSf = e.spawnOpenTerm('c2c spawn SUCC', cutA, SC(port('s0')))
  e.push('c2d join y arguments', { rule: 'wireJoin', a: e.wireOf(H1spawn, 'freeVar', 's0'), b: e.wireOf(H2spawn, 'freeVar', 's1') })
  e.push('c2e join SUCC argument', { rule: 'wireJoin', a: e.wireOf(H1spawn, 'freeVar', 's0'), b: e.wireOf(nSf, 'freeVar') })
  e.push('c2f join hyp outputs', { rule: 'wireJoin', a: e.wireOf(H1spawn, 'output'), b: e.wireOf(H2spawn, 'output') })
  e.push('c2g attach b to hyp1', { rule: 'wireJoin', a: wb, b: e.wireOf(H1spawn, 'freeVar', 's1') })
  e.push('c2h attach b to hyp2', { rule: 'wireJoin', a: wb, b: e.wireOf(H2spawn, 'freeVar', 's0') })
  const wyF = e.wireOf(nSf, 'freeVar')
  const H1 = nodeOnWire(e, cutA, PT, 's0', wyF)
  const H2 = nodeOnWire(e, cutA, PT, 's1', wyF)
  const ohF = e.wireOf(H1, 'output')
  snap = e.cur
  e.push('c3 iterate refB into cutB', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [refB], wires: [] }), target: cutB })
  const refBc = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'ref' && n.region === cutB && snap.nodes[id] === undefined)![0]
  const seedB = e.intro('c3b intro seedB', cutB, ZEROp)
  // manufacture P2sy = `b + (S y)` (baked SUCC) matching the copy's cut3c P2 node
  const P2sy = kOpen(e, 'c4 P2sy', seedB, cutB, PL(port('bb'), SC(port('yy'))), { bb: wb, yy: wyF })
  e.push('c4a erase spent seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [seedB], wires: [e.wireOf(seedB, 'output')] }) })
  const wP = e.wireOf(P2sy, 'output')
  snap = e.cur
  e.push('c4b iterate P2sy', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [P2sy], wires: [] }), target: cutB })
  const P2c = e.newNodeIn(cutB, snap)
  // fold the disposable copy to relational form and cite succShiftS to shift it
  snap = e.cur
  e.push('c4c fission SUCC(y)', { rule: 'fission', node: P2c, path: ['arg'] })
  const sy = e.newNodeIn(cutB, snap, SC(port('s0')))
  const wsy = e.wireOf(sy, 'output')
  refoldSucc(e, sy, [wyF, wsy])         // Succ(y, sy)
  refoldPlus(e, P2c, [wb, wsy, wP])     // Plus(b, sy, wP)
  const succRef = refBy(e, cutB, 'succ')
  const plusRef = refBy(e, cutB, 'plus')
  e.push('c5 cite succShiftS', {
    rule: 'theorem', name: 'succShiftS', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [refBc, succRef, plusRef], wires: [wsy] }), args: [wb, wyF, wP] },
  })
  // unfold the produced Plus(b,y,t) ∧ Succ(t,wP) into A2 = `S(b + y)` on wP
  e.push('c5u unfold succ', { rule: 'relUnfold', node: refBy(e, cutB, 'succ') })
  e.push('c5u fuse succ program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(cutB, SUCCp), 'output') })
  const wt = e.wireOf(e.nodeBy(cutB, SC(port('s0'))), 'freeVar')
  e.push('c5u unfold plus', { rule: 'relUnfold', node: refBy(e, cutB, 'plus') })
  e.push('c5u fuse plus program', { rule: 'fusion', wire: e.wireOf(e.nodeBy(cutB, PLUSp), 'output') })
  e.push('c5u fuse wt', { rule: 'fusion', wire: wt })
  const A2 = e.nodeBy(cutB, SC(PT))
  const natRef2 = refBy(e, cutB, 'nat')

  snap = e.cur
  e.push('c6 fission A2', { rule: 'fission', node: A2, path: ['arg'] })
  const E2 = e.newNodeIn(cutB, snap)
  snap = e.cur
  e.push('c7 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutA, regions: [], nodes: [H1, H2], wires: [ohF] }), target: cutB })
  const H2p = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined)
    .find((id) => e.cur.wires[wyF]!.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === 's1'))!
  e.pushCongruence('c8 cJ E2=H2p', E2, H2p, idCert)
  e.pushDeiteration('c9 deiterate E2', mkSelection(e.cur, { region: cutB, regions: [], nodes: [E2], wires: [] }), 64)
  e.push('c10 erase occurrence leftovers', {
    rule: 'erasure',
    sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [natRef2], wires: [] }),
  })
  e.pushDeiteration('A8 deiterate Cl conjunct', mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), 64)
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })
  e.push('e1 erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M, Mp, Z1], wires: [wM, wZ] }) })
  e.push('e2 erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }) })

  // reconcile the o-node with the R(a) pair; keep P2a = `b + a` on wo, fold to Plus(b,a,o)
  const s0w = (id: NodeId): WireId => e.wireOf(id, 'freeVar', 's0')
  const s1w = (id: NodeId): WireId => e.wireOf(id, 'freeVar', 's1')
  const rootPT = Object.entries(e.cur.nodes)
    .filter(([, n]) => n.kind === 'term' && n.region === e.cur.root && J((n as Extract<typeof n, { kind: 'term' }>).term) === J(PT)).map(([id]) => id)
  const ab = rootPT.filter((id) => s0w(id) === wa && s1w(id) === wb)   // o-node + R(a).P1
  const ba = rootPT.filter((id) => s0w(id) === wb && s1w(id) === wa)   // R(a).P2
  e.pushCongruence('rc cJ ab', ab[0]!, ab[1]!, idCert)
  e.push('rc erase ab', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [ab[0]!, ab[1]!], wires: [] }) })
  refoldPlus(e, ba[0]!, [wb, wa, wo])
  return { name: 'plusComm', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wb, wo]), actions: [...e.actions] }
}

// ─── guard-producing theorems (closed-evidence anchored sharing) ───
//
// natRelation(x) = ¬∃R∃w0[Zero(w0) ∧ R(w0) ∧ Cl(R) ∧ ¬R(x)], the base line w0
// scoped strictly INSIDE the guard bubble (non-vacuity). Producing a concrete
// nat guard requires relating the internal zero witness w0 to the external
// argument line. Anchored splitting duplicates only the available closed zero
// witness for the conclusion endpoint, so the base line and quantifier remain
// in the bubble; contraction then identifies that local duplicate with z.

/**
 * zeroIsNat: the closed sentence `⟹ ∃z. Zero(z) ∧ nat(z)` — from the blank
 * sheet, zero is a natural number. The zero witness is minted as a closed term
 * on an existential z-line (no boundary); the guard body carries the conclusion
 * atom on the internal base line (a tautology built by sound moves), then that
 * endpoint receives a local duplicate of the internal zero witness, then that
 * duplicate contracts onto z by their closed-value equality. The original
 * base line remains scoped in the guard bubble throughout. Boundary [].
 */
function deriveZeroIsNat(ctx: ProofContext): Theorem {
  const lhsD = new DiagramBuilder().build()
  const lhs = mkDiagramWithBoundary(lhsD, [])
  const e = new DerivationCursor(lhsD, ctx)

  // the zero witness: a closed term on a fresh existential z-line
  const zExt = e.intro('intro zero witness', e.cur.root, ZEROp)
  const wz = e.wireOf(zExt, 'output')

  // ¬¬ scaffold; cI becomes the ¬R conclusion cut
  let snap = e.cur
  e.push('dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutO = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === e.cur.root && snap.regions[id] === undefined)![0]
  const cutI = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cutO && snap.regions[id] === undefined)![0]

  // wrap the conclusion cut in the guard bubble (absorbs it — no empty sibling)
  snap = e.cur
  e.push('vbIntro rB', { rule: 'vacuousIntro', sel: mkSelection(e.cur, { region: cutO, regions: [cutI], nodes: [], wires: [] }), arity: 1 })
  const rB = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'bubble' && r.parent === cutO && snap.regions[id] === undefined)![0]

  const guard = spawnNatGuard(e, rB)
  const zrefIn = guard.zero
  const w0 = argWire(e, zrefIn, 0)
  const a0 = guard.base

  // iterate the base R(w0) into the conclusion cut → ¬R(w0) (tautological body)
  snap = e.cur
  e.push('iterate base R into conclusion cut', { rule: 'iteration', sel: mkSelection(e.cur, { region: rB, regions: [], nodes: [a0], wires: [] }), target: cutI })
  const a3 = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'atom' && n.region === cutI && snap.nodes[id] === undefined)![0]

  // unfold the internal zero evidence. Split its conclusion endpoint onto a
  // duplicate available in the guard while retaining w0's base endpoints.
  e.push('unfold internal zero', { rule: 'relUnfold', node: zrefIn })
  const z0 = e.nodeBy(rB, ZEROp)
  snap = e.cur
  e.push('split conclusion from internal zero', {
    rule: 'anchoredWireSplit',
    wire: w0,
    witness: z0,
    endpoints: [{ node: a3, port: { kind: 'arg', index: 0 } }],
    target: rB,
  })
  const localZero = e.newNodeIn(rB, snap, ZEROp)
  e.push('contract conclusion onto external zero', {
    rule: 'anchoredWireContract',
    redundant: localZero,
    survivor: zExt,
    certificate: idCert,
  })

  // refold both retained zeros, then fold the completed guard to nat
  e.push('refold internal zero', { rule: 'relFold', sel: mkSelection(e.cur, { region: rB, regions: [], nodes: [z0], wires: [] }), defId: 'zero', args: [w0] })
  e.push('refold external zero', { rule: 'relFold', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [zExt], wires: [] }), defId: 'zero', args: [wz] })
  e.push('fold nat', { rule: 'relFold', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutO], nodes: [], wires: [] }), defId: 'nat', args: [wz] })

  const rl = new DiagramBuilder()
  const rnat = rl.ref(rl.root, 'nat', 1)
  const rzero = rl.ref(rl.root, 'zero', 1)
  rl.wire(rl.root, [{ node: rnat, port: { kind: 'arg', index: 0 } }, { node: rzero, port: { kind: 'arg', index: 0 } }])
  const rhs = mkDiagramWithBoundary(rl.build(), [])
  return { name: 'zeroIsNat', lhs, rhs, actions: [...e.actions] }
}

/**
 * succNat: `nat(n) ∧ Succ(n,s) ⟹ Succ(n,s) ∧ nat(s)`. The base is INHERITED
 * from nat(n), never created, so no external-line identification is needed and
 * transport is not used here (the wall of UPDATE 10 only bit the base-creating
 * theorems). Build a fresh nat(s) guard skeleton, iterate nat(n) into its
 * conclusion cut and instantiate its R with the skeleton's R (second-order
 * modus ponens), bridge the two bubble-scoped zero witnesses with wireJoin
 * (both internal — the merge keeps the outer bubble scope, so non-vacuity
 * holds), deiterate the copy's base and closure to leave R(n), then run a
 * guarded modus ponens: R(n) ∧ Cl(R) ∧ Succ(n,s) ⟹ R(s), contradicting the
 * conclusion. Fold to nat(s); the input nat(n) is consumed. Boundary [wn, ws].
 */
function deriveSuccNat(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const rN = l.ref(l.root, 'nat', 1)
  const rS = l.ref(l.root, 'succ', 2)
  const wn = l.wire(l.root, [{ node: rN, port: { kind: 'arg', index: 0 } }, { node: rS, port: { kind: 'arg', index: 0 } }])
  const ws = l.wire(l.root, [{ node: rS, port: { kind: 'arg', index: 1 } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wn, ws])
  const e = new DerivationCursor(lhsD, ctx)

  // Phase A: fresh nat(s) guard skeleton (¬¬ scaffold, guard bubble, base+closure)
  let snap = e.cur
  e.push('dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cO = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === e.cur.root && snap.regions[id] === undefined)![0]
  const cI = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cO && snap.regions[id] === undefined)![0]
  snap = e.cur
  e.push('vbIntro rB', { rule: 'vacuousIntro', sel: mkSelection(e.cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
  const rBp = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'bubble' && r.parent === cO && snap.regions[id] === undefined)![0]

  spawnNatGuard(e, rBp)

  // Phase B: iterate nat(n) into cI, instantiate its R with the skeleton's R,
  // bridge the zero witnesses, deiterate base + closure, dcElim → R(n) in cI
  snap = e.cur
  e.push('iterate nat(n) into cI', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [rN], wires: [] }), target: cI })
  const copyRef = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'ref' && n.defId === 'nat' && id !== rN && snap.nodes[id] === undefined)![0]
  e.push('unfold copy', { rule: 'relUnfold', node: copyRef })
  const cut1c = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cI && snap.regions[id] === undefined)![0]
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  const cb = new DiagramBuilder()
  const cstub = cb.bubble(cb.root, 1)
  const catom = cb.atom(cstub, cstub)
  const cbx = cb.wire(cb.root, [{ node: catom, port: { kind: 'arg', index: 0 } }])
  e.push("instantiate R'=R", { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [cbx]), attachments: [], binders: [[cstub, rBp]] })

  const skZero = refBy(e, rBp, 'zero')
  const w0s = argWire(e, skZero, 0)
  const cpZero = refBy(e, cut1c, 'zero')
  const cpAtom = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'atom' && n.region === cut1c)![0]
  const cpClosure = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cut1c && Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id))![0]
  e.push('bridge base lines', { rule: 'wireJoin', a: w0s, b: argWire(e, cpZero, 0) })
  e.pushDeiteration('deiterate copy base', mkSelection(e.cur, { region: cut1c, regions: [], nodes: [cpZero, cpAtom], wires: [] }), 64)
  e.pushDeiteration('deiterate copy closure', mkSelection(e.cur, { region: cut1c, regions: [cpClosure], nodes: [], wires: [] }), 64)
  e.push('dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })
  const rNn = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'atom' && n.region === cI)![0]

  // Phase C: guarded modus ponens — R(n) ∧ Cl(R) ∧ Succ(n,s) ⟹ R(s) in cI
  const skClosure = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === rBp && id !== cI)![0]
  snap = e.cur
  e.push('iterate closure into cI', { rule: 'iteration', sel: mkSelection(e.cur, { region: rBp, regions: [skClosure], nodes: [], wires: [] }), target: cI })
  const cut2c2 = Object.entries(e.cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cI && snap.regions[id] === undefined)![0]
  const succCopy = refBy(e, cut2c2, 'succ')
  const mLine = argWire(e, succCopy, 0)
  const rmAtom = e.cur.wires[mLine]!.endpoints.find((ep) => ep.node !== succCopy)!.node
  e.push('bind m=n', { rule: 'wireJoin', a: wn, b: mLine })
  e.pushDeiteration('deiterate R(m) against R(n)', mkSelection(e.cur, { region: cut2c2, regions: [], nodes: [rmAtom], wires: [] }), 64)
  e.push('bind t=s', { rule: 'wireJoin', a: ws, b: argWire(e, succCopy, 1) })
  e.pushDeiteration('deiterate Succ(n,s) against hypothesis', mkSelection(e.cur, { region: cut2c2, regions: [], nodes: [succCopy], wires: [] }), 64)
  e.push('dcElim closure copy', { rule: 'doubleCutElim', region: cut2c2 })
  e.push('erase R(n)', { rule: 'erasure', sel: mkSelection(e.cur, { region: cI, regions: [], nodes: [rNn], wires: [] }) })

  // Phase D: fold the guard to nat(s); consume nat(n)
  e.push('fold nat(s)', { rule: 'relFold', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cO], nodes: [], wires: [] }), defId: 'nat', args: [ws] })
  e.push('erase nat(n)', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [rN], wires: [] }) })

  const rl = new DiagramBuilder()
  const rSuc = rl.ref(rl.root, 'succ', 2)
  const rNat = rl.ref(rl.root, 'nat', 1)
  const rwn = rl.wire(rl.root, [{ node: rSuc, port: { kind: 'arg', index: 0 } }])
  const rws = rl.wire(rl.root, [{ node: rSuc, port: { kind: 'arg', index: 1 } }, { node: rNat, port: { kind: 'arg', index: 0 } }])
  const rhs = mkDiagramWithBoundary(rl.build(), [rwn, rws])
  return { name: 'succNat', lhs, rhs, actions: [...e.actions] }
}

/**
 * oneIsNat: the closed sentence `⟹ ∃z,s. Zero(z) ∧ Succ(z,s) ∧ nat(s)` — the
 * successor of zero is a natural number. Cite the closed zeroIsNat to plant
 * Zero(z) ∧ nat(z) on a fresh existential z-line, mint Succ(z,s) onto that
 * line, then cite the rule-shaped succNat to carry nat(z) ∧ Succ(z,s) to
 * nat(s). This certifies concrete nat(1). Boundary [].
 */
function deriveOneIsNat(ctx: ProofContext): Theorem {
  const lhsD = new DiagramBuilder().build()
  const lhs = mkDiagramWithBoundary(lhsD, [])
  const e = new DerivationCursor(lhsD, ctx)

  // plant Zero(z) ∧ nat(z) on a fresh existential z-line
  e.push('cite zeroIsNat', {
    rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }), args: [] },
  })
  const zRef = refBy(e, e.cur.root, 'zero')
  const natZ = refBy(e, e.cur.root, 'nat')
  const wz = argWire(e, zRef, 0)

  // mint Succ(z,s) on the z-line (K-trick a `SUCC z` node off a spent seed, then refold)
  const seed = e.intro('intro succ seed', e.cur.root, ZEROp)
  const sNode = kOpen(e, 'mint SUCC z', seed, e.cur.root, SC(port('z')), { z: wz })
  e.push('erase succ seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [seed], wires: [e.wireOf(seed, 'output')] }) })
  const ws = e.wireOf(sNode, 'output')
  refoldSucc(e, sNode, [wz, ws])
  const sRef = refBy(e, e.cur.root, 'succ')

  // carry nat(z) ∧ Succ(z,s) to nat(s) by the rule-shaped succNat
  e.push('cite succNat', {
    rule: 'theorem', name: 'succNat', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [natZ, sRef], wires: [] }), args: [wz, ws] },
  })

  const rl = new DiagramBuilder()
  const rZero = rl.ref(rl.root, 'zero', 1)
  const rSuc = rl.ref(rl.root, 'succ', 2)
  const rNat = rl.ref(rl.root, 'nat', 1)
  rl.wire(rl.root, [{ node: rZero, port: { kind: 'arg', index: 0 } }, { node: rSuc, port: { kind: 'arg', index: 0 } }])
  rl.wire(rl.root, [{ node: rSuc, port: { kind: 'arg', index: 1 } }, { node: rNat, port: { kind: 'arg', index: 0 } }])
  const rhs = mkDiagramWithBoundary(rl.build(), [])
  return { name: 'oneIsNat', lhs, rhs, actions: [...e.actions] }
}

export function buildFregeTheory(): Theory {
  const relations = buildRelations()
  const ctx = verifyTheory({ relations, theorems: [] })
  // Map insertion order is dependency order. zeroIsNat and succNat must precede
  // oneIsNat (which cites both); succShiftS must precede plusComm.
  const zeroIsNat = deriveZeroIsNat(ctx)
  const succNat = deriveSuccNat(ctx)
  const oneIsNat = deriveOneIsNat(registerTheorem(registerTheorem(ctx, zeroIsNat), succNat))
  const theorems: Theorem[] = [
    derivePlusAssoc(ctx),
    derivePlusLeftUnit(ctx),
    derivePlusRightUnit(ctx),
    zeroIsNat,
    succNat,
    oneIsNat,
  ]
  const succShiftS = deriveSuccShiftS(ctx)
  theorems.push(succShiftS)
  const ctxWithSucc = registerTheorem(ctx, succShiftS)
  theorems.push(derivePlusComm(ctxWithSucc))
  return { relations, theorems }
}
