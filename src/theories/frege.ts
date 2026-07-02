import { parseTerm } from '../kernel/term/parse'
import { app, lam, bvar, port, type Term } from '../kernel/term/term'
import type { PathSeg } from '../kernel/term/reduce'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { Definitions } from '../kernel/rules/definitions'
import { applyConversion } from '../kernel/rules/conversion'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import { DerivationCursor } from './macros'

const idCert = { leftSteps: [], rightSteps: [] }

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const fregeDefinitions: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}

/**
 * The general ℕ(x) — inCutNat. The base line w0 is scoped at the guard bubble
 * rB (NOT the root): the zero-witness lives strictly inside the cut, so ℕ is
 * non-vacuous (∃w0 is not witnessable outside the guard by a non-zero). The
 * boundary is the x-line, the only wire that leaves the cut.
 */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the base zero-line is scoped INSIDE the guard bubble (the non-vacuity fix)
  l.wire(rB, [
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
  const wx = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(l.build(), [wx])
}

const PLUS_BODY = fregeDefinitions['PLUS']!

/**
 * A conversion (βη-only) theorem `o = start ⟹ o = target-refolded`, on a single
 * root term node whose output and free ports are the boundary. The recipe uses
 * canonical port names (s0, s1, …), which mkDiagram's name canonicalization
 * leaves fixed in first-occurrence order. Constants are opaque to β, so we
 * unfold before converting to the constant-free target, then refold. Built once
 * at load time; the recorded certificate makes replay fuel-free.
 */
type ConversionRecipe = {
  readonly name: string
  readonly start: string
  readonly freeVars: readonly string[]
  readonly unfolds: readonly (readonly PathSeg[])[]
  readonly target: Term
  readonly folds: readonly { readonly path: readonly PathSeg[]; readonly constId: string }[]
}

function deriveConversion(r: ConversionRecipe, ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p(r.start))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const wf = r.freeVars.map((v) => l.wire(l.root, [{ node: n, port: { kind: 'freeVar', name: v } }]))
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo, ...wf])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  for (const path of r.unfolds) push({ rule: 'unfold', node: n, path: [...path] })
  const conv = applyConversion(cur, n, r.target, 4096)
  push({ rule: 'conversion', node: n, term: r.target, certificate: conv.certificate, attachments: {} })
  for (const f of r.folds) push({ rule: 'fold', node: n, path: [...f.path], constId: f.constId })
  return { name: r.name, lhs, rhs: mkDiagramWithBoundary(cur, [wo, ...wf]), steps }
}

const conversionRecipes: readonly ConversionRecipe[] = [
  {
    name: 'plusAssoc',
    start: 'PLUS (PLUS s0 s1) s2',
    freeVars: ['s0', 's1', 's2'],
    unfolds: [['fn', 'fn'], ['fn', 'arg', 'fn', 'fn']],
    // the constant-free unfolded form of PLUS s0 (PLUS s1 s2)
    target: app(app(PLUS_BODY, port('s0')), app(app(PLUS_BODY, port('s1')), port('s2'))),
    folds: [{ path: ['arg', 'fn', 'fn'], constId: 'PLUS' }, { path: ['fn', 'fn'], constId: 'PLUS' }],
  },
  {
    name: 'plusLeftUnit',
    start: 'PLUS ZERO s0',
    freeVars: ['s0'],
    unfolds: [['fn', 'fn'], ['fn', 'arg']],
    target: port('s0'),
    folds: [],
  },
  {
    name: 'plusRightUnit',
    start: 'PLUS s0 ZERO',
    freeVars: ['s0'],
    unfolds: [['fn', 'fn'], ['arg']],
    target: port('s0'),
    folds: [],
  },
]

// ─── succShiftS (genuine ℕ-induction: PLUS m (SUCC n) ~ SUCC (PLUS m n)) ───
//
// Ported from the verified spike4/succshift4 trace, adapted to the FOLDED ℕ
// guard: the lhs carries a `nat` reference, and a D0 prelude (iterate the ref,
// relUnfold the working copy) opens the guard while the ambient reference stays
// folded into the rhs. The induction runs on the closed comprehension pair
// G(x) := `\n. PLUS x (SUCC n)` —o— `\n. SUCC (PLUS x n)`; base and closure
// facts are manufactured at the root (closedTermIntro + congruenceJoin) and
// discharged by deiteration; congruenceJoin carries the IH transport.

const SUCC_BODY = fregeDefinitions['SUCC']!
const ZERO_BODY = fregeDefinitions['ZERO']!
const F1term = p('\\n. PLUS s0 (SUCC n)')
const F2term = p('\\n. SUCC (PLUS s0 n)')
// left-shifted unfolded forms used by eExtract to fission out the IH subterm
const U1 = lam(app(SUCC_BODY, app(lam(app(app(PLUS_BODY, port('s0')), app(SUCC_BODY, bvar(0)))), bvar(0))))
const U2 = lam(app(SUCC_BODY, app(lam(app(SUCC_BODY, app(app(PLUS_BODY, port('s0')), bvar(0)))), bvar(0))))
const J = (t: Term) => JSON.stringify(t)

/** K-trick: mint a node carrying the OPEN term `s` (its frees wired per
 *  `attach`) in `region`, off the closed `seed`, restoring the seed after. */
function kOpen(
  e: DerivationCursor, tag: string, seed: NodeId, region: RegionId, s: Term, attach: Record<string, WireId>,
): NodeId {
  const seedTerm = e.termOf(seed)
  e.pushConv(`${tag} K-expand`, seed, app(lam(seedTerm), s), attach)
  const before = e.cur
  e.push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
  const made = e.newNodeIn(region, before)
  e.pushConv(`${tag} K-restore`, seed, seedTerm)
  return made
}

/** Unfold the applied F-form, left-shift, fission out the IH-shaped subterm,
 *  refold — extracting a node βη-equal to the inductive hypothesis component. */
function eExtract(e: DerivationCursor, tag: string, D: NodeId, region: RegionId, isF1: boolean): NodeId {
  if (isF1) {
    e.push(`${tag} unfold PLUS`, { rule: 'unfold', node: D, path: ['body', 'fn', 'fn'] })
    e.push(`${tag} unfold SUCCl`, { rule: 'unfold', node: D, path: ['body', 'fn', 'arg', 'fn'] })
    e.push(`${tag} unfold SUCCr`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn'] })
    e.pushConv(`${tag} left-shift`, D, U1)
  } else {
    e.push(`${tag} unfold SUCCo`, { rule: 'unfold', node: D, path: ['body', 'fn'] })
    e.push(`${tag} unfold PLUS`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn', 'fn'] })
    e.push(`${tag} unfold SUCCi`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn', 'arg', 'fn'] })
    e.pushConv(`${tag} left-shift`, D, U2)
  }
  const before = e.cur
  e.push(`${tag} fission`, { rule: 'fission', node: D, path: ['body', 'arg', 'fn'] })
  const Ex = e.newNodeIn(region, before)
  if (isF1) {
    e.push(`${tag} E fold PLUS`, { rule: 'fold', node: Ex, path: ['body', 'fn', 'fn'], constId: 'PLUS' })
    e.push(`${tag} E fold SUCC`, { rule: 'fold', node: Ex, path: ['body', 'arg', 'fn'], constId: 'SUCC' })
  } else {
    e.push(`${tag} E fold SUCC`, { rule: 'fold', node: Ex, path: ['body', 'fn'], constId: 'SUCC' })
    e.push(`${tag} E fold PLUS`, { rule: 'fold', node: Ex, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
  }
  e.push(`${tag} D fold SUCC`, { rule: 'fold', node: D, path: ['body', 'fn'], constId: 'SUCC' })
  return Ex
}

/**
 * succShiftS: `ℕ(m) ∧ (sn = SUCC n) ⟹ ℕ(m) ∧ (PLUS m (SUCC n) —o— SUCC (PLUS m n))`.
 * The SUCC-consumer node keeps the statement citable (its n-line is a boundary
 * attachment); ℕ(m) is a folded guard on both sides. Boundary = [wm, wn, wsn].
 */
function deriveSuccShiftS(ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const ref = l.ref(l.root, 'nat', 1)
  const wm = l.wire(l.root, [{ node: ref, port: { kind: 'arg', index: 0 } }])
  const nS = l.termNode(l.root, p('SUCC s0'))
  const wn = l.wire(l.root, [{ node: nS, port: { kind: 'freeVar', name: 's0' } }])
  const wsn = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wm, wn, wsn])
  const e = new DerivationCursor(lhsD, ctx)

  // ---- D0 prelude: iterate the folded ref, relUnfold the COPY (ambient stays folded)
  let snap = e.cur
  e.push('D0a iterate ref', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [ref], wires: [] }), target: e.cur.root })
  const copyRef = Object.entries(e.cur.nodes).find(([id, n]) => n.kind === 'ref' && id !== ref && snap.nodes[id] === undefined)![0]
  snap = e.cur
  e.push('D0b relUnfold copy', { rule: 'relUnfold', node: copyRef })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]

  // ---- D2: instantiate the copy's bubble with the closed induction pair G
  const cb = new DiagramBuilder()
  const g1 = cb.termNode(cb.root, F1term)
  const g2 = cb.termNode(cb.root, F2term)
  const gbx = cb.wire(cb.root, [
    { node: g1, port: { kind: 'freeVar', name: 's0' } },
    { node: g2, port: { kind: 'freeVar', name: 's0' } },
  ])
  cb.wire(cb.root, [{ node: g1, port: { kind: 'output' } }, { node: g2, port: { kind: 'output' } }])
  e.push('D2 instantiate G', { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [gbx]), attachments: [], binders: {} })

  const nzC = e.nodeBy(cut1c, p('ZERO'))
  const w0C = e.wireOf(nzC, 'output')
  const cut2c = Object.entries(e.cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
      Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
  )![0]
  const cut3c = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]
  const F1_0 = e.nodeBy(cut1c, F1term)
  const F2_0 = e.nodeBy(cut1c, F2term)
  const o0 = e.wireOf(F1_0, 'output')

  // ---- t: transform the closure conjunct to the achievable IH-carrying shape
  const nSc = e.nodeBy(cut2c, p('SUCC s0'))
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
  e.push('t3 sever ws2', {
    rule: 'wireSever', wire: ws2,
    keep: [{ node: nS2, port: { kind: 'output' } }, { node: F1sc, port: { kind: 'freeVar', name: 's0' } }],
  })
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
  e.push('t9 cJ E1c=H1pc', { rule: 'congruenceJoin', a: E1c, b: H1pc, certificate: idCert })
  e.push('t9b cJ E2c=H2pc', { rule: 'congruenceJoin', a: E2c, b: H2pc, certificate: idCert })
  e.push('t11 deiterate E1c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), fuel: 64 })
  e.push('t11b deiterate E2c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E2c], wires: [] }), fuel: 64 })

  // ---- b: manufactured root base fact {Z1, M, Mp}; deiterate the copy's base
  const M = e.intro('b1 intro M', e.cur.root, p('\\n. PLUS ZERO (SUCC n)'))
  snap = e.cur
  e.push('b2 iterate M', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M], wires: [] }), target: e.cur.root })
  const Mp = e.newNodeIn(e.cur.root, snap)
  e.push('b3 unfold PLUS', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'fn'] })
  e.push('b3 unfold ZERO', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'arg'] })
  e.push('b3 unfold SUCC', { rule: 'unfold', node: Mp, path: ['body', 'arg', 'fn'] })
  e.pushConv('b3 convert to F2_0 form', Mp, lam(app(SUCC_BODY, app(app(PLUS_BODY, ZERO_BODY), bvar(0)))))
  e.push('b3 fold SUCC', { rule: 'fold', node: Mp, path: ['body', 'fn'], constId: 'SUCC' })
  e.push('b3 fold PLUS', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
  e.push('b3 fold ZERO', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'arg'], constId: 'ZERO' })
  snap = e.cur
  e.push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['body', 'fn', 'arg'] })
  const Z1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('b4b fission ZERO out of Mp', { rule: 'fission', node: Mp, path: ['body', 'arg', 'fn', 'arg'] })
  const Z2 = e.newNodeIn(e.cur.root, snap)
  e.push('b5 cJ Z1=Z2', { rule: 'congruenceJoin', a: Z1, b: Z2, certificate: idCert })
  e.push('b6 erase Z2 dup', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z2], wires: [] }) })
  const wZ = e.wireOf(Z1, 'output')
  e.push('A7 deiterate base conjunct', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC, F1_0, F2_0], wires: [w0C, o0] }),
    fuel: 64,
  })

  // ---- c: manufactured root closure fact; discharge the copy's closure, unwrap
  snap = e.cur
  e.push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = e.newCutIn(e.cur.root, snap)
  const cutB = e.newCutIn(cutA, snap)
  const jb = new DiagramBuilder()
  const h1 = jb.termNode(jb.root, F1term)
  const h2 = jb.termNode(jb.root, F2term)
  const ns = jb.termNode(jb.root, p('SUCC s0'))
  jb.wire(jb.root, [
    { node: h1, port: { kind: 'freeVar', name: 's0' } },
    { node: h2, port: { kind: 'freeVar', name: 's0' } },
    { node: ns, port: { kind: 'freeVar', name: 's0' } },
  ])
  jb.wire(jb.root, [{ node: h1, port: { kind: 'output' } }, { node: h2, port: { kind: 'output' } }])
  jb.wire(jb.root, [{ node: ns, port: { kind: 'output' } }])
  snap = e.cur
  e.push('c2 insert IH+SUCC', { rule: 'insertion', region: cutA, pattern: mkDiagramWithBoundary(jb.build(), []), attachments: [], binders: {} })
  const H1 = e.newNodeIn(cutA, snap, F1term)
  const H2 = e.newNodeIn(cutA, snap, F2term)
  const wyF = e.wireOf(H1, 'freeVar')
  const ohF = e.wireOf(H1, 'output')
  const seedB = e.intro('c3 intro seedB', cutB, p('ZERO'))
  const D1 = kOpen(e, 'c4', seedB, cutB, p('\\n. PLUS (SUCC a) (SUCC n)'), { a: wyF })
  const D2 = kOpen(e, 'c4b', seedB, cutB, p('\\n. SUCC (PLUS (SUCC a) n)'), { a: wyF })
  const E1 = eExtract(e, 'c5', D1, cutB, true)
  const E2 = eExtract(e, 'c5b', D2, cutB, false)
  snap = e.cur
  e.push('c6 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutA, regions: [], nodes: [H1, H2], wires: [ohF] }), target: cutB })
  const H1p = e.newNodeIn(cutB, snap, F1term)
  const H2p = e.newNodeIn(cutB, snap, F2term)
  e.push('c7 cJ E1=H1p', { rule: 'congruenceJoin', a: E1, b: H1p, certificate: idCert })
  e.push('c7b cJ E2=H2p', { rule: 'congruenceJoin', a: E2, b: H2p, certificate: idCert })
  e.push('c7c cJ D1=D2', { rule: 'congruenceJoin', a: D1, b: D2, certificate: idCert })
  e.push('c8 deiterate E1', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [E1], wires: [] }), fuel: 64 })
  e.push('c8b deiterate E2', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [E2], wires: [] }), fuel: 64 })
  e.push('c8c erase seedB', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [seedB], wires: [e.wireOf(seedB, 'output')] }) })
  e.push('A8 deiterate Cl conjunct', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })

  // ---- e: assemble the applied pair on (wm, wn), erase the manufactured facts
  const F1m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F1term) && id !== M,
  )![0]
  const F2m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F2term) && id !== Mp,
  )![0]
  const oG = e.wireOf(F1m, 'output')
  const A1 = kOpen(e, 'e2 A1', Z1, e.cur.root, app(p('f'), p('a')), { f: oG, a: wn })
  const A2 = kOpen(e, 'e2 A2', Z1, e.cur.root, app(p('f'), p('a')), { f: oG, a: wn })
  e.push('e2 cJ A1=A2', { rule: 'congruenceJoin', a: A1, b: A2, certificate: idCert })
  e.push('e2 sever oG', {
    rule: 'wireSever', wire: oG,
    keep: [{ node: F1m, port: { kind: 'output' } }, { node: A1, port: { kind: 'freeVar', name: 's0' } }],
  })
  e.push('e2 fuse F1m->A1', { rule: 'fusion', wire: oG })
  const oG2 = e.wireOf(F2m, 'output')
  e.push('e2 fuse F2m->A2', { rule: 'fusion', wire: oG2 })
  e.pushConv('e2 convert A1', A1, p('PLUS s0 (SUCC s1)'))
  e.pushConv('e2 convert A2', A2, p('SUCC (PLUS s0 s1)'))
  const wM = e.wireOf(M, 'output')
  e.push('e3 erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M, Mp, Z1], wires: [wM, wZ] }) })
  e.push('e3 erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }) })
  return { name: 'succShiftS', lhs, rhs: mkDiagramWithBoundary(e.cur, [wm, wn, wsn]), steps: [...e.steps] }
}

export function buildFregeTheory(): Theory {
  const relations = { nat: natRelation() }
  const ctx: ProofContext = {
    definitions: fregeDefinitions,
    theorems: new Map(),
    relations: new Map(Object.entries(relations)),
  }
  const theorems: Theorem[] = conversionRecipes.map((r) => deriveConversion(r, ctx))
  theorems.push(deriveSuccShiftS(ctx))
  return { definitions: fregeDefinitions, relations, theorems }
}
