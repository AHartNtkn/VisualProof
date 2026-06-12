// Parameterized succShift derivation (from verified rooted.ts), as a stored Theorem.
// opts.extraSucc=false → original bare-wn succShift; true → succShiftS with a
// root SUCC-node consumer on wn (boundary [wm, wn, wsn]) and e2 arg name 'q'
// (fusion then freshens the m-port to 'q_0': pair PLUS q_0 (SUCC q) -o- SUCC (PLUS q_0 q)).
import { app, lam, bvar, port } from '../../../../src/kernel/term/term'
import type { Term } from '../../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../../src/kernel/diagram/subgraph/extract'
import { boundaryFingerprint } from '../../../../src/kernel/diagram/canonical/fingerprint'
import type { ProofContext } from '../../../../src/kernel/proof/step'
import type { Theorem } from '../../../../src/kernel/proof/theorem'
import type { NodeId, RegionId, WireId } from '../../../../src/kernel/diagram/diagram'
import { fregeDefinitions } from '../../../../src/theories/frege'
import { Eng, p, idCert } from './lib'

const F1term = p('\\n. PLUS q (SUCC n)')
const F2term = p('\\n. SUCC (PLUS q n)')
const Pu = fregeDefinitions['PLUS']!
const Su = fregeDefinitions['SUCC']!
const Zu = fregeDefinitions['ZERO']!

/** rooted-N(x) into builder b at its root: nz ZERO at root on w0; returns [w0, wx, cut1]. */
export function buildRootedNat(b: DiagramBuilder): { w0: WireId; wx: WireId; cut1: RegionId; nz: NodeId } {
  const nz = b.termNode(b.root, p('ZERO'))
  const cut1 = b.cut(b.root)
  const rB = b.bubble(cut1, 1)
  const a0 = b.atom(rB, rB)
  const w0 = b.wire(b.root, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = b.cut(rB)
  const a1 = b.atom(cut2, rB)
  const ny = b.termNode(cut2, p('SUCC q'))
  b.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'q' } },
  ])
  const cut3 = b.cut(cut2)
  const a2 = b.atom(cut3, rB)
  b.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = b.cut(rB)
  const a3 = b.atom(cut4, rB)
  const wx = b.wire(b.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return { w0, wx, cut1, nz }
}

export function deriveSuccShift(ctx: ProofContext, opts: { extraSucc: boolean; quiet?: boolean }): Theorem {
  const l = new DiagramBuilder()
  const { w0, wx: wm, cut1, nz: nzId } = buildRootedNat(l)
  let wn: WireId
  let wsn: WireId | undefined
  if (opts.extraSucc) {
    const nS = l.termNode(l.root, p('SUCC q'))
    wn = l.wire(l.root, [{ node: nS, port: { kind: 'freeVar', name: 'q' } }])
    wsn = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  } else {
    wn = l.wire(l.root, [])
  }
  const lhsDiagram = l.build()
  const boundary = opts.extraSucc ? [wm, wn, wsn!] : [wm, wn]
  const lhs = mkDiagramWithBoundary(lhsDiagram, boundary)
  const e = new Eng(lhsDiagram, ctx, opts.quiet ?? true)
  const nz = nzId

  // ---- A: the wrapped dance
  let snap = e.cur
  e.push('A1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cO2 = e.newCutIn(e.cur.root, snap)
  const cI2 = e.newCutIn(cO2, snap)
  snap = e.cur
  e.push('A2 iterate N', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cut1], nodes: [], wires: [] }), target: cI2 })
  const cut1c = e.newCutIn(cI2, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]

  // A4: instantiate the copy's bubble with the closed λ-comp G (port q)
  const cb = new DiagramBuilder()
  const g1 = cb.termNode(cb.root, F1term)
  const g2 = cb.termNode(cb.root, F2term)
  const gbx = cb.wire(cb.root, [
    { node: g1, port: { kind: 'freeVar', name: 'q' } },
    { node: g2, port: { kind: 'freeVar', name: 'q' } },
  ])
  cb.wire(cb.root, [
    { node: g1, port: { kind: 'output' } },
    { node: g2, port: { kind: 'output' } },
  ])
  e.push('A4 instantiate G', { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [gbx]), binders: {} })
  const basePair = Object.entries(e.cur.nodes)
    .filter(([, n]) => n.kind === 'term' && n.region === cut1c).map(([id]) => id)
  const cut2c = Object.entries(e.cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
      Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
  )![0]
  const cut3c = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]

  // ---- A5/t: transform the closure COPY to the achievable shape
  const nSc = e.nodeBy(cut2c, p('SUCC q'))
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
    keep: [{ node: nS2, port: { kind: 'output' } }, { node: F1sc, port: { kind: 'freeVar', name: 'q' } }],
  })
  const ws3 = e.wireOf(nS3, 'output')
  e.push('t4 fuse nS2->F1sc', { rule: 'fusion', wire: ws2 })
  e.push('t5 fuse nS3->F2sc', { rule: 'fusion', wire: ws3 })
  // (continued in part 2)
  return finishSuccShift(e, { lhs, boundary, opts, nz, w0, wm, wn, cO2, cI2, cut1c, cut2c, cut3c, basePair, F1sc, F2sc })
}

type Mid = {
  lhs: ReturnType<typeof mkDiagramWithBoundary>
  boundary: WireId[]
  opts: { extraSucc: boolean; quiet?: boolean }
  nz: NodeId
  w0: WireId
  wm: WireId
  wn: WireId
  cO2: RegionId
  cI2: RegionId
  cut1c: RegionId
  cut2c: RegionId
  cut3c: RegionId
  basePair: NodeId[]
  F1sc: NodeId
  F2sc: NodeId
}

// E-extraction helper terms (identical in copy and root-fact flows)
const U1 = lam(app(Su, app(lam(app(app(Pu, port('q')), app(Su, bvar(0)))), bvar(0))))
const U2 = lam(app(Su, app(lam(app(Su, app(app(Pu, port('q')), bvar(0)))), bvar(0))))

function eExtract(e: Eng, tag: string, D: NodeId, region: RegionId, isF1: boolean): NodeId {
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
  const E = e.newNodeIn(region, before)
  if (isF1) {
    e.push(`${tag} E fold PLUS`, { rule: 'fold', node: E, path: ['body', 'fn', 'fn'], constId: 'PLUS' })
    e.push(`${tag} E fold SUCC`, { rule: 'fold', node: E, path: ['body', 'arg', 'fn'], constId: 'SUCC' })
  } else {
    e.push(`${tag} E fold SUCC`, { rule: 'fold', node: E, path: ['body', 'fn'], constId: 'SUCC' })
    e.push(`${tag} E fold PLUS`, { rule: 'fold', node: E, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
  }
  e.push(`${tag} D fold SUCC`, { rule: 'fold', node: D, path: ['body', 'fn'], constId: 'SUCC' })
  return E
}

function finishSuccShift(e: Eng, m: Mid): Theorem {
  const { opts, nz, w0, wm, wn, cO2, cut1c, cut2c, cut3c, basePair, F1sc, F2sc } = m
  const E1c = eExtract(e, 't6', F1sc, cut3c, true)
  const E2c = eExtract(e, 't7', F2sc, cut3c, false)

  // t8–t11: iterate the IH pair into cut3c, join, consume the E's
  const F1yc = e.nodeBy(cut2c, F1term)
  const F2yc = e.nodeBy(cut2c, F2term)
  const oyc = e.wireOf(F1yc, 'output')
  let snap = e.cur
  e.push('t8 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [F1yc, F2yc], wires: [oyc] }), target: cut3c })
  const H1pc = e.newNodeIn(cut3c, snap, F1term)
  const H2pc = e.newNodeIn(cut3c, snap, F2term)
  e.push('t9 cJ E1c=H1pc', { rule: 'congruenceJoin', a: E1c, b: H1pc, certificate: idCert })
  e.push('t9b cJ E2c=H2pc', { rule: 'congruenceJoin', a: E2c, b: H2pc, certificate: idCert })
  e.push('t11 deiterate E1c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), fuel: 64 })
  e.push('t11b deiterate E2c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E2c], wires: [] }), fuel: 64 })

  // ---- A3': extract the live conjuncts as the wrapper justifier patterns, insert at cO2
  const o0c = e.wireOf(basePair[0]!, 'output')
  const baseEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: cut1c, regions: [], nodes: basePair, wires: [o0c] }))
  snap = e.cur
  e.push('A3 insert G0+', { rule: 'insertion', region: cO2, pattern: baseEx.pattern, attachments: baseEx.attachments, binders: {} })
  const G0d1 = e.newNodeIn(cO2, snap, F1term)
  const G0d2 = e.newNodeIn(cO2, snap, F2term)
  const oDag = e.wireOf(G0d1, 'output')
  const clEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }))
  snap = e.cur
  e.push('A3b insert Cl+', { rule: 'insertion', region: cO2, pattern: clEx.pattern, attachments: clEx.attachments, binders: {} })
  const clDag = e.newCutIn(cO2, snap)

  // ---- A7–A9: consume the copy, double-cut-eliminate
  e.push('A7 deiterate G(0)c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [], nodes: basePair, wires: [o0c] }), fuel: 64 })
  e.push('A8 deiterate Cl(G)c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })

  // ---- B: root justifiers
  const M = e.kMat('b1', nz, p('ZERO'), e.cur.root, p('\\n. PLUS ZERO (SUCC n)'), {})
  snap = e.cur
  e.push('b2 iterate M', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M], wires: [] }), target: e.cur.root })
  const Mp = e.newNodeIn(e.cur.root, snap)
  e.push('b3 unfold PLUS', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'fn'] })
  e.push('b3 unfold ZERO', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'arg'] })
  e.push('b3 unfold SUCC', { rule: 'unfold', node: Mp, path: ['body', 'arg', 'fn'] })
  e.pushConv('b3 convert to F2_0 form', Mp, lam(app(Su, app(app(Pu, Zu), bvar(0)))))
  e.push('b3 fold SUCC', { rule: 'fold', node: Mp, path: ['body', 'fn'], constId: 'SUCC' })
  e.push('b3 fold PLUS', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
  e.push('b3 fold ZERO', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'arg'], constId: 'ZERO' })
  snap = e.cur
  e.push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['body', 'fn', 'arg'] })
  const Z1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('b4b fission ZERO out of Mp', { rule: 'fission', node: Mp, path: ['body', 'arg', 'fn', 'arg'] })
  const Z2 = e.newNodeIn(e.cur.root, snap)
  e.push('b5 cJ nz=Z1', { rule: 'congruenceJoin', a: nz, b: Z1, certificate: idCert })
  e.push('b5b cJ nz=Z2', { rule: 'congruenceJoin', a: nz, b: Z2, certificate: idCert })

  // ---- C: the root Cl(G) fact in the achievable shape
  snap = e.cur
  e.push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = e.newCutIn(e.cur.root, snap)
  const cutB = e.newCutIn(cutA, snap)
  const jb = new DiagramBuilder()
  const h1 = jb.termNode(jb.root, F1term)
  const h2 = jb.termNode(jb.root, F2term)
  const ns = jb.termNode(jb.root, p('SUCC q'))
  jb.wire(jb.root, [
    { node: h1, port: { kind: 'freeVar', name: 'q' } },
    { node: h2, port: { kind: 'freeVar', name: 'q' } },
    { node: ns, port: { kind: 'freeVar', name: 'q' } },
  ])
  jb.wire(jb.root, [{ node: h1, port: { kind: 'output' } }, { node: h2, port: { kind: 'output' } }])
  jb.wire(jb.root, [{ node: ns, port: { kind: 'output' } }])
  snap = e.cur
  e.push('c2 insert IH+SUCC', { rule: 'insertion', region: cutA, pattern: mkDiagramWithBoundary(jb.build(), []), attachments: [], binders: {} })
  const H1 = e.newNodeIn(cutA, snap, F1term)
  const H2 = e.newNodeIn(cutA, snap, F2term)
  const wyF = e.wireOf(H1, 'freeVar')
  const ohF = e.wireOf(H1, 'output')
  snap = e.cur
  e.push('c3 iterate nz seed', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [nz], wires: [] }), target: cutB })
  const nzb = e.newNodeIn(cutB, snap)
  const D1 = e.kMat('c4', nzb, p('ZERO'), cutB, p('\\n. PLUS (SUCC q) (SUCC n)'), { q: wyF })
  const D2 = e.kMat('c4b', nzb, p('ZERO'), cutB, p('\\n. SUCC (PLUS (SUCC q) n)'), { q: wyF })
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
  e.push('c8c erase nz seed copy', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [nzb], wires: [] }) })
  return finishSuccShift2(e, m, { M, Mp, Z1, Z2, cutA, G0d1, G0d2, oDag, clDag })
}

function finishSuccShift2(
  e: Eng,
  m: Mid,
  r: { M: NodeId; Mp: NodeId; Z1: NodeId; Z2: NodeId; cutA: RegionId; G0d1: NodeId; G0d2: NodeId; oDag: WireId; clDag: RegionId },
): Theorem {
  const { lhs, boundary, opts, nz, wm, wn, cO2 } = m
  const { M, Mp, Z1, Z2, cutA, G0d1, G0d2, oDag, clDag } = r
  const factEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }))
  if (!opts.quiet) {
    console.log('  fact == inserted Cl+:',
      boundaryFingerprint(mkDiagramWithBoundary(factEx.pattern.diagram, [])) ===
      boundaryFingerprint(mkDiagramWithBoundary(extractSubgraph(e.cur, mkSelection(e.cur, { region: cO2, regions: [clDag], nodes: [], wires: [] })).pattern.diagram, [])))
  }
  // ---- d: discharge the wrapper conjuncts, then unwrap
  e.push('d1 discharge G0+', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cO2, regions: [], nodes: [G0d1, G0d2], wires: [oDag] }), fuel: 64 })
  e.push('d2 discharge Cl+', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cO2, regions: [clDag], nodes: [], wires: [] }), fuel: 64 })
  e.push('e1 dcElim cO2', { rule: 'doubleCutElim', region: cO2 })
  const J = (t: Term) => JSON.stringify(t)
  const F1m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F1term) && id !== M,
  )![0]
  const F2m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F2term) && id !== Mp,
  )![0]
  const oG = e.wireOf(F1m, 'output')

  // ---- e2: applied pair on wm/wn. Arg port name: original 'nn'; S-variant 'q'
  // (collides with F-terms' m-port, which fusion freshens to 'q_0').
  const argName = opts.extraSucc ? 'q' : 'nn'
  const mPort = opts.extraSucc ? 'q_0' : 'q'
  const A1 = e.kMat('e2 A1', nz, p('ZERO'), e.cur.root, app(p('f'), p(argName)), { f: oG, [argName]: wn })
  const A2 = e.kMat('e2 A2', nz, p('ZERO'), e.cur.root, app(p('f'), p(argName)), { f: oG, [argName]: wn })
  e.push('e2 cJ A1=A2', { rule: 'congruenceJoin', a: A1, b: A2, certificate: idCert })
  e.push('e2 sever oG', {
    rule: 'wireSever', wire: oG,
    keep: [{ node: F1m, port: { kind: 'output' } }, { node: A1, port: { kind: 'freeVar', name: 'f' } }],
  })
  e.push('e2 fuse F1m->A1', { rule: 'fusion', wire: oG })
  const oG2 = e.wireOf(F2m, 'output')
  e.push('e2 fuse F2m->A2', { rule: 'fusion', wire: oG2 })
  e.pushConv('e2 convert A1', A1, p(`PLUS ${mPort} (SUCC ${argName})`))
  e.pushConv('e2 convert A2', A2, p(`SUCC (PLUS ${mPort} ${argName})`))

  // ---- e3: erase the root scaffolding (all positive)
  const wM = e.wireOf(M, 'output')
  e.push('e3 erase G0 pair', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M, Mp], wires: [wM] }) })
  e.push('e3 erase zero copies', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z1, Z2], wires: [] }) })
  e.push('e3 erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }) })

  const name = opts.extraSucc ? 'succShiftS' : 'succShift'
  return { name, lhs, rhs: mkDiagramWithBoundary(e.cur, boundary), steps: [...e.steps] }
}
