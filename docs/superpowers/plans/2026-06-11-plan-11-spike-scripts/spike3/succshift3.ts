// succShiftS against inCutNat, DIRECT route: iterate the guard to root level,
// instantiate, deiterate conjuncts straight against root-MANUFACTURED facts
// (zero minted by kMat off the lhs SUCC consumer — no ambient witness).
import { app, lam, bvar } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import type { Term } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/extract'
import { boundaryFingerprint } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/canonical/fingerprint'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import type { Theorem } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/theorem'
import type { NodeId, RegionId } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/diagram'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import { Eng, p, idCert } from '/tmp/spike2/lib'
import { F1term, F2term, eExtract } from '/tmp/spike2/succshift-thm'
import { buildInCutNat } from '/tmp/spike3/incut'

const Su = fregeDefinitions['SUCC']!
const Pu = fregeDefinitions['PLUS']!
const Zu = fregeDefinitions['ZERO']!
const J = (t: Term) => JSON.stringify(t)

export function deriveSuccShift3(ctx: ProofContext, quiet = true): Theorem {
  const l = new DiagramBuilder()
  const N = buildInCutNat(l, l.root)
  const wm = N.wx
  const nS = l.termNode(l.root, p('SUCC q'))
  const wn = l.wire(l.root, [{ node: nS, port: { kind: 'freeVar', name: 'q' } }])
  const wsn = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wm, wn, wsn])
  const e = new Eng(lhsD, ctx, quiet)

  // ---- D: iterate the guard to root level, instantiate with the closed G-comp
  let snap = e.cur
  e.push('D1 iterate guard', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [N.cutN], nodes: [], wires: [] }), target: e.cur.root })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  const cb = new DiagramBuilder()
  const g1 = cb.termNode(cb.root, F1term)
  const g2 = cb.termNode(cb.root, F2term)
  const gbx = cb.wire(cb.root, [
    { node: g1, port: { kind: 'freeVar', name: 'q' } },
    { node: g2, port: { kind: 'freeVar', name: 'q' } },
  ])
  cb.wire(cb.root, [{ node: g1, port: { kind: 'output' } }, { node: g2, port: { kind: 'output' } }])
  e.push('D2 instantiate G', { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [gbx]), binders: {} })

  // locate: base conjunct {nzC, w0C, F1_0, F2_0, o0} at cut1c; closure cut2c; conclusion cut4c
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
  if (!quiet) console.log('  base conjunct ported on internal w0C:', e.wireOf(F1_0, 'freeVar', 'q') === w0C)

  // ---- t: transform the closure conjunct (zero-independent; verbatim from rooted.ts)
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
  return finish3(e, { lhs, quiet, nS, wm, wn, cut1c, cut2c, nzC, w0C, F1_0, F2_0, o0 })
}

type Mid3 = {
  lhs: ReturnType<typeof mkDiagramWithBoundary>
  quiet: boolean
  nS: NodeId
  wm: string
  wn: string
  cut1c: RegionId
  cut2c: RegionId
  nzC: NodeId
  w0C: string
  F1_0: NodeId
  F2_0: NodeId
  o0: string
}

function finish3(e: Eng, m: Mid3): Theorem {
  const { lhs, quiet, nS, wm, wn, cut1c, cut2c, nzC, w0C, F1_0, F2_0, o0 } = m

  // ---- b0: mint a dedicated portless root ZERO seed off the SUCC consumer
  // (later kMats attach a port named 'q'; the seed's own term must not free 'q')
  const zSeed = e.kMat('b0 mint zSeed', nS, p('SUCC q'), e.cur.root, p('ZERO'), {})

  // ---- b: MANUFACTURED root base fact {Z1, wZ, M, Mp, wM}
  const M = e.kMat('b1', zSeed, p('ZERO'), e.cur.root, p('\\n. PLUS ZERO (SUCC n)'), {})
  let snap = e.cur
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
  e.push('b5 cJ Z1=Z2', { rule: 'congruenceJoin', a: Z1, b: Z2, certificate: idCert })
  e.push('b6 erase Z2 dup', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z2], wires: [] }) })
  const wZ = e.wireOf(Z1, 'output')
  if (!quiet) console.log('  manufactured base fact: wZ endpoints', e.cur.wires[wZ]!.endpoints.length, '== w0C endpoints', e.cur.wires[w0C]!.endpoints.length)

  // ---- A7-direct: deiterate the base conjunct against the manufactured fact
  e.push('A7 deiterate base conjunct', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC, F1_0, F2_0], wires: [w0C, o0] }),
    fuel: 64,
  })

  // ---- c: root Cl fact (seed = nS copy), then A8-direct
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
  e.push('c3 iterate zSeed', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [zSeed], wires: [] }), target: cutB })
  const nSb = e.newNodeIn(cutB, snap)
  const D1 = e.kMat('c4', nSb, p('ZERO'), cutB, p('\\n. PLUS (SUCC q) (SUCC n)'), { q: wyF })
  const D2 = e.kMat('c4b', nSb, p('ZERO'), cutB, p('\\n. SUCC (PLUS (SUCC q) n)'), { q: wyF })
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
  e.push('c8c erase zSeed copy', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [nSb], wires: [] }) })
  if (!quiet) {
    const factEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }))
    const clEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }))
    console.log('  Cl fact == transformed conjunct:',
      boundaryFingerprint(mkDiagramWithBoundary(factEx.pattern.diagram, [])) ===
      boundaryFingerprint(mkDiagramWithBoundary(clEx.pattern.diagram, [])))
  }
  e.push('A8 deiterate Cl conjunct', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })
  return finish3b(e, { lhs, quiet, zSeed, wm, wn, M, Mp, Z1, wZ, cutA })
}

type Mid3b = {
  lhs: ReturnType<typeof mkDiagramWithBoundary>
  quiet: boolean
  zSeed: NodeId
  wm: string
  wn: string
  M: NodeId
  Mp: NodeId
  Z1: NodeId
  wZ: string
  cutA: RegionId
}

function finish3b(e: Eng, m: Mid3b): Theorem {
  const { lhs, quiet, zSeed, wm, wn, M, Mp, Z1, wZ, cutA } = m
  // A9 left the bare G(m) pair at root
  const F1m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F1term) && id !== M,
  )![0]
  const F2m = Object.entries(e.cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === e.cur.root && J(n.term) === J(F2term) && id !== Mp,
  )![0]
  const oG = e.wireOf(F1m, 'output')
  if (!quiet) console.log('  bare G(m) at root on wm:', e.wireOf(F1m, 'freeVar', 'q') === wm)

  // ---- e2: applied pair on wm/wn (S-variant names: arg 'q', fusion freshens m-port to q_0)
  const A1 = e.kMat('e2 A1', zSeed, p('ZERO'), e.cur.root, app(p('f'), p('q')), { f: oG, q: wn })
  const A2 = e.kMat('e2 A2', zSeed, p('ZERO'), e.cur.root, app(p('f'), p('q')), { f: oG, q: wn })
  e.push('e2 cJ A1=A2', { rule: 'congruenceJoin', a: A1, b: A2, certificate: idCert })
  e.push('e2 sever oG', {
    rule: 'wireSever', wire: oG,
    keep: [{ node: F1m, port: { kind: 'output' } }, { node: A1, port: { kind: 'freeVar', name: 'f' } }],
  })
  e.push('e2 fuse F1m->A1', { rule: 'fusion', wire: oG })
  const oG2 = e.wireOf(F2m, 'output')
  e.push('e2 fuse F2m->A2', { rule: 'fusion', wire: oG2 })
  e.pushConv('e2 convert A1', A1, p('PLUS q_0 (SUCC q)'))
  e.pushConv('e2 convert A2', A2, p('SUCC (PLUS q_0 q)'))

  // ---- e3: erase the root facts
  const wM = e.wireOf(M, 'output')
  e.push('e3 erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M, Mp, Z1, zSeed], wires: [wM, wZ, e.wireOf(zSeed, 'output')] }) })
  e.push('e3 erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }) })
  return { name: 'succShiftS3', lhs, rhs: mkDiagramWithBoundary(e.cur, [...lhs.boundary]), steps: [...e.steps] }
}
