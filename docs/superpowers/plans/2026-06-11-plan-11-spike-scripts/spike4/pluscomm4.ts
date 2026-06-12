// plusComm4, FLAT route: comp R(x) := PLUS x b -o- PLUS b x with ONE parameter
// attachment (the lhs b-line). R(a) IS the bare pair — no forall-b unwrapping.
import { app, port } from '../../../../../src/kernel/term/term'
import type { Term } from '../../../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../../../src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '../../../../../src/kernel/proof/step'
import type { Theorem } from '../../../../../src/kernel/proof/theorem'
import type { NodeId, RegionId, WireId } from '../../../../../src/kernel/diagram/diagram'
import { fregeDefinitions } from '../../../../../src/theories/frege'
import { E, p, idCert } from './lib4'
import { buildInCutNat } from './incut4'

const PT = p('PLUS s0 s1')
const Pu = fregeDefinitions['PLUS']!
const Su = fregeDefinitions['SUCC']!
const Zu = fregeDefinitions['ZERO']!

/** Flat parameterized comp: boundary = [x-stub, b-parameter-stub]. */
function buildComp4() {
  const cb = new DiagramBuilder()
  const P1 = cb.termNode(cb.root, PT) // PLUS x b
  const P2 = cb.termNode(cb.root, PT) // PLUS b x
  const wq = cb.wire(cb.root, [
    { node: P1, port: { kind: 'freeVar', name: 's0' } },
    { node: P2, port: { kind: 'freeVar', name: 's1' } },
  ])
  const wr = cb.wire(cb.root, [
    { node: P1, port: { kind: 'freeVar', name: 's1' } },
    { node: P2, port: { kind: 'freeVar', name: 's0' } },
  ])
  cb.wire(cb.root, [{ node: P1, port: { kind: 'output' } }, { node: P2, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(cb.build(), [wq, wr])
}

export function derivePlusComm4(ctx: ProofContext, quiet = true): Theorem {
  const l = new DiagramBuilder()
  const NA = buildInCutNat(l, l.root)
  const NB = buildInCutNat(l, l.root)
  const wa = NA.wx
  const wb = NB.wx
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wb])
  const e = new E(lhsD, ctx, quiet)

  // ---- D: iterate guard A to root, instantiate with the flat comp + param [wb]
  let snap = e.cur
  e.push('D1 iterate guard A', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [NA.cutN], nodes: [], wires: [] }), target: e.cur.root })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  e.push('D2 instantiate R(x):=x+b -o- b+x', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp4(), attachments: [wb], binders: {} })

  // locate copy anatomy
  const nzC = e.nodeBy(cut1c, p('ZERO'))
  const w0C = e.wireOf(nzC, 'output')
  const cut2c = Object.entries(e.cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
      Object.values(e.cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
  )![0]
  const cut3c = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]
  const P1_0 = e.nodeOnWire(cut1c, PT, 's0', w0C)
  const P2_0 = e.nodeOnWire(cut1c, PT, 's1', w0C)
  const o0 = e.wireOf(P1_0, 'output')

  // ---- t: transform the closure conjunct (fuse SUCCs in; left-shift the a-side)
  const nSc = e.nodeBy(cut2c, p('SUCC s0'))
  const wyC = e.wireOf(nSc, 'freeVar')
  const wsC = e.wireOf(nSc, 'output')
  const P1y = e.nodeOnWire(cut2c, PT, 's0', wyC)
  const P2y = e.nodeOnWire(cut2c, PT, 's1', wyC)
  const oyC = e.wireOf(P1y, 'output')
  const P1s = e.nodeOnWire(cut3c, PT, 's0', wsC)
  const P2s = e.nodeOnWire(cut3c, PT, 's1', wsC)
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
    keep: [{ node: nS2, port: { kind: 'output' } }, { node: P1s, port: { kind: 'freeVar', name: 's0' } }],
  })
  const ws3 = e.wireOf(nS3, 'output')
  e.push('t4 fuse nS2->P1s', { rule: 'fusion', wire: ws2 })
  e.push('t5 fuse nS3->P2s', { rule: 'fusion', wire: ws3 })
  // P1s = PLUS (SUCC y) b : left-shift to SUCC (PLUS y b), fission out the IH shape
  e.push('t6 unfold PLUS', { rule: 'unfold', node: P1s, path: ['fn', 'fn'] })
  e.push('t6 unfold SUCC', { rule: 'unfold', node: P1s, path: ['fn', 'arg', 'fn'] })
  e.pushConv('t6 left-shift', P1s, app(Su, app(app(Pu, port('s0')), port('s1'))))
  snap = e.cur
  e.push('t6 fission', { rule: 'fission', node: P1s, path: ['arg'] })
  const E1c = e.newNodeIn(cut3c, snap)
  e.push('t6 E fold PLUS', { rule: 'fold', node: E1c, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('t6 P1s fold SUCC', { rule: 'fold', node: P1s, path: ['fn'], constId: 'SUCC' })
  snap = e.cur
  e.push('t8 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [P1y, P2y], wires: [oyC] }), target: cut3c })
  const newPair = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined)
  const H1pc = newPair.find((id) =>
    e.cur.wires[wyC]!.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === 's0'))!
  e.push('t9 cJ E1c=H1pc', { rule: 'congruenceJoin', a: E1c, b: H1pc, certificate: idCert })
  e.push('t11 deiterate E1c', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), fuel: 64 })
  return finishPC(e, { lhs, quiet, wa, wb, cut1c, cut2c, nzC, w0C, P1_0, P2_0, o0, NB })
}

type MidPC = {
  lhs: ReturnType<typeof mkDiagramWithBoundary>
  quiet: boolean
  wa: WireId
  wb: WireId
  cut1c: RegionId
  cut2c: RegionId
  nzC: NodeId
  w0C: WireId
  P1_0: NodeId
  P2_0: NodeId
  o0: WireId
  NB: ReturnType<typeof buildInCutNat>
}

function finishPC(e: E, m: MidPC): Theorem {
  const { lhs, quiet, wa, wb, cut1c, cut2c, nzC, w0C, P1_0, P2_0, o0, NB } = m

  // ---- b: root base fact PLUS 0 b -o- PLUS b 0 (units are pure conversion)
  const Zs = e.intro('b0 intro K-seed', e.cur.root, p('ZERO'))
  const M = e.kOpen('b1 M=PLUS ZERO b', Zs, e.cur.root, p('PLUS ZERO r'), { r: wb })
  let snap = e.cur
  e.push('b2 iterate M', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M], wires: [] }), target: e.cur.root })
  const Mp = e.newNodeIn(e.cur.root, snap)
  e.push('b3 unfold PLUS', { rule: 'unfold', node: Mp, path: ['fn', 'fn'] })
  e.push('b3 unfold ZERO', { rule: 'unfold', node: Mp, path: ['fn', 'arg'] })
  e.pushConv('b3 convert to b+0', Mp, app(app(Pu, port('s0')), Zu))
  e.push('b3 fold PLUS', { rule: 'fold', node: Mp, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('b3 fold ZERO', { rule: 'fold', node: Mp, path: ['arg'], constId: 'ZERO' })
  snap = e.cur
  e.push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['fn', 'arg'] })
  const Z1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('b4b fission ZERO out of Mp', { rule: 'fission', node: Mp, path: ['arg'] })
  const Z2 = e.newNodeIn(e.cur.root, snap)
  e.push('b5 cJ Z1=Z2', { rule: 'congruenceJoin', a: Z1, b: Z2, certificate: idCert })
  e.push('b6 erase Z2 dup', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z2], wires: [] }) })
  const wZ = e.wireOf(Z1, 'output')
  const wM = e.wireOf(M, 'output')

  // ---- A7: discharge the base conjunct
  e.push('A7 deiterate base conjunct', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC, P1_0, P2_0], wires: [w0C, o0] }),
    fuel: 64,
  })

  // ---- c: root Cl fact; the inductive step cites succShiftS4 inside cutB
  snap = e.cur
  e.push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = e.newCutIn(e.cur.root, snap)
  const cutB = e.newCutIn(cutA, snap)
  const jb = new DiagramBuilder()
  const h1 = jb.termNode(jb.root, PT)
  const h2 = jb.termNode(jb.root, PT)
  const ns = jb.termNode(jb.root, p('SUCC s0'))
  jb.wire(jb.root, [
    { node: h1, port: { kind: 'freeVar', name: 's0' } },
    { node: h2, port: { kind: 'freeVar', name: 's1' } },
    { node: ns, port: { kind: 'freeVar', name: 's0' } },
  ])
  jb.wire(jb.root, [{ node: h1, port: { kind: 'output' } }, { node: h2, port: { kind: 'output' } }])
  jb.wire(jb.root, [{ node: ns, port: { kind: 'output' } }])
  const wrJ = jb.wire(jb.root, [
    { node: h1, port: { kind: 'freeVar', name: 's1' } },
    { node: h2, port: { kind: 'freeVar', name: 's0' } },
  ])
  snap = e.cur
  e.push('c2 insert hyp pair+SUCC', { rule: 'insertion', region: cutA, pattern: mkDiagramWithBoundary(jb.build(), [wrJ]), attachments: [wb], binders: {} })
  const newA = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined)
  const nSf = newA.find((id) => JSON.stringify(e.termOf(id)) === JSON.stringify(p('SUCC s0')))!
  const wyF = e.wireOf(nSf, 'freeVar')
  const H1 = e.nodeOnWire(cutA, PT, 's0', wyF)
  const H2 = e.nodeOnWire(cutA, PT, 's1', wyF)
  const ohF = e.wireOf(H1, 'output')

  // assemble the succShiftS4 occurrence in cutB: iterate guard B + mint SUCC(y)
  snap = e.cur
  e.push('c3 iterate guard B', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [NB.cutN], nodes: [], wires: [] }), target: cutB })
  const guardB2 = e.newCutIn(cutB, snap)
  const seedB = e.intro('c3b intro seedB', cutB, p('ZERO'))
  const nSb = e.kOpen('c4 mint SUCC(y)', seedB, cutB, p('SUCC a'), { a: wyF })
  const wsb = e.wireOf(nSb, 'output')
  snap = e.cur
  e.push('c5 cite succShiftS4', {
    rule: 'theorem', name: 'succShiftS4', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: cutB, regions: [guardB2], nodes: [nSb], wires: [] }), args: [wb, wyF, wsb] },
  })
  const newB = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined && e.cur.nodes[id]!.region === cutB)
  const A1 = newB.find((id) => JSON.stringify(e.termOf(id)) === JSON.stringify(p('PLUS s0 (SUCC s1)')))!
  const A2 = newB.find((id) => JSON.stringify(e.termOf(id)) === JSON.stringify(p('SUCC (PLUS s0 s1)')))!
  const nSb2 = newB.find((id) => JSON.stringify(e.termOf(id)) === JSON.stringify(p('SUCC s0')))!
  const guardB3 = e.newCutIn(cutB, snap)
  const oP = e.wireOf(A1, 'output')
  // A2 = SUCC (PLUS b y): fission out the IH shape, join onto the iterated IH
  snap = e.cur
  e.push('c6 fission A2', { rule: 'fission', node: A2, path: ['arg'] })
  const E2 = e.newNodeIn(cutB, snap)
  snap = e.cur
  e.push('c7 iterate IH pair', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutA, regions: [], nodes: [H1, H2], wires: [ohF] }), target: cutB })
  const newP = Object.keys(e.cur.nodes).filter((id) => snap.nodes[id] === undefined)
  const H2p = newP.find((id) =>
    e.cur.wires[wyF]!.endpoints.some((ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === 's1'))!
  e.push('c8 cJ E2=H2p', { rule: 'congruenceJoin', a: E2, b: H2p, certificate: idCert })
  e.push('c9 deiterate E2', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutB, regions: [], nodes: [E2], wires: [] }), fuel: 64 })
  e.push('c10 erase occurrence leftovers', {
    rule: 'erasure',
    sel: mkSelection(e.cur, { region: cutB, regions: [guardB3], nodes: [nSb2, seedB], wires: [wsb, e.wireOf(seedB, 'output')] }),
  })

  // ---- A8/A9: discharge the closure conjunct, unwrap
  e.push('A8 deiterate Cl conjunct', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })

  // ---- e: cleanup — R(a) IS the bare pair on (wa, wb)
  e.push('e1 erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [M, Mp, Z1, Zs], wires: [wM, wZ, e.wireOf(Zs, 'output')] }) })
  e.push('e2 erase Cl fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutA], nodes: [], wires: [] }) })
  if (!quiet) {
    const P1a = e.nodeOnWire(e.cur.root, PT, 's0', wa)
    const P2a = e.nodeOnWire(e.cur.root, PT, 's1', wa)
    console.log('  pair output shared:', e.wireOf(P1a, 'output') === e.wireOf(P2a, 'output'))
  }
  return { name: 'plusComm4', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wb]), steps: [...e.steps] }
}
