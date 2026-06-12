// plusComm spike: lhs = rooted-N(a) ^ rooted-N(b) (separate witnesses), boundary [wa, wb];
// rhs = lhs + applied pair PLUS q q_0 -o- PLUS q_0 q riding (wa, wb).
// Induction on a with R(x) = forall b [N(b) -> PLUS x b ~ PLUS b x] (closed comp).
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/extract'
import { boundaryFingerprint } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/canonical/fingerprint'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { checkTheorem, type Theorem } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/theorem'
import type { NodeId, RegionId, Term, WireId } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/diagram'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import { Eng, p, idCert } from './lib'
import { convertible } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/convert'
import { buildNatAt, buildComp, P1term, P2term } from './comp'
import { deriveSuccShift } from './succshift-thm'

const J = JSON.stringify

function main(): void {
  const ctx0: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
  const ssS = deriveSuccShift(ctx0, { extraSucc: true })
  checkTheorem(ssS, ctx0)
  const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map([[ssS.name, ssS]]) }
  console.log(`S0 succShiftS checkTheorem PASSED (${ssS.steps.length} steps), stored in context`)

  // ---- lhs
  const l = new DiagramBuilder()
  const NA = buildNatAt(l, l.root)
  const NB = buildNatAt(l, l.root)
  const wa = NA.wx
  const wb = NB.wx
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [wa, wb])
  const e = new Eng(lhsD, ctx, false)

  // ---- A: wrapped dance prefix
  let snap = e.cur
  e.push('A1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cO2 = e.newCutIn(e.cur.root, snap)
  const cI2 = e.newCutIn(cO2, snap)
  snap = e.cur
  e.push('A2 iterate N(a)', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [NA.cutN], nodes: [], wires: [] }), target: cI2 })
  const cut1c = e.newCutIn(cI2, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  e.push('A4 instantiate R', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp(), binders: {} })

  // locate the three copies under cut1c
  const cutsIn = (r: RegionId): RegionId[] =>
    Object.entries(e.cur.regions).filter(([, x]) => x.kind === 'cut' && x.parent === r).map(([id]) => id)
  const nodesIn = (r: RegionId, t: Term): NodeId[] =>
    Object.entries(e.cur.nodes).filter(([, n]) => n.kind === 'term' && n.region === r && J(n.term) === J(t)).map(([id]) => id)
  const kids = cutsIn(cut1c)
  const pairCutOf = (h: RegionId): RegionId | undefined => cutsIn(h).find((s) => nodesIn(s, P1term).length === 1)
  const cutH0 = kids.find((k) => nodesIn(k, p('ZERO')).length === 1 && pairCutOf(k) !== undefined)!
  const cut2c = kids.find((k) => nodesIn(k, p('SUCC q')).length === 1)!
  const cut4c = kids.find((k) => k !== cutH0 && k !== cut2c)!
  console.log('A4 copies located:', { cutH0, cut2c, cut4c })

  // ---- BT: transform the BASE copy to closed literal form (fuse ZERO copies in)
  const cutC0 = pairCutOf(cutH0)!
  const P1b = nodesIn(cutC0, P1term)[0]!
  const P2b = nodesIn(cutC0, P2term)[0]!
  snap = e.cur
  e.push('BT1 iterate nzA', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [NA.nz], wires: [] }), target: e.cur.root })
  const nz1 = e.newNodeIn(e.cur.root, snap)
  snap = e.cur
  e.push('BT1b iterate nzA', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [NA.nz], wires: [] }), target: e.cur.root })
  const nz2 = e.newNodeIn(e.cur.root, snap)
  e.push('BT2 sever w0a', {
    rule: 'wireSever', wire: NA.w0,
    keep: [{ node: nz1, port: { kind: 'output' } }, { node: P1b, port: { kind: 'freeVar', name: 'q' } }],
  })
  e.push('BT3 fuse nz1->P1b', { rule: 'fusion', wire: NA.w0 })
  const w0r = e.wireOf(NA.nz, 'output')
  e.push('BT4 sever w0r', {
    rule: 'wireSever', wire: w0r,
    keep: [{ node: nz2, port: { kind: 'output' } }, { node: P2b, port: { kind: 'freeVar', name: 'q' } }],
  })
  e.push('BT5 fuse nz2->P2b', { rule: 'fusion', wire: w0r })
  console.log('BT base pair now:', J(e.termOf(P1b)) === J(p('PLUS ZERO q_0')), J(e.termOf(P2b)) === J(p('PLUS q_0 ZERO')))
  const baseEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: cut1c, regions: [cutH0], nodes: [], wires: [] }))
  console.log('BT base copy closed (attachments):', baseEx.attachments.length === 0)
  console.log(`MILESTONE base-transform done (${e.steps.length} steps)`)

  // ---- CT: transform the CLOSURE copy — fuse the SUCC node into the conclusion pair
  const nSc = nodesIn(cut2c, p('SUCC q'))[0]!
  const cutHy = cutsIn(cut2c).find((k) => nodesIn(k, p('ZERO')).length === 1)!
  const cut3c = cutsIn(cut2c).find((k) => k !== cutHy)!
  const cutHs = cutsIn(cut3c)[0]!
  const cutCs0 = pairCutOf(cutHs)!
  const P1s = nodesIn(cutCs0, P1term)[0]!
  const P2s = nodesIn(cutCs0, P2term)[0]!
  const ws = e.wireOf(nSc, 'output')
  snap = e.cur
  e.push('CT1 iterate nSc', { rule: 'iteration', sel: mkSelection(e.cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nSc2 = e.newNodeIn(cut2c, snap)
  e.push('CT2 sever ws', {
    rule: 'wireSever', wire: ws,
    keep: [{ node: nSc2, port: { kind: 'output' } }, { node: P1s, port: { kind: 'freeVar', name: 'q' } }],
  })
  e.push('CT3 fuse nSc2->P1s', { rule: 'fusion', wire: ws })
  const wsr = e.wireOf(nSc, 'output')
  e.push('CT4 fuse nSc->P2s', { rule: 'fusion', wire: wsr })
  console.log('CT closure pair now:', J(e.termOf(P1s)) === J(p('PLUS (SUCC q) q_0')), J(e.termOf(P2s)) === J(p('PLUS q_0 (SUCC q)')))
  const clEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }))
  console.log('CT closure copy closed (attachments):', clEx.attachments.length === 0)

  // ---- A3: insert the live-extracted justifiers into cO2, consume the copies, unwrap inner
  snap = e.cur
  e.push('A3 insert base+', { rule: 'insertion', region: cO2, pattern: baseEx.pattern, attachments: [], binders: {} })
  const baseDag = e.newCutIn(cO2, snap)
  snap = e.cur
  e.push('A3b insert Cl+', { rule: 'insertion', region: cO2, pattern: clEx.pattern, attachments: [], binders: {} })
  const clDag = e.newCutIn(cO2, snap)
  e.push('A7 deiterate base copy', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cutH0], nodes: [], wires: [] }), fuel: 64 })
  e.push('A8 deiterate closure copy', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  e.push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })
  console.log(`MILESTONE wrapped dance done (${e.steps.length} steps)`)

  // ---- FB: root base fact — cutHb[ N(b^) ; cutCb[ PLUS ZERO q_0 -o- PLUS q_0 ZERO ] ]
  snap = e.cur
  e.push('FB1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutHb = e.newCutIn(e.cur.root, snap)
  const cutCb = e.newCutIn(cutHb, snap)
  const hb = new DiagramBuilder()
  buildNatAt(hb, hb.root)
  snap = e.cur
  e.push('FB2 insert N(b^)', { rule: 'insertion', region: cutHb, pattern: mkDiagramWithBoundary(hb.build(), []), attachments: [], binders: {} })
  const wbH = Object.entries(e.cur.wires).find(
    ([id, w]) => w.scope === cutHb && w.endpoints.length === 1 && snap.wires[id] === undefined,
  )![0]
  snap = e.cur
  e.push('FB3 iterate seed', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [NB.nz], wires: [] }), target: cutCb })
  const seedB = e.newNodeIn(cutCb, snap)
  const Lb = e.kMat('FB4', seedB, p('ZERO'), cutCb, p('PLUS ZERO q_0'), { q_0: wbH })
  const Rb = e.kMat('FB4b', seedB, p('ZERO'), cutCb, p('PLUS q_0 ZERO'), { q_0: wbH })
  // cJ needs const-free terms: unfold both, join with computed cert, fold back
  e.push('FB5 unfold L.PLUS', { rule: 'unfold', node: Lb, path: ['fn', 'fn'] })
  e.push('FB5 unfold L.ZERO', { rule: 'unfold', node: Lb, path: ['fn', 'arg'] })
  e.push('FB5 unfold R.PLUS', { rule: 'unfold', node: Rb, path: ['fn', 'fn'] })
  e.push('FB5 unfold R.ZERO', { rule: 'unfold', node: Rb, path: ['arg'] })
  const certB = convertible(e.termOf(Lb), e.termOf(Rb), 8192)
  if (certB.status !== 'convertible') throw new Error(`FB5 cert: ${certB.status}`)
  e.push('FB5 cJ L=R', { rule: 'congruenceJoin', a: Lb, b: Rb, certificate: certB.certificate })
  e.push('FB6 fold L.PLUS', { rule: 'fold', node: Lb, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('FB6 fold L.ZERO', { rule: 'fold', node: Lb, path: ['fn', 'arg'], constId: 'ZERO' })
  e.push('FB6 fold R.PLUS', { rule: 'fold', node: Rb, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('FB6 fold R.ZERO', { rule: 'fold', node: Rb, path: ['arg'], constId: 'ZERO' })
  e.push('FB7 erase seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutCb, regions: [], nodes: [seedB], wires: [] }) })
  const factBEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: e.cur.root, regions: [cutHb], nodes: [], wires: [] }))
  console.log('FB fact == base+:',
    boundaryFingerprint(mkDiagramWithBoundary(factBEx.pattern.diagram, [])) ===
    boundaryFingerprint(mkDiagramWithBoundary(baseEx.pattern.diagram, [])))
  console.log(`MILESTONE base fact done (${e.steps.length} steps)`)

  // ---- FC: root closure fact — cutAf[ R(y)-hyp ; cutBf[ cutHs2[ N(b^s) ; cutCs2[pair] ] ] ]
  snap = e.cur
  e.push('FC1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutAf = e.newCutIn(e.cur.root, snap)
  const cutBf = e.newCutIn(cutAf, snap)
  snap = e.cur
  e.push('FC2 insert R(y)-hyp', { rule: 'insertion', region: cutAf, pattern: mkDiagramWithBoundary(buildComp().diagram, []), attachments: [], binders: {} })
  const cutHyF = e.newCutIn(cutAf, snap)
  const cutCyF = pairCutOf(cutHyF)!
  const P1yF = nodesIn(cutCyF, P1term)[0]!
  const wyF = e.wireOf(P1yF, 'freeVar', 'q')
  snap = e.cur
  e.push('FC3 dcIntro in cutBf', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: cutBf, regions: [], nodes: [], wires: [] }) })
  const cutHs2 = e.newCutIn(cutBf, snap)
  const cutCs2 = e.newCutIn(cutHs2, snap)
  const hs = new DiagramBuilder()
  buildNatAt(hs, hs.root)
  snap = e.cur
  e.push('FC4 insert N(b^s)', { rule: 'insertion', region: cutHs2, pattern: mkDiagramWithBoundary(hs.build(), []), attachments: [], binders: {} })
  const wbS = Object.entries(e.cur.wires).find(
    ([id, w]) => w.scope === cutHs2 && w.endpoints.length === 1 && snap.wires[id] === undefined,
  )![0]
  const nzS = nodesIn(cutHs2, p('ZERO'))[0]!
  const cutNS = e.newCutIn(cutHs2, snap)
  const w0S = e.wireOf(nzS, 'output')
  // IH application: iterate the hypothesis into cutCs2, join its b-line to wbS, discharge its N(b^y)
  snap = e.cur
  e.push('FC5 iterate R(y)-hyp', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutAf, regions: [cutHyF], nodes: [], wires: [] }), target: cutCs2 })
  const cutHy2 = e.newCutIn(cutCs2, snap)
  const cutCy2 = pairCutOf(cutHy2)!
  const P1y2 = nodesIn(cutCy2, P1term)[0]!
  const wby2 = e.wireOf(P1y2, 'freeVar', 'q_0')
  e.push('FC6 wireJoin b-lines', { rule: 'wireJoin', a: wbS, b: wby2 })
  const nzy2 = nodesIn(cutHy2, p('ZERO'))[0]!
  const cutNy2 = cutsIn(cutHy2).find((k) => k !== cutCy2)!
  e.push('FC7 deiterate N(b^y)', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cutHy2, regions: [cutNy2], nodes: [nzy2], wires: [e.wireOf(nzy2, 'output')] }),
    fuel: 64,
  })
  e.push('FC8 dcElim cutHy2', { rule: 'doubleCutElim', region: cutHy2 })
  const I1 = nodesIn(cutCs2, P1term)[0]!
  const I2 = nodesIn(cutCs2, P2term)[0]!
  const wI = e.wireOf(I1, 'output')
  console.log('FC IH applied:', e.wireOf(I1, 'freeVar', 'q') === wyF && e.wireOf(I1, 'freeVar', 'q_0') === wbS && wI === e.wireOf(I2, 'output'))
  console.log(`MILESTONE IH in place (${e.steps.length} steps)`)

  // chain: A = PLUS (SUCC y) b ~ Bn = SUCC (PLUS y b) [left-shift] ~ SUCC@IH ~ S2 = SUCC (PLUS b y) [cite] ~ S1 = PLUS b (SUCC y)
  snap = e.cur
  e.push('FC9 iterate seed', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [NB.nz], wires: [] }), target: cutCs2 })
  const seedC = e.newNodeIn(cutCs2, snap)
  const An = e.kMat('FC10', seedC, p('ZERO'), cutCs2, p('PLUS (SUCC q) q_0'), { q: wyF, q_0: wbS })
  const Bn = e.kMat('FC11', seedC, p('ZERO'), cutCs2, p('SUCC (PLUS q q_0)'), { q: wyF, q_0: wbS })
  e.push('FC12 unfold A.PLUS', { rule: 'unfold', node: An, path: ['fn', 'fn'] })
  e.push('FC12 unfold A.SUCC', { rule: 'unfold', node: An, path: ['fn', 'arg', 'fn'] })
  e.push('FC12 unfold B.SUCC', { rule: 'unfold', node: Bn, path: ['fn'] })
  e.push('FC12 unfold B.PLUS', { rule: 'unfold', node: Bn, path: ['arg', 'fn', 'fn'] })
  const certC = convertible(e.termOf(An), e.termOf(Bn), 8192)
  if (certC.status !== 'convertible') throw new Error(`FC12 cert: ${certC.status}`)
  e.push('FC12 cJ A=B (left-shift)', { rule: 'congruenceJoin', a: An, b: Bn, certificate: certC.certificate })
  e.push('FC12 fold A.PLUS', { rule: 'fold', node: An, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('FC12 fold A.SUCC', { rule: 'fold', node: An, path: ['fn', 'arg', 'fn'], constId: 'SUCC' })
  e.push('FC12 fold B.SUCC', { rule: 'fold', node: Bn, path: ['fn'], constId: 'SUCC' })
  e.push('FC12 fold B.PLUS', { rule: 'fold', node: Bn, path: ['arg', 'fn', 'fn'], constId: 'PLUS' })
  snap = e.cur
  e.push('FC13 fission Bn arg', { rule: 'fission', node: Bn, path: ['arg'] })
  const E1 = e.newNodeIn(cutCs2, snap, P1term)
  e.push('FC13 cJ E1=I1', { rule: 'congruenceJoin', a: E1, b: I1, certificate: idCert })
  e.push('FC13 deiterate E1', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutCs2, regions: [], nodes: [E1], wires: [] }), fuel: 64 })
  console.log('FC Bn now SUCC@IH:', J(e.termOf(Bn)) === J(p('SUCC q_1')) && e.wireOf(Bn, 'freeVar', 'q_1') === e.wireOf(I1, 'output'))

  // citation: succShiftS at (b^s, y) — needs an N(b^s) copy + a SUCC-node occurrence in cutCs2
  snap = e.cur
  e.push('FC14 iterate N(b^s)', { rule: 'iteration', sel: mkSelection(e.cur, { region: cutHs2, regions: [cutNS], nodes: [nzS], wires: [w0S] }), target: cutCs2 })
  const nzS2 = e.newNodeIn(cutCs2, snap)
  const cutNS2 = e.newCutIn(cutCs2, snap)
  const w0S2 = e.wireOf(nzS2, 'output')
  const nSx = e.kMat('FC14b', seedC, p('ZERO'), cutCs2, p('SUCC q'), { q: wyF })
  const wsx = e.wireOf(nSx, 'output')
  snap = e.cur
  e.push('FC15 cite succShiftS', {
    rule: 'theorem', name: 'succShiftS', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: cutCs2, regions: [cutNS2], nodes: [nzS2, nSx], wires: [w0S2] }), args: [wbS, wyF, wsx] },
  })
  const S1 = e.newNodeIn(cutCs2, snap, p('PLUS q_0 (SUCC q)'))
  const S2 = e.newNodeIn(cutCs2, snap, p('SUCC (PLUS q_0 q)'))
  const nzS3 = e.newNodeIn(cutCs2, snap, p('ZERO'))
  const nSx2 = e.newNodeIn(cutCs2, snap, p('SUCC q'))
  const cutNS3 = e.newCutIn(cutCs2, snap)
  console.log('FC cited pair on (b^s, y):', e.wireOf(S1, 'freeVar', 'q_0') === wbS && e.wireOf(S1, 'freeVar', 'q') === wyF)
  console.log(`MILESTONE citation done (${e.steps.length} steps)`)

  // transport S2 onto the IH line, then join the two SUCC consumers
  snap = e.cur
  e.push('FC16 fission S2 arg', { rule: 'fission', node: S2, path: ['arg'] })
  const E2 = e.newNodeIn(cutCs2, snap, P2term)
  e.push('FC16 cJ E2=I2', { rule: 'congruenceJoin', a: E2, b: I2, certificate: idCert })
  e.push('FC16 deiterate E2', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutCs2, regions: [], nodes: [E2], wires: [] }), fuel: 64 })
  e.push('FC17 cJ Bn=S2', { rule: 'congruenceJoin', a: Bn, b: S2, certificate: idCert })
  const wStar = e.wireOf(An, 'output')
  console.log('FC chain closed:', wStar === e.wireOf(S1, 'output') && wStar === e.wireOf(Bn, 'output') && wStar === e.wireOf(S2, 'output'))

  // cleanup cutCs2 (positive): drop the citation residue + the chain middles + seed
  e.push('FC18 deiterate N(b^s) copy', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cutCs2, regions: [cutNS3], nodes: [nzS3], wires: [e.wireOf(nzS3, 'output')] }),
    fuel: 64,
  })
  e.push('FC18b erase SUCC copy', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutCs2, regions: [], nodes: [nSx2], wires: [wsx] }) })
  const wIm = e.wireOf(I1, 'output')
  e.push('FC18c erase chain middles', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutCs2, regions: [], nodes: [Bn, S2, I1, I2], wires: [wIm] }) })
  e.push('FC18d erase seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutCs2, regions: [], nodes: [seedC], wires: [] }) })
  console.log('FC final pair:', J(e.termOf(An)) === J(p('PLUS (SUCC q) q_0')) && J(e.termOf(S1)) === J(p('PLUS q_0 (SUCC q)')))
  const factCEx = extractSubgraph(e.cur, mkSelection(e.cur, { region: e.cur.root, regions: [cutAf], nodes: [], wires: [] }))
  console.log('FC fact == Cl+:',
    boundaryFingerprint(mkDiagramWithBoundary(factCEx.pattern.diagram, [])) ===
    boundaryFingerprint(mkDiagramWithBoundary(clEx.pattern.diagram, [])))
  console.log(`MILESTONE closure fact done (${e.steps.length} steps)`)

  // ---- D: discharge the wrapper justifiers against the root facts, unwrap
  e.push('d1 discharge base+', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cO2, regions: [baseDag], nodes: [], wires: [] }), fuel: 64 })
  e.push('d2 discharge Cl+', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cO2, regions: [clDag], nodes: [], wires: [] }), fuel: 64 })
  snap = e.cur
  e.push('e1 dcElim cO2', { rule: 'doubleCutElim', region: cO2 })
  const cutHA = cutsIn(e.cur.root).find((k) => snap.regions[k] !== undefined &&
    (snap.regions[k] as { parent?: string }).parent !== e.cur.root)!
  const cutCA = pairCutOf(cutHA)!
  const P1A = nodesIn(cutCA, P1term)[0]!
  const P2A = nodesIn(cutCA, P2term)[0]!
  console.log('R(a) at root:', e.wireOf(P1A, 'freeVar', 'q') === wa)

  // ---- MP: apply R(a) at the actual b against the ambient rooted-N(b)
  const wbA = e.wireOf(P1A, 'freeVar', 'q_0')
  e.push('mp1 wireJoin b-lines', { rule: 'wireJoin', a: wb, b: wbA })
  const nzA2 = nodesIn(cutHA, p('ZERO'))[0]!
  const cutNA2 = cutsIn(cutHA).find((k) => k !== cutCA)!
  e.push('mp2 deiterate N(b^)', {
    rule: 'deiteration',
    sel: mkSelection(e.cur, { region: cutHA, regions: [cutNA2], nodes: [nzA2], wires: [e.wireOf(nzA2, 'output')] }),
    fuel: 64,
  })
  e.push('mp3 dcElim cutHA', { rule: 'doubleCutElim', region: cutHA })
  console.log('bare pair at root:', e.cur.nodes[P1A]!.region === e.cur.root && e.cur.nodes[P2A]!.region === e.cur.root)

  // ---- Z: erase the root facts
  e.push('z1 erase base fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutHb], nodes: [], wires: [] }) })
  e.push('z2 erase closure fact', { rule: 'erasure', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cutAf], nodes: [], wires: [] }) })

  // ---- theorem
  const thm: Theorem = { name: 'plusComm', lhs, rhs: mkDiagramWithBoundary(e.cur, [wa, wb]), steps: [...e.steps] }
  checkTheorem(thm, ctx)
  console.log(`FINAL: bare plusComm checkTheorem PASSED (${e.steps.length} steps)`)
  console.log('rhs audit: root nodes', Object.values(e.cur.nodes).filter((n) => n.region === e.cur.root).length,
    '| pair shares output:', e.wireOf(P1A, 'output') === e.wireOf(P2A, 'output'),
    '| P1:', J(e.termOf(P1A)) === J(p('PLUS q q_0')), 'on (q@wa, q_0@wb):',
    e.wireOf(P1A, 'freeVar', 'q') === wa && e.wireOf(P1A, 'freeVar', 'q_0') === wb,
    '| P2:', J(e.termOf(P2A)) === J(p('PLUS q_0 q')), 'on (q@wa, q_0@wb):',
    e.wireOf(P2A, 'freeVar', 'q') === wa && e.wireOf(P2A, 'freeVar', 'q_0') === wb,
    '| wa endpoints:', e.cur.wires[wa]!.endpoints.length, '| wb endpoints:', e.cur.wires[wb]!.endpoints.length)
}

try {
  main()
} catch (err) {
  console.log(`pluscomm: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}
