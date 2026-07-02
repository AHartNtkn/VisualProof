// Spike 2c: rooted-ℕ (nz at root) → wrapped succShift → full discharge → bare applied form.
import { parseTerm } from '../../../../src/kernel/term/parse'
import { app, lam, bvar, port } from '../../../../src/kernel/term/term'
import type { Term } from '../../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../../src/kernel/diagram/subgraph/extract'
import { boundaryFingerprint } from '../../../../src/kernel/diagram/canonical/fingerprint'
import { applyConversion } from '../../../../src/kernel/rules/conversion'
import type { ConversionCertificate } from '../../../../src/kernel/term/certificate'
import { replayProof, type ProofContext, type ProofStep } from '../../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../../src/kernel/proof/theorem'
import type { Diagram, NodeId, RegionId, WireId } from '../../../../src/kernel/diagram/diagram'
import { fregeDefinitions } from '../../../../src/theories/frege'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
const idCert: ConversionCertificate = { leftSteps: [], rightSteps: [] }
// global port discipline: 'q' everywhere (comp, relation SUCC node, fission products)
const F1term = p('\\n. PLUS q (SUCC n)')
const F2term = p('\\n. SUCC (PLUS q n)')
const Pu = fregeDefinitions['PLUS']!
const Su = fregeDefinitions['SUCC']!

function main(): void {
  // ---- lhs: rooted ℕ(m) (nz at ROOT) + bare root n-line; boundary [wm, wn]
  const l = new DiagramBuilder()
  const nz = l.termNode(l.root, p('ZERO'))
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const a0 = l.atom(rB, rB)
  const w0 = l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const ny = l.termNode(cut2, p('SUCC q'))
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'q' } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wm = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  const wn = l.wire(l.root, [])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wm, wn])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (label: string, s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
    console.log(`  ${label} (${s.rule}): ok`)
  }
  const newCutIn = (parent: RegionId, before: Diagram): RegionId =>
    Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
    )![0]
  const newNodeIn = (region: RegionId, before: Diagram, term?: Term): NodeId =>
    Object.entries(cur.nodes).find(
      ([id, n]) => n.kind === 'term' && n.region === region && before.nodes[id] === undefined &&
        (term === undefined || JSON.stringify(n.term) === JSON.stringify(term)),
    )![0]
  const wireOf = (node: NodeId, kind: 'output' | 'freeVar'): WireId =>
    Object.entries(cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === kind))![0]

  // ---- A: the wrapped dance
  let snap = cur
  push('A1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
  const cO2 = newCutIn(cur.root, snap)
  const cI2 = newCutIn(cO2, snap)
  snap = cur
  push('A2 iterate ℕ', { rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }), target: cI2 })
  const cut1c = newCutIn(cI2, snap)
  const rBc = Object.entries(cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]

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
  push('A4 instantiate G', { rule: 'comprehensionInstantiate', bubble: rBc, comp: mkDiagramWithBoundary(cb.build(), [gbx]), binders: {} })
  const basePair = Object.entries(cur.nodes)
    .filter(([, n]) => n.kind === 'term' && n.region === cut1c).map(([id]) => id)
  const cut2c = Object.entries(cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
      Object.values(cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
  )![0]
  const cut3c = Object.entries(cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cut2c)![0]
  console.log('  structure:', { cO2, cI2, cut1c, basePair: basePair.length, cut2c, cut3c })

  // ---- A5: transform the closure COPY to the achievable shape
  const nodeBy = (region: RegionId, t: Term): NodeId => Object.entries(cur.nodes).find(
    ([, n]) => n.kind === 'term' && n.region === region && JSON.stringify(n.term) === JSON.stringify(t),
  )![0]
  const nSc = nodeBy(cut2c, p('SUCC q'))
  const F1sc = nodeBy(cut3c, F1term)
  const F2sc = nodeBy(cut3c, F2term)
  const wsC = wireOf(nSc, 'output')
  snap = cur
  push('t1 iterate nSᶜ', { rule: 'iteration', sel: mkSelection(cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS2 = newNodeIn(cut2c, snap)
  snap = cur
  push('t1b iterate nSᶜ', { rule: 'iteration', sel: mkSelection(cur, { region: cut2c, regions: [], nodes: [nSc], wires: [] }), target: cut2c })
  const nS3 = newNodeIn(cut2c, snap)
  push('t2 sever wsᶜ', { rule: 'wireSever', wire: wsC, keep: [{ node: nSc, port: { kind: 'output' } }] })
  const ws2 = Object.entries(cur.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === nS2 && ep.port.kind === 'output'))![0]
  push('t3 sever ws2', {
    rule: 'wireSever', wire: ws2,
    keep: [{ node: nS2, port: { kind: 'output' } }, { node: F1sc, port: { kind: 'freeVar', name: 'q' } }],
  })
  const ws3 = Object.entries(cur.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === nS3 && ep.port.kind === 'output'))![0]
  push('t4 fuse nS2→F1sᶜ', { rule: 'fusion', wire: ws2 })
  push('t5 fuse nS3→F2sᶜ', { rule: 'fusion', wire: ws3 })
  console.log('  fused F1sᶜ:', JSON.stringify((cur.nodes[F1sc] as { term: Term }).term) === JSON.stringify(p('\\n. PLUS (SUCC q) (SUCC n)')))

  // E-extraction helper (terms identical in copy and root-fact flows)
  const U1 = lam(app(Su, app(lam(app(app(Pu, port('q')), app(Su, bvar(0)))), bvar(0))))
  const U2 = lam(app(Su, app(lam(app(Su, app(app(Pu, port('q')), bvar(0)))), bvar(0))))
  const pushConv = (label: string, node: NodeId, t: Term): void => {
    const c = applyConversion(cur, node, t, 8192)
    push(label, { rule: 'conversion', node, term: t, certificate: c.certificate, attachments: {} })
  }
  const eExtract = (tag: string, D: NodeId, region: RegionId, isF1: boolean): NodeId => {
    if (isF1) {
      push(`${tag} unfold PLUS`, { rule: 'unfold', node: D, path: ['body', 'fn', 'fn'] })
      push(`${tag} unfold SUCCl`, { rule: 'unfold', node: D, path: ['body', 'fn', 'arg', 'fn'] })
      push(`${tag} unfold SUCCr`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn'] })
      pushConv(`${tag} left-shift`, D, U1)
    } else {
      push(`${tag} unfold SUCCo`, { rule: 'unfold', node: D, path: ['body', 'fn'] })
      push(`${tag} unfold PLUS`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn', 'fn'] })
      push(`${tag} unfold SUCCi`, { rule: 'unfold', node: D, path: ['body', 'arg', 'fn', 'arg', 'fn'] })
      pushConv(`${tag} left-shift`, D, U2)
    }
    const before = cur
    push(`${tag} fission`, { rule: 'fission', node: D, path: ['body', 'arg', 'fn'] })
    const E = newNodeIn(region, before)
    if (isF1) {
      push(`${tag} E fold PLUS`, { rule: 'fold', node: E, path: ['body', 'fn', 'fn'], constId: 'PLUS' })
      push(`${tag} E fold SUCC`, { rule: 'fold', node: E, path: ['body', 'arg', 'fn'], constId: 'SUCC' })
    } else {
      push(`${tag} E fold SUCC`, { rule: 'fold', node: E, path: ['body', 'fn'], constId: 'SUCC' })
      push(`${tag} E fold PLUS`, { rule: 'fold', node: E, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
    }
    push(`${tag} D fold SUCC`, { rule: 'fold', node: D, path: ['body', 'fn'], constId: 'SUCC' })
    return E
  }
  const E1c = eExtract('t6', F1sc, cut3c, true)
  const E2c = eExtract('t7', F2sc, cut3c, false)
  console.log('  D-residual port:', (((cur.nodes[F1sc] as { term: Term }).term as { body: { arg: { fn: { name: string } } } }).body.arg.fn.name))

  // t8–t11: iterate the IH pair into cut3ᶜ, join, consume the E's
  const F1yc = nodeBy(cut2c, F1term)
  const F2yc = nodeBy(cut2c, F2term)
  const oyc = wireOf(F1yc, 'output')
  snap = cur
  push('t8 iterate IH pair', { rule: 'iteration', sel: mkSelection(cur, { region: cut2c, regions: [], nodes: [F1yc, F2yc], wires: [oyc] }), target: cut3c })
  const H1pc = newNodeIn(cut3c, snap, F1term)
  const H2pc = newNodeIn(cut3c, snap, F2term)
  push('t9 cJ E1ᶜ≡H1′ᶜ', { rule: 'congruenceJoin', a: E1c, b: H1pc, certificate: idCert })
  push('t9b cJ E2ᶜ≡H2′ᶜ', { rule: 'congruenceJoin', a: E2c, b: H2pc, certificate: idCert })
  push('t11 deiterate E1ᶜ', { rule: 'deiteration', sel: mkSelection(cur, { region: cut3c, regions: [], nodes: [E1c], wires: [] }), fuel: 64 })
  push('t11b deiterate E2ᶜ', { rule: 'deiteration', sel: mkSelection(cur, { region: cut3c, regions: [], nodes: [E2c], wires: [] }), fuel: 64 })

  // ---- A3′: extract the live conjuncts as the wrapper justifier patterns, insert at cO2
  const o0c = wireOf(basePair[0]!, 'output')
  const baseEx = extractSubgraph(cur, mkSelection(cur, { region: cut1c, regions: [], nodes: basePair, wires: [o0c] }))
  snap = cur
  push('A3 insert G0‡', { rule: 'insertion', region: cO2, pattern: baseEx.pattern, attachments: baseEx.attachments, binders: {} })
  const G0d1 = newNodeIn(cO2, snap, F1term)
  const G0d2 = newNodeIn(cO2, snap, F2term)
  const oDag = wireOf(G0d1, 'output')
  const clEx = extractSubgraph(cur, mkSelection(cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }))
  snap = cur
  push('A3b insert Cl‡', { rule: 'insertion', region: cO2, pattern: clEx.pattern, attachments: clEx.attachments, binders: {} })
  const clDag = newCutIn(cO2, snap)

  // ---- A7–A9: consume the copy, double-cut-eliminate
  push('A7 deiterate G(0)ᶜ', { rule: 'deiteration', sel: mkSelection(cur, { region: cut1c, regions: [], nodes: basePair, wires: [o0c] }), fuel: 64 })
  push('A8 deiterate Cl(G)ᶜ', { rule: 'deiteration', sel: mkSelection(cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })
  push('A9 dcElim cut1c', { rule: 'doubleCutElim', region: cut1c })

  const wrapped: Theorem = { name: 'succShiftWrappedRooted', lhs, rhs: mkDiagramWithBoundary(cur, [wm, wn]), steps: [...steps] }
  checkTheorem(wrapped, ctx)
  console.log(`  MILESTONE 1: wrapped checkTheorem PASSED (${steps.length} steps)`)

  // ---- B: root justifiers. K-trick materializer off an arbitrary seed node
  const kMat = (tag: string, seed: NodeId, seedTerm: Term, region: RegionId, s: Term, attach: Record<string, WireId>): NodeId => {
    const target = app(lam(seedTerm), s)
    const c1 = applyConversion(cur, seed, target, 8192, attach)
    push(`${tag} K-expand`, { rule: 'conversion', node: seed, term: target, certificate: c1.certificate, attachments: attach })
    const before = cur
    push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
    const made = newNodeIn(region, before)
    const c2 = applyConversion(cur, seed, seedTerm, 8192)
    push(`${tag} K-restore`, { rule: 'conversion', node: seed, term: seedTerm, certificate: c2.certificate, attachments: {} })
    return made
  }

  // B-G0 (step 3): the ported G(0) pair on the zero line w0, at root
  const M = kMat('b1', nz, p('ZERO'), cur.root, p('\\n. PLUS ZERO (SUCC n)'), {})
  snap = cur
  push('b2 iterate M', { rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [M], wires: [] }), target: cur.root })
  const Mp = newNodeIn(cur.root, snap)
  push('b3 unfold PLUS', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'fn'] })
  push('b3 unfold ZERO', { rule: 'unfold', node: Mp, path: ['body', 'fn', 'arg'] })
  push('b3 unfold SUCC', { rule: 'unfold', node: Mp, path: ['body', 'arg', 'fn'] })
  const Zu = fregeDefinitions['ZERO']!
  pushConv('b3 convert to F2₀ form', Mp, lam(app(Su, app(app(Pu, Zu), bvar(0)))))
  push('b3 fold SUCC', { rule: 'fold', node: Mp, path: ['body', 'fn'], constId: 'SUCC' })
  push('b3 fold PLUS', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'fn'], constId: 'PLUS' })
  push('b3 fold ZERO', { rule: 'fold', node: Mp, path: ['body', 'arg', 'fn', 'arg'], constId: 'ZERO' })
  snap = cur
  push('b4 fission ZERO out of M', { rule: 'fission', node: M, path: ['body', 'fn', 'arg'] })
  const Z1 = newNodeIn(cur.root, snap)
  snap = cur
  push('b4b fission ZERO out of M′', { rule: 'fission', node: Mp, path: ['body', 'arg', 'fn', 'arg'] })
  const Z2 = newNodeIn(cur.root, snap)
  push('b5 cJ nz≡Z1', { rule: 'congruenceJoin', a: nz, b: Z1, certificate: idCert })
  push('b5b cJ nz≡Z2', { rule: 'congruenceJoin', a: nz, b: Z2, certificate: idCert })
  console.log('  root pair ported on w0:', wireOf(M, 'freeVar') === w0 && JSON.stringify((cur.nodes[M] as { term: Term }).term) === JSON.stringify(F1term))

  // B-Cl (step 4): the root Cl(G) fact in the achievable shape
  snap = cur
  push('c1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
  const cutA = newCutIn(cur.root, snap)
  const cutB = newCutIn(cutA, snap)
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
  snap = cur
  push('c2 insert IH+SUCC', { rule: 'insertion', region: cutA, pattern: mkDiagramWithBoundary(jb.build(), []), attachments: [], binders: {} })
  const H1 = newNodeIn(cutA, snap, F1term)
  const H2 = newNodeIn(cutA, snap, F2term)
  const wyF = wireOf(H1, 'freeVar')
  const ohF = wireOf(H1, 'output')
  snap = cur
  push('c3 iterate nz seed', { rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [nz], wires: [] }), target: cutB })
  const nzb = newNodeIn(cutB, snap)
  const D1 = kMat('c4', nzb, p('ZERO'), cutB, p('\\n. PLUS (SUCC q) (SUCC n)'), { q: wyF })
  const D2 = kMat('c4b', nzb, p('ZERO'), cutB, p('\\n. SUCC (PLUS (SUCC q) n)'), { q: wyF })
  const E1 = eExtract('c5', D1, cutB, true)
  const E2 = eExtract('c5b', D2, cutB, false)
  snap = cur
  push('c6 iterate IH pair', { rule: 'iteration', sel: mkSelection(cur, { region: cutA, regions: [], nodes: [H1, H2], wires: [ohF] }), target: cutB })
  const H1p = newNodeIn(cutB, snap, F1term)
  const H2p = newNodeIn(cutB, snap, F2term)
  push('c7 cJ E1≡H1′', { rule: 'congruenceJoin', a: E1, b: H1p, certificate: idCert })
  push('c7b cJ E2≡H2′', { rule: 'congruenceJoin', a: E2, b: H2p, certificate: idCert })
  push('c7c cJ D1≡D2', { rule: 'congruenceJoin', a: D1, b: D2, certificate: idCert })
  push('c8 deiterate E1', { rule: 'deiteration', sel: mkSelection(cur, { region: cutB, regions: [], nodes: [E1], wires: [] }), fuel: 64 })
  push('c8b deiterate E2', { rule: 'deiteration', sel: mkSelection(cur, { region: cutB, regions: [], nodes: [E2], wires: [] }), fuel: 64 })
  push('c8c erase nz seed copy', { rule: 'erasure', sel: mkSelection(cur, { region: cutB, regions: [], nodes: [nzb], wires: [] }) })
  const factEx = extractSubgraph(cur, mkSelection(cur, { region: cur.root, regions: [cutA], nodes: [], wires: [] }))
  console.log('  fact == inserted Cl‡:',
    boundaryFingerprint(mkDiagramWithBoundary(factEx.pattern.diagram, [])) ===
    boundaryFingerprint(mkDiagramWithBoundary(clEx.pattern.diagram, [])))
  // ---- d: discharge the wrapper conjuncts, then unwrap
  push('d1 discharge G0‡', { rule: 'deiteration', sel: mkSelection(cur, { region: cO2, regions: [], nodes: [G0d1, G0d2], wires: [oDag] }), fuel: 64 })
  push('d2 discharge Cl‡', { rule: 'deiteration', sel: mkSelection(cur, { region: cO2, regions: [clDag], nodes: [], wires: [] }), fuel: 64 })
  push('e1 dcElim cO2', { rule: 'doubleCutElim', region: cO2 })
  const F1m = Object.entries(cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === cur.root && JSON.stringify(n.term) === JSON.stringify(F1term) && id !== M,
  )![0]
  const F2m = Object.entries(cur.nodes).find(
    ([id, n]) => n.kind === 'term' && n.region === cur.root && JSON.stringify(n.term) === JSON.stringify(F2term) && id !== Mp,
  )![0]
  const oG = wireOf(F1m, 'output')
  console.log('  BARE G(m) at root:', oG === wireOf(F2m, 'output'), '| ported on wm:', wireOf(F1m, 'freeVar') === wm)

  // ---- e2: Phase 3 endgame — applied pair on wm/wn
  const A1 = kMat('e2 A1', nz, p('ZERO'), cur.root, app(p('f'), p('nn')), { f: oG, nn: wn })
  const A2 = kMat('e2 A2', nz, p('ZERO'), cur.root, app(p('f'), p('nn')), { f: oG, nn: wn })
  push('e2 cJ A1≡A2', { rule: 'congruenceJoin', a: A1, b: A2, certificate: idCert })
  push('e2 sever oG', {
    rule: 'wireSever', wire: oG,
    keep: [{ node: F1m, port: { kind: 'output' } }, { node: A1, port: { kind: 'freeVar', name: 'f' } }],
  })
  push('e2 fuse F1m→A1', { rule: 'fusion', wire: oG })
  const oG2 = wireOf(F2m, 'output')
  push('e2 fuse F2m→A2', { rule: 'fusion', wire: oG2 })
  pushConv('e2 convert A1', A1, p('PLUS q (SUCC nn)'))
  pushConv('e2 convert A2', A2, p('SUCC (PLUS q nn)'))

  // ---- e3: erase the root scaffolding (all positive)
  const wM = wireOf(M, 'output')
  push('e3 erase G0 pair', { rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [M, Mp], wires: [wM] }) })
  push('e3 erase zero copies', { rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [Z1, Z2], wires: [] }) })
  push('e3 erase Cl fact', { rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [cutA], nodes: [], wires: [] }) })

  const bare: Theorem = { name: 'succShift', lhs, rhs: mkDiagramWithBoundary(cur, [wm, wn]), steps }
  checkTheorem(bare, ctx)
  console.log(`  FINAL: bare succShift checkTheorem PASSED (${steps.length} steps)`)
  console.log('  rhs audit: root nodes', Object.values(cur.nodes).filter((n) => n.region === cur.root).length,
    '| pair shares output:', wireOf(A1, 'output') === wireOf(A2, 'output'),
    '| A1 term:', JSON.stringify((cur.nodes[A1] as { term: Term }).term) === JSON.stringify(p('PLUS q (SUCC nn)')),
    '| A2 term:', JSON.stringify((cur.nodes[A2] as { term: Term }).term) === JSON.stringify(p('SUCC (PLUS q nn)')),
    '| on wm/wn:', cur.wires[wm]!.endpoints.length === 3 && cur.wires[wn]!.endpoints.length === 2)
  void { lhs, steps, ny, a1, a2 }
}

try {
  main()
} catch (e) {
  console.log(`main: ERROR — ${e instanceof Error ? e.message : String(e)}`)
}
