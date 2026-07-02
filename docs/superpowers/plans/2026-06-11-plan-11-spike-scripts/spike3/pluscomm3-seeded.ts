// CONTROL (deviates from the requested statement): lhs = guards + ONE root ZERO
// seed Z0 on its own line. Shows how far plusComm gets under inCutNat with a seed,
// and the exact gates that still block the base-conjunct justifier.
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import { convertible } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/convert'
import type { Term } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { Eng, p, idCert } from '/tmp/spike2/lib'
import { buildInCutNat, buildComp3, P1term, P2term } from '/tmp/spike3/incut'

const J = (t: Term) => JSON.stringify(t)
const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
const msg = (err: unknown): string => (err instanceof Error ? err.message : String(err))

function main(): void {
  const l = new DiagramBuilder()
  const NA = buildInCutNat(l, l.root)
  const NB = buildInCutNat(l, l.root)
  const Z0 = l.termNode(l.root, p('ZERO'))
  const wZ0 = l.wire(l.root, [{ node: Z0, port: { kind: 'output' } }])
  const lhsD = l.build()
  void mkDiagramWithBoundary(lhsD, [NA.wx, NB.wx])
  console.log('SEEDED lhs (DEVIATION): root nodes', Object.values(lhsD.nodes).filter((n) => n.region === lhsD.root).length, '(the granted Z0)')

  const e = new Eng(lhsD, ctx, true)
  let snap = e.cur
  e.push('D1', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [NA.cutN], nodes: [], wires: [] }), target: e.cur.root })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  e.push('D2', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp3(), binders: {} })
  const nzC = e.nodeBy(cut1c, p('ZERO'))
  const w0C = e.wireOf(nzC, 'output')

  // S1: instantiate the copy's witness by the granted seed, discharge the copy's zero
  e.push('S1 wireJoin Z0-line = copy zero line', { rule: 'wireJoin', a: wZ0, b: w0C })
  e.push('S2 deiterate copy zero vs Z0', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [], nodes: [nzC], wires: [] }), fuel: 64 })
  console.log('S1/S2: copy witness joined onto Z0-line and its ZERO discharged OK')

  // base conjunct is now cut_H0[guard(b^), cut_C0[pair(q@wZ0, q_0@b^)]] hanging on wZ0.
  // Manufacture the justifier fact at root: dcIntro + insert guard; pair in cutC'.
  snap = e.cur
  e.push('F1 dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cutH = e.newCutIn(e.cur.root, snap)
  const cutC = e.newCutIn(cutH, snap)
  const hb = new DiagramBuilder()
  buildInCutNat(hb, hb.root)
  snap = e.cur
  e.push('F2 insert guard(b^)', { rule: 'insertion', region: cutH, pattern: mkDiagramWithBoundary(hb.build(), []), attachments: [], binders: {} })
  const wbH = Object.entries(e.cur.wires).find(
    ([id, w]) => w.scope === cutH && w.endpoints.length === 1 && snap.wires[id] === undefined,
  )![0]
  snap = e.cur
  e.push('F3 iterate Z0 seed (no wire: wZ0 now carries the conjunct ports)', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [Z0], wires: [] }), target: cutC })
  const Zx = e.newNodeIn(cutC, snap)
  const zc = e.kMat('F3b mint inner-line zero', Zx, p('ZERO'), cutC, p('ZERO'), {})
  const L0 = e.kMat('F4', zc, p('ZERO'), cutC, p('PLUS ZERO q_0'), { q_0: wbH })
  const R0 = e.kMat('F4b', zc, p('ZERO'), cutC, p('PLUS q_0 ZERO'), { q_0: wbH })
  e.push('F5 unfold L.PLUS', { rule: 'unfold', node: L0, path: ['fn', 'fn'] })
  e.push('F5 unfold L.ZERO', { rule: 'unfold', node: L0, path: ['fn', 'arg'] })
  e.push('F5 unfold R.PLUS', { rule: 'unfold', node: R0, path: ['fn', 'fn'] })
  e.push('F5 unfold R.ZERO', { rule: 'unfold', node: R0, path: ['arg'] })
  const cert = convertible(e.termOf(L0), e.termOf(R0), 8192)
  if (cert.status !== 'convertible') throw new Error(`F5 cert: ${cert.status}`)
  e.push('F5 cJ L=R (units)', { rule: 'congruenceJoin', a: L0, b: R0, certificate: cert.certificate })
  e.push('F6 fold L.PLUS', { rule: 'fold', node: L0, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('F6 fold L.ZERO', { rule: 'fold', node: L0, path: ['fn', 'arg'], constId: 'ZERO' })
  e.push('F6 fold R.PLUS', { rule: 'fold', node: R0, path: ['fn', 'fn'], constId: 'PLUS' })
  e.push('F6 fold R.ZERO', { rule: 'fold', node: R0, path: ['arg'], constId: 'ZERO' })
  snap = e.cur
  e.push('F7 fission ZERO out of L0', { rule: 'fission', node: L0, path: ['fn', 'arg'] })
  const Zf1 = e.newNodeIn(cutC, snap)
  const wf1 = e.wireOf(Zf1, 'output')
  console.log('F: literal pair derived in cutC and L0 fissioned to ported form:', J(e.termOf(L0)) === J(P1term))

  // The pair must ride the ROOT zero line wZ0 (to be iso to the conjunct). Attempts:
  try {
    e.push('W4 cJ Zf1=Zx (port onto wZ0)', { rule: 'congruenceJoin', a: Zf1, b: Zx, certificate: idCert })
    console.log('W4: cJ onto the root zero line SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W4: cJ onto the root zero line refused — ${msg(err)}`)
  }
  try {
    e.push('W5 wireJoin wZ0=wf1', { rule: 'wireJoin', a: wZ0, b: wf1 })
    console.log('W5: wireJoin SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W5: wireJoin refused — ${msg(err)}`)
  }
  // inner-witnessed form IS reachable (cJ at equal depth) — but it is not iso to the conjunct:
  e.push('W6 cJ Zf1=zc (inner witness)', { rule: 'congruenceJoin', a: Zf1, b: zc, certificate: idCert })
  e.push('W6b deiterate Zf1 dup', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutC, regions: [], nodes: [Zf1], wires: [] }), fuel: 64 })
  snap = e.cur
  e.push('W6c fission ZERO out of R0', { rule: 'fission', node: R0, path: ['arg'] })
  const Zf2 = e.newNodeIn(cutC, snap)
  e.push('W6d cJ Zf2=zc', { rule: 'congruenceJoin', a: Zf2, b: zc, certificate: idCert })
  e.push('W6e deiterate Zf2 dup', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cutC, regions: [], nodes: [Zf2], wires: [] }), fuel: 64 })
  e.push('W6f erase Zx seed', { rule: 'erasure', sel: mkSelection(e.cur, { region: cutC, regions: [], nodes: [Zx], wires: [] }) })
  console.log('W6: inner-witnessed fact completed (pair ported on a cutC-internal zero line):', J(e.termOf(R0)) === J(P2term))

  // W7: the conjunct rides the OUTER wZ0 — the inner-witnessed fact does not justify it
  const kids = Object.entries(e.cur.regions).filter(([, r]) => r.kind === 'cut' && r.parent === cut1c).map(([id]) => id)
  const pairCutOf = (h: string): string | undefined =>
    Object.entries(e.cur.regions).filter(([, r]) => r.kind === 'cut' && r.parent === h).map(([id]) => id)
      .find((s) => Object.values(e.cur.nodes).some((n) => n.kind === 'term' && n.region === s && J(n.term) === J(P1term)))
  const cutH0 = kids.find((k) => {
    const pc = pairCutOf(k)
    if (pc === undefined) return false
    const p1 = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'term' && n.region === pc && J(n.term) === J(P1term))![0]
    return e.cur.wires[wZ0]!.endpoints.some((ep) => ep.node === p1)
  })!
  try {
    e.push('W7 deiterate base conjunct', { rule: 'deiteration', sel: mkSelection(e.cur, { region: cut1c, regions: [cutH0], nodes: [], wires: [] }), fuel: 64 })
    console.log('W7: base-conjunct deiteration SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W7: base-conjunct deiteration vs inner-witnessed fact refused — ${msg(err)}`)
  }
  console.log('SEEDED plusComm: BLOCKED at the base-conjunct justifier — zero-line knowledge cannot cross the comp body\'s 2-cut nesting')
}

try {
  main()
} catch (err) {
  console.log(`pluscomm3-seeded: ERROR — ${msg(err)}`)
}
