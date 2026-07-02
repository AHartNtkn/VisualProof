// plusComm against inCutNat: lhs = two self-contained guards, NO root nodes.
// Drives the dance to the discharge and records every refusal exactly.
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import type { Term } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { Eng, p } from '/tmp/spike2/lib'
import { buildInCutNat, buildComp3, P1term } from '/tmp/spike3/incut'

const J = (t: Term) => JSON.stringify(t)
const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
const msg = (err: unknown): string => (err instanceof Error ? err.message : String(err))

function main(): void {
  const l = new DiagramBuilder()
  const NA = buildInCutNat(l, l.root)
  const NB = buildInCutNat(l, l.root)
  const lhsD = l.build()
  void mkDiagramWithBoundary(lhsD, [NA.wx, NB.wx])
  const rootNodes = Object.values(lhsD.nodes).filter((n) => n.region === lhsD.root).length
  const posNodes = Object.values(lhsD.nodes).filter((n) => n.kind === 'term').length
  console.log(`lhs audit: root nodes ${rootNodes} (expect 0) | term nodes anywhere: ${posNodes} (all inside guards)`)

  const e = new Eng(lhsD, ctx, true)
  // W1: the only node-minting rule at hand is insertion — attempt it at root
  try {
    const zb = new DiagramBuilder()
    zb.termNode(zb.root, p('ZERO'))
    e.push('W1 insert ZERO at root', { rule: 'insertion', region: e.cur.root, pattern: mkDiagramWithBoundary(zb.build(), []), attachments: [], binders: {} })
    console.log('W1: insertion at root SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W1: insertion at root refused — ${msg(err)}`)
  }

  // Dance: iterate guard-a to root level, instantiate with the strengthened comp
  let snap = e.cur
  e.push('D1 iterate guard', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [NA.cutN], nodes: [], wires: [] }), target: e.cur.root })
  const cut1c = e.newCutIn(e.cur.root, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  e.push('D2 instantiate R', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp3(), binders: {} })
  console.log('D1/D2: guard iterated to root level and instantiated with the nested comp OK')

  // locate the base conjunct: {nzC, w0C} + cut_H0[guard(b^), cut_C0[pair q@w0C]]
  const nzC = e.nodeBy(cut1c, p('ZERO'))
  const w0C = e.wireOf(nzC, 'output')
  const kids = Object.entries(e.cur.regions).filter(([, r]) => r.kind === 'cut' && r.parent === cut1c).map(([id]) => id)
  const pairCutOf = (h: string): string | undefined =>
    Object.entries(e.cur.regions).filter(([, r]) => r.kind === 'cut' && r.parent === h).map(([id]) => id)
      .find((s) => Object.values(e.cur.nodes).some((n) => n.kind === 'term' && n.region === s && J(n.term) === J(P1term)))
  const pairNodeIn = (s: string): string | undefined =>
    Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'term' && n.region === s && J(n.term) === J(P1term))?.[0]
  const cutH0 = kids.find((k) => {
    const pc = pairCutOf(k)
    if (pc === undefined) return false
    const p1 = pairNodeIn(pc)!
    return e.cur.wires[w0C]!.endpoints.some((ep) => ep.node === p1)
  })!
  const P1b = pairNodeIn(pairCutOf(cutH0)!)!
  console.log('base conjunct located: pair q rides the copy-internal zero line:', e.wireOf(P1b, 'freeVar', 'q') === w0C)

  // W2: discharge it with no root fact (none is manufacturable — no seeds)
  try {
    e.push('W2 deiterate base conjunct', {
      rule: 'deiteration',
      sel: mkSelection(e.cur, { region: cut1c, regions: [cutH0], nodes: [nzC], wires: [w0C] }),
      fuel: 64,
    })
    console.log('W2: base-conjunct deiteration SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W2: base-conjunct deiteration refused — ${msg(err)}`)
  }

  // W3: the spike2 literal route (BT-fusion) needs severing the zero line
  try {
    e.push('W3 sever w0C', { rule: 'wireSever', wire: w0C, keep: [{ node: nzC, port: { kind: 'output' } }] })
    console.log('W3: sever w0C SUCCEEDED (unexpected)')
  } catch (err) {
    console.log(`W3: sever w0C refused — ${msg(err)}`)
  }
  console.log('UNSEEDED plusComm: BLOCKED (no kernel rule mints a term node in a positive region from a node-free sheet; kMat needs a seed node)')
}

try {
  main()
} catch (err) {
  console.log(`pluscomm3: ERROR — ${msg(err)}`)
}
