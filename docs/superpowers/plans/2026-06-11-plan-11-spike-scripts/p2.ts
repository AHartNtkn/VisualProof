// p2: instantiate N(a)'s bubble (in the wrapped dance) with the big closed comp R.
// Also p3 inline: shared-witness lhs builder acceptance.
import { DiagramBuilder } from '../../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../../src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '../../../../src/kernel/proof/step'
import { fregeDefinitions } from '../../../../src/theories/frege'
import { Eng, p } from './lib'
import { buildNatAt, buildComp, P1term, P2term } from './comp'

const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }

function main(): void {
  // plusComm lhs, separate witnesses
  const l = new DiagramBuilder()
  const A = buildNatAt(l, l.root)
  const B = buildNatAt(l, l.root)
  const lhsD = l.build()
  void mkDiagramWithBoundary(lhsD, [A.wx, B.wx])
  console.log('p2: lhs (separate witnesses) builds, boundary accepted')

  const e = new Eng(lhsD, ctx, true)
  let snap = e.cur
  e.push('A1', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
  const cO2 = e.newCutIn(e.cur.root, snap)
  const cI2 = e.newCutIn(cO2, snap)
  snap = e.cur
  e.push('A2', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [A.cutN], nodes: [], wires: [] }), target: cI2 })
  const cut1c = e.newCutIn(cI2, snap)
  const rBc = Object.entries(e.cur.regions).find(([, r]) => r.kind === 'bubble' && r.parent === cut1c)![0]
  snap = e.cur
  e.push('A4 instantiate R', { rule: 'comprehensionInstantiate', bubble: rBc, comp: buildComp(), binders: {} })

  // audit: cut1c children = base copy cutH0, closure cut2c, conclusion cut4c
  const cutsIn = (r: string): string[] =>
    Object.entries(e.cur.regions).filter(([, x]) => x.kind === 'cut' && x.parent === r).map(([id]) => id)
  const kids = cutsIn(cut1c)
  const J = JSON.stringify
  const pairIn = (r: string): { P1?: string; P2?: string } => {
    const out: { P1?: string; P2?: string } = {}
    for (const [id, n] of Object.entries(e.cur.nodes)) {
      if (n.kind === 'term' && n.region === r) {
        if (J(n.term) === J(P1term)) out.P1 = id
        if (J(n.term) === J(P2term)) out.P2 = id
      }
    }
    return out
  }
  // base copy: a child of cut1c whose grandchild cut holds the pair with q on w0a
  let report: string[] = []
  for (const k of kids) {
    const zero = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'term' && n.region === k && J(n.term) === J(p('ZERO')))
    const sub = cutsIn(k)
    const pairCut = sub.find((s) => pairIn(s).P1 !== undefined)
    if (pairCut !== undefined) {
      const pr = pairIn(pairCut)
      const qw = e.wireOf(pr.P1!, 'freeVar', 'q')
      const shared = e.wireOf(pr.P1!, 'output') === e.wireOf(pr.P2!, 'output')
      report.push(`copy[zero:${zero !== undefined},qWire:${qw === A.w0 ? 'w0a' : qw === A.wx ? 'wa' : qw},sharedOut:${shared}]`)
    } else {
      // closure cut: contains SUCC node + hyp copy + inner cut with conc copy
      const succ = Object.entries(e.cur.nodes).find(([, n]) => n.kind === 'term' && n.region === k && J(n.term) === J(p('SUCC q')))
      report.push(`closure[succ:${succ !== undefined},children:${sub.length}]`)
    }
  }
  console.log('p2: cut1c children:', kids.length, '|', report.join(' '))
}

try {
  main()
} catch (err) {
  console.log(`p2: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}
