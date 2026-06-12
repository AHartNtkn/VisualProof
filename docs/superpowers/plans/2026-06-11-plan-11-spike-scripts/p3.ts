// p3: final-MP deiteration of R(a)'s N(b^) hypothesis against the AMBIENT
// rooted-N(b): does it tolerate a SHARED zero witness (extra endpoint on w0)?
// Builds the post-wireJoin state directly; separate-witness variant as control.
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import { applyDeiteration } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/rules/iteration'
import { p } from './lib'
import { buildNatAt, buildNatCut, P1term, P2term } from './comp'

function probe(shared: boolean): void {
  const b = new DiagramBuilder()
  const nzA = b.termNode(b.root, p('ZERO'))
  const NA = buildNatCut(b, b.root)
  const NB = buildNatCut(b, b.root)
  let nzB = nzA
  if (shared) {
    b.wire(b.root, [
      { node: nzA, port: { kind: 'output' } },
      { node: NA.a0, port: { kind: 'arg', index: 0 } },
      { node: NB.a0, port: { kind: 'arg', index: 0 } },
    ])
  } else {
    nzB = b.termNode(b.root, p('ZERO'))
    b.wire(b.root, [{ node: nzA, port: { kind: 'output' } }, { node: NA.a0, port: { kind: 'arg', index: 0 } }])
    b.wire(b.root, [{ node: nzB, port: { kind: 'output' } }, { node: NB.a0, port: { kind: 'arg', index: 0 } }])
  }
  const wa = b.wire(b.root, [{ node: NA.a3, port: { kind: 'arg', index: 0 } }])
  // R(a)-content at root, post wireJoin: hypothesis N(b^) inside cut_HA, b-line = wb
  const cutHA = b.cut(b.root)
  const nzH = b.termNode(cutHA, p('ZERO'))
  const NH = buildNatCut(b, cutHA)
  const w0H = b.wire(cutHA, [
    { node: nzH, port: { kind: 'output' } },
    { node: NH.a0, port: { kind: 'arg', index: 0 } },
  ])
  const cutCA = b.cut(cutHA)
  const P1 = b.termNode(cutCA, P1term)
  const P2 = b.termNode(cutCA, P2term)
  const wb = b.wire(b.root, [
    { node: NB.a3, port: { kind: 'arg', index: 0 } },
    { node: NH.a3, port: { kind: 'arg', index: 0 } },
    { node: P1, port: { kind: 'freeVar', name: 'q_0' } },
    { node: P2, port: { kind: 'freeVar', name: 'q_0' } },
  ])
  b.wire(b.root, [
    { node: P1, port: { kind: 'freeVar', name: 'q' } },
    { node: P2, port: { kind: 'freeVar', name: 'q' } },
  ]) // rides wa conceptually; separate fine for this probe — actually attach to wa:
  const d = b.build()
  try {
    const r = applyDeiteration(d, mkSelection(d, { region: cutHA, regions: [NH.cutN], nodes: [nzH], wires: [w0H] }), 64)
    const left = Object.values(r.nodes).filter((n) => n.region === cutHA).length
    console.log(`p3(${shared ? 'shared' : 'separate'}): deiteration OK (cutHA nodes left: ${left})`)
  } catch (err) {
    console.log(`p3(${shared ? 'shared' : 'separate'}): refused — ${err instanceof Error ? err.message : String(err)}`)
  }
}

probe(false)
probe(true)
