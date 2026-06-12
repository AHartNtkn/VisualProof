// p1: assemble succShift theorems; verify; probe citations in a depth-2 positive region.
import { checkTheorem } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/theorem'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import { deriveSuccShift } from './succshift-thm'

const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
try {
  const t0 = deriveSuccShift(ctx, { extraSucc: false })
  checkTheorem(t0, ctx)
  console.log(`p1a: succShift (bare wn) assembled, checkTheorem PASSED (${t0.steps.length} steps)`)
} catch (err) {
  console.log(`p1a: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}
try {
  const t1 = deriveSuccShift(ctx, { extraSucc: true })
  checkTheorem(t1, ctx)
  console.log(`p1b: succShiftS (SUCC consumer) assembled, checkTheorem PASSED (${t1.steps.length} steps)`)
} catch (err) {
  console.log(`p1b: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}

// ---- p1c/p1d: cite inside cutB of a dcIntro pair (positive depth-2)
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkSelection } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/subgraph/selection'
import { Eng, p } from './lib'
import { buildRootedNat } from './succshift-thm'

const ssBare = deriveSuccShift(ctx, { extraSucc: false })
const ssS = deriveSuccShift(ctx, { extraSucc: true })
const ctx2: ProofContext = {
  definitions: fregeDefinitions,
  theorems: new Map([[ssBare.name, ssBare], [ssS.name, ssS]]),
}
const h = new DiagramBuilder()
const { w0, wx: wm, cut1, nz } = buildRootedNat(h)
const nS = h.termNode(h.root, p('SUCC q'))
const wn = h.wire(h.root, [{ node: nS, port: { kind: 'freeVar', name: 'q' } }])
const ws = h.wire(h.root, [{ node: nS, port: { kind: 'output' } }])
const e = new Eng(h.build(), ctx2, true)
let snap = e.cur
e.push('dcIntro', { rule: 'doubleCutIntro', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [], wires: [] }) })
const cA = e.newCutIn(e.cur.root, snap)
const cB = e.newCutIn(cA, snap)
snap = e.cur
e.push('iterate N(m)', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [cut1], nodes: [nz], wires: [w0] }), target: cB })
const nzC = e.newNodeIn(cB, snap)
const cut1C = e.newCutIn(cB, snap)
const w0C = e.wireOf(nzC, 'output')
snap = e.cur
e.push('iterate SUCC', { rule: 'iteration', sel: mkSelection(e.cur, { region: e.cur.root, regions: [], nodes: [nS], wires: [] }), target: cB })
const nSC = e.newNodeIn(cB, snap)
try {
  e.push('p1c cite bare succShift', {
    rule: 'theorem', name: 'succShift', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: cB, regions: [cut1C], nodes: [nzC], wires: [w0C] }), args: [wm, wn] },
  })
  console.log('p1c: bare-wn citation SUCCEEDED (unexpected)')
} catch (err) {
  console.log(`p1c: bare-wn citation refused — ${err instanceof Error ? err.message : String(err)}`)
}
try {
  snap = e.cur
  e.push('p1d cite succShiftS', {
    rule: 'theorem', name: 'succShiftS', direction: 'forward',
    at: { sel: mkSelection(e.cur, { region: cB, regions: [cut1C], nodes: [nzC, nSC], wires: [w0C] }), args: [wm, wn, ws] },
  })
  const s1 = e.newNodeIn(cB, snap, p('PLUS q_0 (SUCC q)'))
  const s2 = e.newNodeIn(cB, snap, p('SUCC (PLUS q_0 q)'))
  const shared = e.wireOf(s1, 'output') === e.wireOf(s2, 'output')
  const onWires = e.wireOf(s1, 'freeVar', 'q_0') === wm && e.wireOf(s1, 'freeVar', 'q') === wn
  console.log(`p1d: succShiftS citation at depth-2 positive OK; pair spliced, shared out: ${shared}, ports (q_0@wm, q@wn): ${onWires}`)
} catch (err) {
  console.log(`p1d: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}
