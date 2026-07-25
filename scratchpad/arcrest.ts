// The app's observed blind-cone rest, reconstructed: does the operator really
// rest here, and does the TRUE energy descend along single coordinates?
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { mkEngine, resolveLeg } from '../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
const p = (s: string) => parseTerm(s)
const b = new DiagramBuilder()
const ids = ['n', 'n_0', 'n_1', 'n_2']
for (const _ of ids) b.termNode(b.root, p('x'))
const e = mkEngine(b.build(), [])
seedProject(e)
// the APP's frame + scale at the observed arc rest (debug seam frameScale())
e.frame = { center: { x: 6, y: 0 }, half: 11 }
e.scale = 0.30300246511790724
const S = [
  ['n0', 6.6917, 2.7822, 1.6154], ['n1', 4.6215, -8.2761, 3.1049],
  ['n2', -0.3585, -1.6661, 7.0857], ['n3', 13.0717, -2.813, 8.0556],
  ['j:w0', 6.3338, 9.2776, 0], ['j:w1', 6.9198, -3.5845, 0],
  ['j:w2', 3.2835, -8.218, 0], ['j:w3', 15.1171, -8.5659, 0],
  ['j:w4', 2.4485, 1.3304, 0], ['j:w5', -3.6381, -9.5582, 0],
  ['j:w6', 13.6657, 9.0129, 0], ['j:w7', 14.0452, -7.1796, 0],
] as const
for (const [id, x, y, th] of S) { const bd = e.bodies.get(id); if (bd === undefined) throw new Error('missing ' + id); bd.pos = { x, y }; bd.theta = th }
console.log('bodies present:', [...e.bodies.keys()].join(','))
const E0 = totalEnergy(e)
console.log(`E0=${E0.toFixed(4)}`)
// blind-cone check per leg
for (const [wid, w] of e.wires) {
  for (const leg of w.legs) {
    const sh = resolveLeg(e, w, leg)
    if (Math.abs(sh.sol.dTurn) > 3.2) console.log(`BLIND-CONE leg on ${wid}: tau=${sh.sol.dTurn.toFixed(2)} L=${sh.sol.L.toFixed(2)}`)
  }
}
// does the operator move?
let acc = 0
for (let t = 0; t < 60; t++) if (settleStep(e)) acc++; else break
console.log(`accepted ${acc}/60 frames; E=${totalEnergy(e).toFixed(4)}`)
// single-coordinate true-E probes at whatever state we're now in
const En = totalEnergy(e)
for (const id of ['n0', 'j:w0']) {
  const bd = e.bodies.get(id)!
  for (const [lbl, f, undo] of [
    ['x+', () => { bd.pos = { x: bd.pos.x + 0.05, y: bd.pos.y } }, () => { bd.pos = { x: bd.pos.x - 0.05, y: bd.pos.y } }],
    ['x-', () => { bd.pos = { x: bd.pos.x - 0.05, y: bd.pos.y } }, () => { bd.pos = { x: bd.pos.x + 0.05, y: bd.pos.y } }],
    ['th+', () => { bd.theta += 0.02 }, () => { bd.theta -= 0.02 }],
    ['th-', () => { bd.theta -= 0.02 }, () => { bd.theta += 0.02 }],
  ] as const) {
    f(); const dE = totalEnergy(e) - En; undo()
    if (dE < -1e-5) console.log(`${id} ${lbl}: dE=${dE.toFixed(5)} DESCENDS`)
  }
}
console.log('done')
