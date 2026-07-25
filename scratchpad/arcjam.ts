// The app's operator-jam state with blind-cone arcs, byte-exact (unrounded dump).
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { mkEngine, resolveLeg } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions } from '../src/view/relax'
const p = (s: string) => parseTerm(s)
const b = new DiagramBuilder()
for (let i = 0; i < 4; i++) b.termNode(b.root, p('x'))
const e = mkEngine(b.build(), [])
e.frame = { center: { x: 6, y: 0 }, half: 11 }
e.scale = 0.32969774372196
const S: [string, number, number, number][] = [
  ['n0', 11.722834345333732, -3.715409597707985, 2.103782401584096],
  ['n1', 0.9841102244839439, 4.390926383936995, 5.415602507341373],
  ['n2', 2.4274836084540286, -4.677943061038405, 7.0254020377509665],
  ['n3', 10.122848521748113, 5.891612527093708, 9.5111722049181],
  ['j:w0', 8.779024652701063, 1.2095952508812884, 0],
  ['j:w1', 8.936512281685655, -4.042441564325911, 0],
  ['j:w2', 3.5754997089005864, 1.307717450345423, 0],
  ['j:w3', -1.8142344029807347, 7.681419192988106, 0],
  ['j:w4', 5.070344487889731, -2.2459732160397987, 0],
  ['j:w5', -0.7945724121692073, -7.639601427667707, 0],
  ['j:w6', 11.801612515568529, 3.237119025317792, 0],
  ['j:w7', 14.382688055107774, 6.254471955450711, 0],
]
for (const [id, x, y, th] of S) { const bd = e.bodies.get(id); if (bd === undefined) throw new Error('missing ' + id); bd.pos = { x, y }; bd.theta = th }
recomputeRegions(e)
const E0 = totalEnergy(e)
console.log(`E0=${E0.toFixed(6)}`)
for (const [wid, w] of e.wires) for (const leg of w.legs) {
  const sh = resolveLeg(e, w, leg)
  if (Math.abs(sh.sol.dTurn) > 3.2) console.log(`ARC ${wid}: tau=${sh.sol.dTurn.toFixed(2)} L=${sh.sol.L.toFixed(1)}`)
}
console.log('operator moves?', settleStep(e))
// single-coordinate TRUE-E probes over every body coordinate
const En = totalEnergy(e)
for (const [id, bd] of e.bodies) {
  for (const [lbl, ap, un] of [
    ['x', (dd: number) => { bd.pos = { x: bd.pos.x + dd, y: bd.pos.y } }, (dd: number) => { bd.pos = { x: bd.pos.x - dd, y: bd.pos.y } }],
    ['y', (dd: number) => { bd.pos = { x: bd.pos.x, y: bd.pos.y + dd } }, (dd: number) => { bd.pos = { x: bd.pos.x, y: bd.pos.y - dd } }],
    ['θ', (dd: number) => { bd.theta += dd }, (dd: number) => { bd.theta -= dd }],
  ] as const) {
    for (const dd of [0.02, -0.02, 0.1, -0.1, 0.4, -0.4]) {
      ap(dd); recomputeRegions(e); const dE = totalEnergy(e) - En; un(dd); 
      if (dE < -1e-4) { console.log(`  ${id}.${lbl} d=${dd}: dE=${dE.toFixed(5)} DESCENDS`); break }
    }
  }
}
recomputeRegions(e)
console.log('done')

// Arc anatomy + a ring sweep of the tip around its anchor
import { worldBindAnchor } from '../src/view/engine'
for (const [wid, w] of e.wires) {
  for (const leg of w.legs) {
    const sh = resolveLeg(e, w, leg)
    if (Math.abs(sh.sol.dTurn) < 3.2) continue
    const bind = w.binds[0]!
    const nb = e.bodies.get(bind.body)!
    const anchor = worldBindAnchor(e, nb, bind.key)
    const tip = e.bodies.get(w.endBodyId!)!
    const dist = Math.hypot(tip.pos.x - anchor.x, tip.pos.y - anchor.y)
    console.log(`${wid}: node=${bind.body} key=${bind.key} anchor=(${anchor.x.toFixed(2)},${anchor.y.toFixed(2)}) th0=${sh.th0.toFixed(3)} tip=(${tip.pos.x.toFixed(2)},${tip.pos.y.toFixed(2)}) tipDist=${dist.toFixed(3)} tau=${sh.sol.dTurn.toFixed(2)} L=${sh.sol.L.toFixed(2)}`)
    // ring sweep: tip at anchor + dist·(cosφ,sinφ)
    const save = { ...tip.pos }
    const EBase = totalEnergy(e)
    let line = '  ring: '
    for (let k = 0; k < 16; k++) {
      const phi = (k / 16) * 2 * Math.PI
      tip.pos = { x: anchor.x + dist * Math.cos(phi), y: anchor.y + dist * Math.sin(phi) }
      recomputeRegions(e)
      line += `${(totalEnergy(e) - EBase).toFixed(1)} `
    }
    tip.pos = save
    recomputeRegions(e)
    console.log(line)
  }
}
console.log('anatomy done')
