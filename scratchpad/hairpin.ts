// The user's reported configuration: a dangle whose tip rests across a big
// disc, drawn as a half-wrap. Under the new energy (soft routing + BEND_COST
// turning + no standoff + uniform overlap), this must be crushed.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, enableLayoutOptimization } from '../src/view/relax'
import { layoutScore } from '../src/view/optimize'
import { legPaths } from '../src/view/wires'
import { polylineTurning } from '../src/view/route/freespace'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const big = b.ref(b.root, 'R', rel1)
const e = mkEngine(b.build(), [])
seedProject(e)
// place the tip on the FAR side of the disc (the reported trap)
const node = e.bodies.get(big)!
node.pos = { x: 0, y: 0 }; node.theta = 0
const tip = [...e.bodies.values()].find((x) => x.kind === 'end')!
tip.pos = { x: -node.discR * e.scale * 2.5, y: 0 }
const maxTurn = () => Math.max(...legPaths(e).map((l) => polylineTurning(l.pts)))
console.log(`start: score=${layoutScore(e).toFixed(2)} maxTurn=${(maxTurn() / Math.PI).toFixed(2)}π`)
enableLayoutOptimization(true)
for (let t = 0; t < 6000; t++) if (!settleStep(e)) { console.log(`RESTED at ${t}`); break }
console.log(`final: score=${layoutScore(e).toFixed(2)} maxTurn=${(maxTurn() / Math.PI).toFixed(2)}π tipDist=${Math.hypot(tip.pos.x - node.pos.x, tip.pos.y - node.pos.y).toFixed(2)}`)
enableLayoutOptimization(false)
