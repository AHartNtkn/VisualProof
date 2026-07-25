// OBSERVATION PROBE (scratch, untracked): does the derived-tree model's descent
// REST (movement decays to zero) or CONVEYOR (movement persists forever)?
// Runs plusComm@20 — the worst post-settle wanderer (11.77 wu / 200 ticks).
import { mkEngine, type Engine } from '../src/view/engine'
import { settle, settleStep, totalEnergy } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'

const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e: Engine = mkEngine(r.diagramAt(20), r.boundaryAt(20))

const used = settle(e, 1100)
console.log(`settle(1100) used ${used} ticks (cap hit: ${used === 1100})`)

const snap = (): Map<string, { x: number; y: number }> =>
  new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))

const WINDOW = 100
for (let w = 0; w < 40; w++) {
  const before = snap()
  let anyMove = false
  for (let t = 0; t < WINDOW; t++) anyMove = settleStep(e) || anyMove
  let maxd = 0
  let maxId = ''
  for (const [id, b] of e.bodies) {
    const p = before.get(id)!
    const d = Math.hypot(b.pos.x - p.x, b.pos.y - p.y)
    if (d > maxd) { maxd = d; maxId = id }
  }
  console.log(`window ${String(w).padStart(2)} [ticks ${1100 + w * WINDOW}-${1100 + (w + 1) * WINDOW}]: maxMove=${maxd.toFixed(4)} (${maxId})  E=${totalEnergy(e).toFixed(3)}  moved=${anyMove}`)
  if (!anyMove) { console.log('FIXED POINT reached — rests.'); break }
}
