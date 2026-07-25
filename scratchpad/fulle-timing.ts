// OBSERVATION (scratch): cost of one full totalEnergy evaluation on the two
// heaviest fixtures — bounds the step operator's backtracking loop (≤10 evals/frame).
import { mkEngine } from '../src/view/engine'
import { settle, totalEnergy } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'

const bootCtx = (await bootFixture()).ctx
for (const [thm, k] of [['plusComm', 20], ['succShiftS', 48]] as const) {
  const r = mkReplay(thm, bootCtx)
  const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
  settle(e, 200)
  totalEnergy(e) // warm caches
  const t0 = performance.now()
  const N = 50
  for (let i = 0; i < N; i++) totalEnergy(e)
  const warm = (performance.now() - t0) / N
  // cold-ish: perturb every body slightly so leg caches miss
  for (const b of e.bodies.values()) b.pos = { x: b.pos.x + 0.001, y: b.pos.y + 0.001 }
  const t1 = performance.now()
  for (let i = 0; i < 5; i++) {
    for (const b of e.bodies.values()) b.pos = { x: b.pos.x + 0.0001, y: b.pos.y }
    totalEnergy(e)
  }
  const cold = (performance.now() - t1) / 5
  console.log(`${thm}@${k}: bodies=${e.bodies.size} totalEnergy warm=${warm.toFixed(3)}ms cold=${cold.toFixed(3)}ms → 10 evals ≈ ${(10 * cold).toFixed(1)}ms`)
}
