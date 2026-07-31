import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import type { Engine, WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
import { junctionWire, pinAt, minInternal } from './harness'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function rect4(): { e: Engine; w: WireView } {
  const b = new DiagramBuilder()
  const refs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `r${i}`, rel(3)))
  b.wire(b.root, refs.map((r) => ({ node: r, port: { kind: 'arg' as const, index: 0 } })))
  const e = mkEngine(b.build(), [])
  return { e, w: junctionWire(e) }
}
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: { x: number; y: number }[], b0: { x: number; y: number }, b1: { x: number; y: number }): void {
  const bd = (n: number): WireLegEnd => ({ kind: 'bind', i: n })
  const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const ch = (f: { x: number; y: number }, t: { x: number; y: number }) => Math.atan2(t.y - f.y, t.x - f.x)
  const mk = (a: WireLegEnd, bb: WireLegEnd, f: { x: number; y: number }, t: { x: number; y: number }): WireLeg => ({ a, b: bb, angA: ch(f, t), angB: ch(f, t), cache: mkLegCache() })
  w.branches.length = 0; w.branches.push({ ...b0 }, { ...b1 })
  w.legs.length = 0
  for (const lg of [mk(bd(i), br(0), c[i]!, b0), mk(bd(j), br(0), c[j]!, b0), mk(bd(k), br(1), c[k]!, b1), mk(bd(l), br(1), c[l]!, b1), mk(br(0), br(1), b0, b1)]) w.legs.push(lg)
}
const C = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]
const { e, w } = rect4()
const pin = pinAt(e, w, C)
setPairing(w, 0, 3, 1, 2, C, { x: -1, y: 0 }, { x: 1, y: 0 })
recomputeRegions(e); establishFrame(e)
let fixedAt = -1
for (let t = 0; t < 20000; t++) {
  const moved = settleStep(e, pin)
  if (t % 2000 === 0) console.error(`t${t}: minL=${minInternal(w).toFixed(5)} E=${totalEnergy(e).toFixed(3)} moved=${moved}`)
  if (!moved) { fixedAt = t; break }
}
console.error(`03|12 fixed point at t=${fixedAt}: minL=${minInternal(w).toFixed(5)} (MERGE_EPS=0.01) reachedFace=${minInternal(w) <= 0.01}`)
