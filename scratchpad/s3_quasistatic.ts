// Scenario 3: quasi-static truth. (1) Which pairing is optimal for a WIDE rect, and
// does the natural mkEngine seed reach it? (2) Static aspect-ratio sweep wide->tall,
// each aspect settled to FULL rest — does resting ℓ_e -> 0 at the topology boundary,
// or floor? This removes all drive-injection: pure strict descent to a fixed point.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import type { Engine, WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, __decompose, recomputeRegions, establishFrame } from '../src/view/relax'
import { __PROBE2 } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
import { junctionWire, pinAt, internalEdges, minInternal, topoSig, resetProbes, MERGE_EPS } from './harness'

const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function rect4Engine(): { e: Engine; w: WireView } {
  const b = new DiagramBuilder()
  const refs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `r${i}`, rel(3)))
  b.wire(b.root, refs.map((r) => ({ node: r, port: { kind: 'arg' as const, index: 0 } })))
  const e = mkEngine(b.build(), [])
  return { e, w: junctionWire(e) }
}

// force a pairing (i,j)|(k,l): two branches, straight legs (mirrors the crossing test)
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: { x: number; y: number }[], b0: { x: number; y: number }, b1: { x: number; y: number }): void {
  const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n })
  const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const ch = (f: { x: number; y: number }, t: { x: number; y: number }) => Math.atan2(t.y - f.y, t.x - f.x)
  const mk = (a: WireLegEnd, bb: WireLegEnd, f: { x: number; y: number }, t: { x: number; y: number }): WireLeg => ({ a, b: bb, angA: ch(f, t), angB: ch(f, t), cache: mkLegCache() })
  w.branches.length = 0; w.branches.push({ ...b0 }, { ...b1 })
  w.legs.length = 0
  for (const lg of [mk(bind(i), br(0), c[i]!, b0), mk(bind(j), br(0), c[j]!, b0), mk(bind(k), br(1), c[k]!, b1), mk(bind(l), br(1), c[l]!, b1), mk(br(0), br(1), b0, b1)]) w.legs.push(lg)
}

function settleToRest(e: Engine, pinned: Set<string>, cap: number): number {
  let n = 0
  for (let t = 0; t < cap; t++) { n++; if (!settleStep(e, pinned)) break }
  return n
}

function corners(a: number, b: number): { x: number; y: number }[] {
  return [{ x: -a, y: -b }, { x: -a, y: b }, { x: a, y: -b }, { x: a, y: b }]
}

console.log('########## (1) WIDE rect: optimal pairing vs natural seed ##########')
{
  const C = corners(40, 12)
  // natural seed
  const nat = rect4Engine()
  const pinnedN = pinAt(nat.e, nat.w, C); recomputeRegions(nat.e); establishFrame(nat.e)
  const seedTopo = topoSig(nat.w)
  settleToRest(nat.e, pinnedN, 3000)
  console.log(`  natural mkEngine seed: topo@birth=${seedTopo} -> rest topo=${topoSig(nat.w)} E=${totalEnergy(nat.e).toFixed(2)} min ℓ_e=${minInternal(nat.w).toFixed(3)}`)
  // each forced pairing
  const b0 = { x: -20, y: 0 }, b1 = { x: 20, y: 0 }, v0 = { x: 0, y: -6 }, v1 = { x: 0, y: 6 }
  for (const [nm, p, s0, s1] of [['01|23', [0, 1, 2, 3], b0, b1], ['02|13', [0, 2, 1, 3], v0, v1], ['03|12', [0, 3, 1, 2], b0, b1]] as const) {
    const { e, w } = rect4Engine()
    const pinned = pinAt(e, w, C)
    setPairing(w, p[0], p[1], p[2], p[3], C, s0, s1)
    recomputeRegions(e); establishFrame(e)
    settleToRest(e, pinned, 3000)
    console.log(`  forced ${nm}: rest topo=${topoSig(w)} E=${totalEnergy(e).toFixed(2)} min ℓ_e=${minInternal(w).toFixed(3)}`)
  }
}

console.log('\n########## (2) static aspect sweep wide->tall, each settled to FULL rest ##########')
console.log('  (a from 40->12, b from 12->40; boundary near square a=b=26. natural seed + settle each)')
{
  const N = 21
  let prevTopo = ''
  for (let i = 0; i < N; i++) {
    const u = i / (N - 1)
    const a = 40 + (12 - 40) * u, b = 12 + (40 - 12) * u
    const C = corners(a, b)
    const { e, w } = rect4Engine()
    const pinned = pinAt(e, w, C); recomputeRegions(e); establishFrame(e)
    resetProbes()
    const used = settleToRest(e, pinned, 5000)
    const topo = topoSig(w)
    const flip = topo !== prevTopo && prevTopo !== '' ? '  <== TOPO FLIP' : ''
    prevTopo = topo
    console.log(`  a=${a.toFixed(1)} b=${b.toFixed(1)} aspect=${(a / b).toFixed(2)}: rest topo=${topo} min ℓ_e=${minInternal(w).toFixed(4)} E=${totalEnergy(e).toFixed(1)} ticks=${used} crossings=${__PROBE2.faceCross.length}${flip}`)
  }
}

console.log('\n########## (3) continuous quasi-static morph (carry state across aspect steps) ##########')
console.log('  ONE engine, aspect stepped in tiny increments, fully re-settled each step (true quasi-static).')
{
  const { e, w } = rect4Engine()
  let C = corners(40, 12)
  let pinned = pinAt(e, w, C); recomputeRegions(e); establishFrame(e)
  settleToRest(e, pinned, 3000)
  console.log(`  start a=40 b=12: topo=${topoSig(w)} min ℓ_e=${minInternal(w).toFixed(4)}`)
  resetProbes()
  const N = 200
  let minEver = minInternal(w), floorAtBoundary = Infinity
  for (let i = 1; i <= N; i++) {
    const u = i / N
    const a = 40 + (12 - 40) * u, b = 12 + (40 - 40 + 40 - 12) * 0 + (12 + (40 - 12) * u - 12) // b = 12 + 28u
    const bb = 12 + (40 - 12) * u
    C = corners(a, bb)
    pinned = pinAt(e, w, C)
    settleToRest(e, pinned, 400)
    const mi = minInternal(w); minEver = Math.min(minEver, mi)
    if (a / bb < 1.3 && a / bb > 0.77) floorAtBoundary = Math.min(floorAtBoundary, mi)
    if (i % 10 === 0 || mi < 1) console.log(`  step${i} a=${a.toFixed(1)} b=${bb.toFixed(1)}: topo=${topoSig(w)} min ℓ_e=${mi.toFixed(4)} cross=${__PROBE2.faceCross.length}`)
  }
  console.log(`  min ℓ_e EVER=${minEver.toFixed(5)} near-boundary floor=${floorAtBoundary.toFixed(5)} reachedFace=${minEver <= MERGE_EPS} totalCrossings=${__PROBE2.faceCross.length}`)
  for (const fc of __PROBE2.faceCross) console.log(`    CROSS ei=${fc.ei} ΔE=${(fc.bestE - fc.E0).toFixed(4)}`)
}
