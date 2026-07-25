// Scenario 2: forced topology-boundary crossing. (a) rect4 90° wide->tall rotation
// (the OLD attempt's 0.15-floor case), (b) slow/medium/fast/teleport boundary drags,
// (c) squeeze. Records per-sweep min ℓ_e, crossings + ΔE, E monotonicity, and — at any
// floor — the gradient decomposition (which term holds the edge open).
import {
  nWay, junctionWire, pinAt, internalEdges, minInternal, topoSig,
  totalEnergy, __decompose, settleStep, mkEngine, recomputeRegions, establishFrame,
  resetProbes, __PROBE2, MERGE_EPS,
} from './harness'
import type { Engine } from '../src/view/engine'
import type { WireView } from '../src/view/engine'

// Drive the 4 corners each frame to `pos`, pin them, settle ONE sweep (app cadence).
function drivePinned(e: Engine, w: WireView, pos: { x: number; y: number }[]): Set<string> {
  return pinAt(e, w, pos)
}

function rot(p: { x: number; y: number }, cx: number, cy: number, a: number): { x: number; y: number } {
  const dx = p.x - cx, dy = p.y - cy
  return { x: cx + dx * Math.cos(a) - dy * Math.sin(a), y: cy + dx * Math.sin(a) + dy * Math.cos(a) }
}

// gradient decomposition of the internal edge at the current (floored) state: compress
// the shortest internal edge by δ (move both branches to their midpoint by δ/2) and read
// ΔE per term. A positive Δ means that term RESISTS the collapse (holds the edge open).
function decomposeFloor(e: Engine, w: WireView): void {
  const es = internalEdges(w)
  if (es.length === 0) { console.log('    (no internal edge)'); return }
  const edge = es.reduce((a, b) => (a.len < b.len ? a : b))
  const before = __decompose(e)
  const p = w.branches[edge.bi]!, q = w.branches[edge.bj]!
  const mx = (p.x + q.x) / 2, my = (p.y + q.y) / 2
  const L = edge.len
  const frac = L > 1e-6 ? Math.min(0.5, (MERGE_EPS * 2) / L) : 0 // compress toward face by a small step
  const savedP = { ...p }, savedQ = { ...q }
  w.branches[edge.bi] = { x: p.x + (mx - p.x) * frac, y: p.y + (my - p.y) * frac }
  w.branches[edge.bj] = { x: q.x + (mx - q.x) * frac, y: q.y + (my - q.y) * frac }
  const dL = L * frac // total shrink in ℓ_e
  const after = __decompose(e)
  w.branches[edge.bi] = savedP; w.branches[edge.bj] = savedQ
  console.log(`    floored ℓ_e=${L.toFixed(4)}; compress by Δℓ=${dL.toFixed(4)} -> per-term ΔE (dE/dℓ; >0 resists collapse):`)
  const keys = Object.keys(before) as (keyof typeof before)[]
  const rows = keys.map((k) => ({ k, d: after[k] - before[k], slope: (after[k] - before[k]) / -dL }))
    .filter((r) => Math.abs(r.d) > 1e-6).sort((a, b) => Math.abs(b.d) - Math.abs(a.d))
  for (const r of rows) console.log(`      ${r.k.padEnd(13)} ΔE=${r.d >= 0 ? '+' : ''}${r.d.toFixed(4)}  dE/dℓ=${r.slope.toFixed(3)}`)
  const totalSlope = rows.reduce((s, r) => s + (after[r.k] - before[r.k]), 0) / -dL
  console.log(`      NET dE/dℓ = ${totalSlope.toFixed(3)}  (>0 => shrinking raises E => gate rejects => floored)`)
}

const WIDE = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]
const mk = (): { e: Engine; w: WireView } => {
  const e = mkEngine(nWay(4).d, [])
  const w = junctionWire(e)
  pinAt(e, w, WIDE); recomputeRegions(e); establishFrame(e)
  // settle it into its natural basin first
  for (let i = 0; i < 400; i++) if (!settleStep(e, new Set(w.binds.map((b) => b.body)))) break
  return { e, w }
}

// The settleStep in runFrames must keep the driven corners pinned; wrap so pinAt is
// re-applied each frame and the pinned set is honoured. Re-implement runFrames driver
// with an explicit pinned set instead of the generic settleStep call above.
function runDriven(tag: string, e: Engine, w: WireView, posFn: (t: number) => { x: number; y: number }[], nFrames: number, settlePer: number): void {
  resetProbes()
  let prevE = totalEnergy(e), worstRise = 0, minEver = minInternal(w), crossFrame = -1
  const startTopo = topoSig(w)
  const samples: string[] = []
  for (let f = 0; f < nFrames; f++) {
    const pinned = pinAt(e, w, posFn(f))
    for (let s = 0; s < settlePer; s++) {
      const fcB = __PROBE2.faceCross.length
      settleStep(e, pinned)
      const cur = totalEnergy(e)
      worstRise = Math.max(worstRise, cur - prevE); prevE = cur
      if (__PROBE2.faceCross.length > fcB && crossFrame < 0) crossFrame = f
    }
    const mi = minInternal(w); minEver = Math.min(minEver, mi)
    if (f % Math.max(1, Math.floor(nFrames / 12)) === 0 || mi <= MERGE_EPS * 3) samples.push(`f${f}:min=${mi.toFixed(4)}`)
  }
  console.log(`  [${tag}] ${samples.join(' ')}`)
  console.log(`  [${tag}] min ℓ_e EVER=${minEver.toFixed(5)} reachedFace=${minEver <= MERGE_EPS} crossings=${__PROBE2.faceCross.length}${crossFrame >= 0 ? ` (first@f${crossFrame})` : ''} topo ${startTopo}->${topoSig(w)} worstRise=${worstRise.toExponential(2)}`)
  for (const fc of __PROBE2.faceCross) console.log(`      CROSS ei=${fc.ei} ΔE=${(fc.bestE - fc.E0).toFixed(4)} (E0=${fc.E0.toFixed(2)}->${fc.bestE.toFixed(2)})`)
  if (minEver > MERGE_EPS && __PROBE2.faceCross.length === 0) decomposeFloor(e, w)
}

const cx = 0, cy = 0

console.log('\n########## (A) rect4 90° wide->tall ROTATION (old attempt: floored ~0.15) ##########')
{
  const { e, w } = mk()
  console.log('  start topo=' + topoSig(w) + ' min=' + minInternal(w).toFixed(4))
  // rotate the 4 corners 0 -> 90° over 90 frames, app cadence (1 sweep/frame)
  runDriven('rot-1sweep/frame', e, w, (f) => WIDE.map((p) => rot(p, cx, cy, (Math.PI / 2) * (f / 89))), 90, 1)
}
{
  const { e, w } = mk()
  // slower rotation, more settle per frame (does more relaxation let it reach the face?)
  runDriven('rot-8sweep/frame', e, w, (f) => WIDE.map((p) => rot(p, cx, cy, (Math.PI / 2) * (f / 179))), 180, 8)
}

console.log('\n########## (B) boundary-crossing DRAGS (drag corner 0 across the diagonal) ##########')
// Drag corner 0 from top-left to top-right (past corner 2/3 region) so its optimal
// pairing partner flips. speeds = wu/frame.
for (const [name, wuPerFrame] of [['slow-0.5', 0.5], ['medium-2', 2], ['fast-8', 8]] as const) {
  const { e, w } = mk()
  const start = WIDE[0]!, target = { x: 38, y: -12 } // sweep 0 across to the right column
  const dist = Math.hypot(target.x - start.x, target.y - start.y)
  const nF = Math.ceil(dist / wuPerFrame)
  runDriven(`drag ${name}`, e, w, (f) => {
    const u = Math.min(1, f / (nF - 1))
    const p0 = { x: start.x + (target.x - start.x) * u, y: start.y + (target.y - start.y) * u }
    return [p0, WIDE[1]!, WIDE[2]!, WIDE[3]!]
  }, nF, 4)
}
{
  // teleport: jump corner 0 to target in 1 frame, then settle
  const { e, w } = mk()
  const target = { x: 38, y: -12 }
  runDriven('drag teleport', e, w, () => [target, WIDE[1]!, WIDE[2]!, WIDE[3]!], 300, 1)
}

console.log('\n########## (C) SQUEEZE (drag corners 2,3 in to compress the internal edge) ##########')
{
  const { e, w } = mk()
  runDriven('squeeze', e, w, (f) => {
    const u = Math.min(1, f / 120)
    // pull the right column toward the junction centre along -x
    const sx = 40 - u * 39
    return [WIDE[0]!, WIDE[1]!, { x: sx, y: -12 }, { x: sx, y: 12 }]
  }, 140, 4)
}
