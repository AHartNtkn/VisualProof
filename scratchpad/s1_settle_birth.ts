// Scenario 1: settle-from-seed + birth-seed behavior. Does the seed's near-zero
// internal edge resolve sanely? Do birth edges cross immediately / expand / oscillate?
import {
  nWay, forallVia3, junctionWire, pinAt, internalEdges, minInternal, topoSig,
  totalEnergy, __decompose, settleStep, mkEngine, recomputeRegions, establishFrame,
  resetProbes, __PROBE2, MERGE_EPS,
} from './harness'
import type { Engine } from '../src/view/engine'

function sanityDecompose(e: Engine): void {
  const d = __decompose(e)
  const sum = Object.values(d).reduce((s, x) => s + x, 0)
  const te = totalEnergy(e)
  console.log(`  [sanity] Σcomponents=${sum.toFixed(4)} totalEnergy=${te.toFixed(4)} diff=${(sum - te).toExponential(2)}`)
}

type Fix = { name: string; make: () => { e: Engine; pinned: Set<string> } }

function pinnedNWay(name: string, pos: { x: number; y: number }[]): Fix {
  return {
    name, make: () => {
      const e = mkEngine(nWay(pos.length).d, [])
      const w = junctionWire(e)
      const pinned = pinAt(e, w, pos)
      recomputeRegions(e); establishFrame(e)
      return { e, pinned }
    },
  }
}

// rect4: WIDE rectangle corners (row split optimal). bar5: 5 colinear-ish terminals.
const rect4 = pinnedNWay('rect4-wide', [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }])
const bar5 = pinnedNWay('bar5', [{ x: -40, y: 0 }, { x: -20, y: 8 }, { x: 0, y: -8 }, { x: 20, y: 8 }, { x: 40, y: 0 }])
// a symmetric square (all three pairings near-degenerate — a birth near-zero edge stressor)
const square4 = pinnedNWay('square4', [{ x: -20, y: -20 }, { x: -20, y: 20 }, { x: 20, y: -20 }, { x: 20, y: 20 }])
const forall: Fix = {
  name: 'forall-via3', make: () => {
    const e = mkEngine(forallVia3().d, [])
    recomputeRegions(e); establishFrame(e)
    return { e, pinned: new Set<string>() }
  },
}

for (const fix of [rect4, bar5, square4, forall]) {
  const { e, pinned } = fix.make()
  const w = junctionWire(e)
  resetProbes()
  const birthEdges = internalEdges(w)
  console.log(`\n=== ${fix.name} ===  binds=${w.binds.length} branches=${w.branches.length} intEdges=${birthEdges.length}`)
  console.log(`  BIRTH ℓ_e = [${birthEdges.map((x) => x.len.toFixed(4)).join(', ')}]  topo=${topoSig(w)}`)
  sanityDecompose(e)
  let prevE = totalEnergy(e)
  let worstRise = 0, minEver = minInternal(w)
  const trace: string[] = []
  let crossSweep = -1
  for (let t = 0; t < 1200; t++) {
    const fcBefore = __PROBE2.faceCross.length
    const moved = settleStep(e, pinned.size ? pinned : null)
    const curE = totalEnergy(e)
    worstRise = Math.max(worstRise, curE - prevE); prevE = curE
    const mi = minInternal(w); minEver = Math.min(minEver, mi)
    if (__PROBE2.faceCross.length > fcBefore && crossSweep < 0) crossSweep = t
    if (t < 20 || t % 100 === 0) trace.push(`t${t}:min=${mi.toFixed(4)}/E=${curE.toFixed(2)}`)
    if (!moved) { trace.push(`REST@t${t}`); break }
  }
  console.log('  ' + trace.join(' '))
  console.log(`  min ℓ_e EVER = ${minEver.toFixed(5)} (MERGE_EPS=${MERGE_EPS})  reachedFace=${minEver <= MERGE_EPS}`)
  console.log(`  crossings fired = ${__PROBE2.faceCross.length}` + (crossSweep >= 0 ? ` (first @ sweep ${crossSweep})` : ''))
  for (const fc of __PROBE2.faceCross) console.log(`    cross wid=${fc.wid} ei=${fc.ei} E0=${fc.E0.toFixed(3)} -> ${fc.bestE.toFixed(3)} ΔE=${(fc.bestE - fc.E0).toFixed(4)}`)
  console.log(`  final ℓ_e = [${internalEdges(w).map((x) => x.len.toFixed(4)).join(', ')}]  topo=${topoSig(w)}`)
  console.log(`  worst single-sweep E rise = ${worstRise.toExponential(3)} (monotone if ~0)`)
}
